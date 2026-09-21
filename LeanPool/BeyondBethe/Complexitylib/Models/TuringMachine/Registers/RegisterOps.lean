/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Registers.Emit

/-!
# Register operations

The hand-rolled core machines of the reduction emitter's register calculus
(`docs/A5-ReductionEmitter.md`): `skipTM` (a one-step no-op, the fold
identity), `incRegTM` (append one mark to a register), and `clearRegTM`
(blank a register). All register arithmetic (addition, multiplication,
polynomial evaluation) composes from these via the `forRegTM` loop
combinator.

Specs are in the ghost-parametrized `EmitPred` style: registers are the
canonical tapes `regTape v`, and posts are `Function.update` equations.
-/


@[expose] public section

namespace Complexity

namespace TM

variable {n : ℕ}

-- ════════════════════════════════════════════════════════════════════════
-- skipTM: the one-step no-op
-- ════════════════════════════════════════════════════════════════════════

/-- One idle step and halt: the identity for `seqTM` folds. -/
def skipTM : TM n where
  Q := BumpPhase
  qstart := .go
  qhalt := .done
  δ := fun _ iHead wHeads oHead =>
    (.done, fun i => readBackWrite (wHeads i), readBackWrite oHead,
     idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
  δ_right_of_start := fun _ _ _ _ =>
    ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start, idleDir_right_of_start⟩

/-- `skipTM` changes nothing (parked tapes). -/
theorem skipTM_hoareTime (inp₀ : Tape) (work₀ : Fin n → Tape) (ys : List Bool)
    (hinp₀ : Parked inp₀) (hwork₀ : ∀ i, Parked (work₀ i)) :
    (skipTM (n := n)).HoareTime
      (EmitPred inp₀ work₀ ys) (EmitPred inp₀ work₀ ys) 1 := by
  rintro inp work out ⟨rfl, rfl, hout⟩
  have hstep : (skipTM (n := n)).step
      { state := .go, input := inp, work := work, output := out } = some
      { state := .done, input := inp, work := work, output := out } := by
    simp only [TM.step, skipTM, reduceCtorEq, ↓reduceIte]
    refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
    · exact hinp₀.move_idle
    · funext i
      exact (hwork₀ i).writeAndMove_readBack_idle
    · exact hout.parked.writeAndMove_readBack_idle
  exact ⟨_, 1, le_refl 1, .step hstep .zero, rfl, rfl, rfl, hout⟩

/-- `skipTM` preserves an arbitrary fully parked tape frame exactly. -/
theorem skipTM_hoareTime_frame (inp₀ : Tape) (work₀ : Fin n → Tape)
    (out₀ : Tape) (hinput : Parked inp₀) (hwork : ∀ i, Parked (work₀ i))
    (houtput : Parked out₀) :
    (skipTM (n := n)).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      1 := by
  rintro inp work out ⟨hinp, hworkEq, hout⟩
  subst inp
  subst work
  subst out
  let c' : Cfg n (skipTM (n := n)).Q :=
    { state := (skipTM (n := n)).qhalt
      input := inp₀
      work := work₀
      output := out₀ }
  have hstep : (skipTM (n := n)).step
      { state := (skipTM (n := n)).qstart
        input := inp₀
        work := work₀
        output := out₀ } = some c' := by
    simp only [TM.step, skipTM, reduceCtorEq, ↓reduceIte, c']
    refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
    · exact hinput.move_idle
    · funext i
      exact (hwork i).writeAndMove_readBack_idle
    · exact houtput.writeAndMove_readBack_idle
  exact ⟨c', 1, le_rfl, .step hstep .zero, rfl, rfl, rfl, rfl⟩

-- ════════════════════════════════════════════════════════════════════════
-- incRegTM: append one mark to a register
-- ════════════════════════════════════════════════════════════════════════

/-- State set shared by `incRegTM` and `clearRegTM`: `scan` sweeps right over
    the marks, `back` rewinds to the sentinel, `park` steps onto cell 1, and
    `done` halts. -/
inductive IncPhase where
  | scan | back | park | done
  deriving DecidableEq

/-- `IncPhase` is finite (it has exactly four states). -/
instance : Fintype IncPhase where
  elems := {.scan, .back, .park, .done}
  complete := fun x => by cases x <;> simp

/-- **Increment register `q`**: scan right over the marks, write a mark on the
    first blank, rewind to cell 1. From `regTape d` to `regTape (d + 1)` in
    `2d + 4` steps; every other tape untouched. -/
def incRegTM (q : Fin n) : TM n where
  Q := IncPhase
  qstart := .scan
  qhalt := .done
  δ := fun s iHead wHeads oHead =>
    match s with
    | .scan =>
      if wHeads q = Γ.one then
        (.scan, fun i => readBackWrite (wHeads i), readBackWrite oHead,
         idleDir iHead, fun i => if i = q then Dir3.right else idleDir (wHeads i),
         idleDir oHead)
      else
        (.back, fun i => if i = q then Γw.one else readBackWrite (wHeads i),
         readBackWrite oHead, idleDir iHead,
         fun i => if i = q then (if wHeads q = Γ.start then Dir3.right else Dir3.left)
                  else idleDir (wHeads i),
         idleDir oHead)
    | .back =>
      if wHeads q = Γ.start then
        (.park, fun i => readBackWrite (wHeads i), readBackWrite oHead,
         idleDir iHead, fun i => if i = q then Dir3.right else idleDir (wHeads i),
         idleDir oHead)
      else
        (.back, fun i => readBackWrite (wHeads i), readBackWrite oHead,
         idleDir iHead, fun i => if i = q then Dir3.left else idleDir (wHeads i),
         idleDir oHead)
    | .park =>
      (.done, fun i => readBackWrite (wHeads i), readBackWrite oHead,
       idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
    | .done => allIdle s iHead wHeads oHead
  δ_right_of_start := by
    intro s iHead wHeads oHead
    match s with
    | .scan =>
      dsimp only []
      split
      · next hone =>
        refine ⟨idleDir_right_of_start, fun i hi => ?_, idleDir_right_of_start⟩
        dsimp only []
        by_cases hir : i = q
        · subst hir; rw [hone] at hi; exact absurd hi (by decide)
        · rw [if_neg hir]; exact idleDir_right_of_start hi
      · next hnone =>
        refine ⟨idleDir_right_of_start, fun i hi => ?_, idleDir_right_of_start⟩
        dsimp only []
        by_cases hir : i = q
        · subst hir; rw [if_pos rfl, if_pos hi]
        · rw [if_neg hir]; exact idleDir_right_of_start hi
    | .back =>
      dsimp only []
      split
      · refine ⟨idleDir_right_of_start, fun i hi => ?_, idleDir_right_of_start⟩
        dsimp only []
        by_cases hir : i = q
        · rw [if_pos hir]
        · rw [if_neg hir]; exact idleDir_right_of_start hi
      · next hns =>
        refine ⟨idleDir_right_of_start, fun i hi => ?_, idleDir_right_of_start⟩
        dsimp only []
        by_cases hir : i = q
        · subst hir; exact absurd hi hns
        · rw [if_neg hir]; exact idleDir_right_of_start hi
    | .park =>
      exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start,
        idleDir_right_of_start⟩
    | .done => exact rightOfStart_allIdle iHead wHeads oHead

section IncReg

variable {q : Fin n}

private theorem incRegTM_ne_halt {s : IncPhase} (h : s ≠ .done)
    {c : Cfg n (incRegTM (n := n) q).Q} (hst : c.state = s) :
    ¬ c.state = (incRegTM (n := n) q).qhalt := by
  rw [hst]
  show ¬ s = IncPhase.done
  exact h

/-- `scan` over a mark: the register head advances; nothing else changes. -/
private theorem incRegTM_step_scan_one (c : Cfg n (incRegTM (n := n) q).Q)
    (hst : c.state = .scan) (hone : (c.work q).read = Γ.one)
    (hinp : Parked c.input) (hwork : ∀ i, i ≠ q → Parked (c.work i))
    (hout : Parked c.output) :
    (incRegTM (n := n) q).step c = some
      { state := .scan, input := c.input,
        work := Function.update c.work q ((c.work q).move .right),
        output := c.output } := by
  rw [TM.step, if_neg (incRegTM_ne_halt (by decide) hst)]
  simp only [incRegTM, hst, hone, ↓reduceIte]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact hinp.move_idle
  · funext i
    by_cases hir : i = q
    · subst hir
      rw [if_pos rfl, Function.update_self,
        writeAndMove_readBack _ (by rw [hone]; decide)]
    · rw [if_neg hir, Function.update_of_ne hir]
      exact (hwork i hir).writeAndMove_readBack_idle
  · exact hout.writeAndMove_readBack_idle

/-- `scan` at the first blank: write the new mark and turn around. -/
private theorem incRegTM_step_scan_blank (c : Cfg n (incRegTM (n := n) q).Q)
    (hst : c.state = .scan) (hblank : (c.work q).read = Γ.blank)
    (hinp : Parked c.input) (hwork : ∀ i, i ≠ q → Parked (c.work i))
    (hout : Parked c.output) :
    (incRegTM (n := n) q).step c = some
      { state := .back, input := c.input,
        work := Function.update c.work q
          (((c.work q).write Γw.one).move .left),
        output := c.output } := by
  rw [TM.step, if_neg (incRegTM_ne_halt (by decide) hst)]
  simp only [incRegTM, hst, hblank, reduceCtorEq, ↓reduceIte]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact hinp.move_idle
  · funext i
    by_cases hir : i = q
    · subst hir
      simp only [↓reduceIte, Function.update_self]
    · rw [if_neg hir, if_neg hir, Function.update_of_ne hir]
      exact (hwork i hir).writeAndMove_readBack_idle
  · exact hout.writeAndMove_readBack_idle

/-- `back` off the sentinel: keep rewinding. -/
private theorem incRegTM_step_back_left (c : Cfg n (incRegTM (n := n) q).Q)
    (hst : c.state = .back) (hns : (c.work q).read ≠ Γ.start)
    (hinp : Parked c.input) (hwork : ∀ i, i ≠ q → Parked (c.work i))
    (hout : Parked c.output) :
    (incRegTM (n := n) q).step c = some
      { state := .back, input := c.input,
        work := Function.update c.work q ((c.work q).move .left),
        output := c.output } := by
  rw [TM.step, if_neg (incRegTM_ne_halt (by decide) hst)]
  simp only [incRegTM, hst, hns, ↓reduceIte]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact hinp.move_idle
  · funext i
    by_cases hir : i = q
    · subst hir
      rw [if_pos rfl, Function.update_self, writeAndMove_readBack _ hns]
    · rw [if_neg hir, Function.update_of_ne hir]
      exact (hwork i hir).writeAndMove_readBack_idle
  · exact hout.writeAndMove_readBack_idle

/-- `back` on the sentinel: step right to cell 1 and park. -/
private theorem incRegTM_step_back_start (c : Cfg n (incRegTM (n := n) q).Q)
    (hst : c.state = .back) (hs : (c.work q).read = Γ.start)
    (hcr : ∀ j, 1 ≤ j → (c.work q).cells j ≠ Γ.start)
    (hinp : Parked c.input) (hwork : ∀ i, i ≠ q → Parked (c.work i))
    (hout : Parked c.output) :
    (incRegTM (n := n) q).step c = some
      { state := .park, input := c.input,
        work := Function.update c.work q ((c.work q).move .right),
        output := c.output } := by
  have h0 : (c.work q).head = 0 := by
    by_contra hc
    exact hcr _ (by omega) hs
  rw [TM.step, if_neg (incRegTM_ne_halt (by decide) hst)]
  simp only [incRegTM, hst, hs, ↓reduceIte]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact hinp.move_idle
  · funext i
    by_cases hir : i = q
    · subst hir
      rw [if_pos rfl, Function.update_self]
      show ((c.work i).write _).move Dir3.right = (c.work i).move .right
      congr 1
      rw [Tape.write, if_pos h0]
    · rw [if_neg hir, Function.update_of_ne hir]
      exact (hwork i hir).writeAndMove_readBack_idle
  · exact hout.writeAndMove_readBack_idle

/-- `park`: one idle step into `done`. -/
private theorem incRegTM_step_park (c : Cfg n (incRegTM (n := n) q).Q)
    (hst : c.state = .park) (hinp : Parked c.input) (hwork : ∀ i, Parked (c.work i))
    (hout : Parked c.output) :
    (incRegTM (n := n) q).step c = some
      { state := .done, input := c.input, work := c.work, output := c.output } := by
  rw [TM.step, if_neg (incRegTM_ne_halt (by decide) hst)]
  simp only [incRegTM, hst]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact hinp.move_idle
  · funext i
    exact (hwork i).writeAndMove_readBack_idle
  · exact hout.writeAndMove_readBack_idle

/-- The scan loop: from `scan` with the register head at `k + 1` over
    `regCells d` cells (`k ≤ d`), reach the first blank in `d - k` steps. -/
private theorem incRegTM_scan_run (d m : ℕ) :
    ∀ (k : ℕ), d = k + m →
      ∀ (c : Cfg n (incRegTM (n := n) q).Q),
      c.state = .scan → Parked c.input → (∀ i, i ≠ q → Parked (c.work i)) →
      Parked c.output →
      (c.work q).cells = regCells d → (c.work q).head = k + 1 →
      ∃ c', (incRegTM (n := n) q).reachesIn m c c' ∧
        c'.state = .scan ∧ c'.input = c.input ∧
        (∀ i, i ≠ q → c'.work i = c.work i) ∧
        (c'.work q).cells = regCells d ∧ (c'.work q).head = d + 1 ∧
        c'.output = c.output := by
  induction m with
  | zero =>
    intro k hk c hst hinp hwork hout hcells hhead
    exact ⟨c, .zero, hst, rfl, fun _ _ => rfl, hcells, by rw [hhead, hk], rfl⟩
  | succ m ih =>
    intro k hk c hst hinp hwork hout hcells hhead
    have hone : (c.work q).read = Γ.one := by
      rw [Tape.read, hhead, hcells]
      exact regCells_one (by omega) (by omega)
    have hstep := incRegTM_step_scan_one c hst hone hinp hwork hout
    obtain ⟨c', hreach, hst', hinp', hwork', hcells', hhead', hout'⟩ :=
      ih (k + 1) (by omega)
        { state := .scan, input := c.input,
          work := Function.update c.work q ((c.work q).move .right),
          output := c.output } rfl hinp
        (fun i hi => by
          show Parked (Function.update c.work q ((c.work q).move .right) i)
          rw [Function.update_of_ne hi]
          exact hwork i hi)
        hout
        (by
          show (Function.update c.work q ((c.work q).move .right) q).cells = _
          rw [Function.update_self]
          show (c.work q).cells = _
          exact hcells)
        (by
          show (Function.update c.work q ((c.work q).move .right) q).head = _
          rw [Function.update_self]
          show (c.work q).head + 1 = _
          rw [hhead])
    refine ⟨c', .step hstep hreach, hst', hinp', ?_, hcells', hhead', hout'⟩
    intro i hi
    rw [hwork' i hi]
    show Function.update c.work q ((c.work q).move .right) i = c.work i
    rw [Function.update_of_ne hi]

/-- The rewind loop: from `back` at head `h` over `▷`-clean cells, reach
    `done` parked at cell 1 in `h + 2` steps. -/
private theorem incRegTM_back_run (h : ℕ) :
    ∀ (c : Cfg n (incRegTM (n := n) q).Q),
      c.state = .back → Parked c.input → (∀ i, i ≠ q → Parked (c.work i)) →
      Parked c.output →
      (c.work q).cells 0 = Γ.start →
      (∀ j, 1 ≤ j → (c.work q).cells j ≠ Γ.start) →
      (c.work q).head = h →
      ∃ c', (incRegTM (n := n) q).reachesIn (h + 2) c c' ∧
        c'.state = .done ∧ c'.input = c.input ∧
        (∀ i, i ≠ q → c'.work i = c.work i) ∧
        (c'.work q).cells = (c.work q).cells ∧ (c'.work q).head = 1 ∧
        c'.output = c.output := by
  induction h with
  | zero =>
    intro c hst hinp hwork hout hc0 hcr hhead
    have hs : (c.work q).read = Γ.start := by rw [Tape.read, hhead]; exact hc0
    have hstep₁ := incRegTM_step_back_start c hst hs hcr hinp hwork hout
    have hworkP : ∀ i, Parked (Function.update c.work q ((c.work q).move .right) i) := by
      intro i
      by_cases hir : i = q
      · subst hir
        rw [Function.update_self]
        exact ⟨by show (c.work i).head + 1 ≥ 1; omega, fun j hj => hcr j hj⟩
      · rw [Function.update_of_ne hir]
        exact hwork i hir
    have hstep₂ := incRegTM_step_park (q := q)
      { state := .park, input := c.input,
        work := Function.update c.work q ((c.work q).move .right),
        output := c.output } rfl hinp hworkP hout
    refine ⟨_, .step hstep₁ (.step hstep₂ .zero), rfl, rfl, ?_, ?_, ?_, rfl⟩
    · intro i hi
      show Function.update c.work q ((c.work q).move .right) i = c.work i
      rw [Function.update_of_ne hi]
    · show (Function.update c.work q ((c.work q).move .right) q).cells = _
      rw [Function.update_self]
      rfl
    · show (Function.update c.work q ((c.work q).move .right) q).head = 1
      rw [Function.update_self]
      show (c.work q).head + 1 = 1
      rw [hhead]
  | succ h ih =>
    intro c hst hinp hwork hout hc0 hcr hhead
    have hns : (c.work q).read ≠ Γ.start := by
      rw [Tape.read, hhead]; exact hcr (h + 1) (by omega)
    have hstep₁ := incRegTM_step_back_left c hst hns hinp hwork hout
    have hupd : (Function.update c.work q ((c.work q).move .left) q).cells
        = (c.work q).cells := by
      rw [Function.update_self]
      rfl
    obtain ⟨c', hreach, hst', hinp', hwork', hcells', hhead', hout'⟩ :=
      ih { state := .back, input := c.input,
           work := Function.update c.work q ((c.work q).move .left),
           output := c.output } rfl hinp
        (fun i hi => by
          show Parked (Function.update c.work q ((c.work q).move .left) i)
          rw [Function.update_of_ne hi]
          exact hwork i hi)
        hout
        (by rw [hupd]; exact hc0)
        (fun j hj => by rw [hupd]; exact hcr j hj)
        (by
          show (Function.update c.work q ((c.work q).move .left) q).head = h
          rw [Function.update_self]
          show (c.work q).head - 1 = h
          rw [hhead]
          omega)
    refine ⟨c', .step hstep₁ hreach, hst', hinp', ?_, ?_, hhead', hout'⟩
    · intro i hi
      rw [hwork' i hi]
      show Function.update c.work q ((c.work q).move .left) i = c.work i
      rw [Function.update_of_ne hi]
    · rw [hcells', hupd]

/-- **`incRegTM` Hoare specification.** From `regTape d` in register `q`, reach
    `regTape (d + 1)` in `2d + 4` steps; the input, output, and every other work
    tape are untouched. -/
theorem incRegTM_hoareTime (q : Fin n) (d : ℕ) (inp₀ : Tape) (work₀ : Fin n → Tape)
    (ys : List Bool) (hinp₀ : Parked inp₀) (hwork₀ : ∀ i, i ≠ q → Parked (work₀ i))
    (hq : work₀ q = regTape d) :
    (incRegTM (n := n) q).HoareTime
      (EmitPred inp₀ work₀ ys)
      (EmitPred inp₀ (Function.update work₀ q (regTape (d + 1))) ys)
      (2 * d + 4) := by
  rintro inp work out ⟨rfl, rfl, hout⟩
  obtain ⟨c₁, hreach₁, hst₁, hinp₁, hwork₁, hcells₁, hhead₁, hout₁⟩ :=
    incRegTM_scan_run d d 0 (by omega)
      { state := .scan, input := inp, work := work, output := out } rfl
      hinp₀ hwork₀ hout.parked
      (by show (work q).cells = regCells d; rw [hq, regT_cells])
      (by show (work q).head = 0 + 1; rw [hq, regT_head])
  have hinpP₁ : Parked c₁.input := by rw [hinp₁]; exact hinp₀
  have hworkP₁ : ∀ i, i ≠ q → Parked (c₁.work i) := fun i hi => by
    rw [hwork₁ i hi]
    exact hwork₀ i hi
  have houtP₁ : Parked c₁.output := by rw [hout₁]; exact hout.parked
  have hblank₁ : (c₁.work q).read = Γ.blank := by
    rw [Tape.read, hhead₁, hcells₁]
    exact regCells_blank (le_refl _)
  have hstep₂ := incRegTM_step_scan_blank c₁ hst₁ hblank₁ hinpP₁ hworkP₁ houtP₁
  set wq₂ : Tape := ((c₁.work q).write Γw.one).move .left with hwq₂
  have hwq₂cells : wq₂.cells = regCells (d + 1) := by
    rw [hwq₂]
    show ((c₁.work q).write Γw.one).cells = _
    rw [Tape.write, if_neg (by rw [hhead₁]; omega)]
    show Function.update (c₁.work q).cells (c₁.work q).head Γw.one.toΓ = _
    rw [hhead₁, hcells₁]
    exact regCells_update_succ d
  have hwq₂head : wq₂.head = d := by
    rw [hwq₂]
    show ((c₁.work q).write Γw.one).head - 1 = d
    rw [Tape.write_head, hhead₁]
    omega
  obtain ⟨c₃, hreach₃, hst₃, hinp₃, hwork₃, hcells₃, hhead₃, hout₃⟩ :=
    incRegTM_back_run d
      { state := .back, input := c₁.input,
        work := Function.update c₁.work q wq₂,
        output := c₁.output } rfl hinpP₁
      (fun i hi => by
        show Parked (Function.update c₁.work q wq₂ i)
        rw [Function.update_of_ne hi]
        exact hworkP₁ i hi)
      houtP₁
      (by
        show (Function.update c₁.work q wq₂ q).cells 0 = Γ.start
        rw [Function.update_self, hwq₂cells]
        rfl)
      (fun j hj => by
        show (Function.update c₁.work q wq₂ q).cells j ≠ Γ.start
        rw [Function.update_self, hwq₂cells]
        exact (reg_regT (d + 1)).cells_ne_start hj)
      (by
        show (Function.update c₁.work q wq₂ q).head = d
        rw [Function.update_self, hwq₂head])
  refine ⟨c₃, d + ((d + 2) + 1), by omega,
    reachesIn_trans _ hreach₁ (.step hstep₂ hreach₃), hst₃, ?_, ?_, ?_⟩
  · rw [hinp₃]; exact hinp₁
  · funext i
    by_cases hir : i = q
    · subst hir
      rw [Function.update_self]
      refine Tape.ext ?_ ?_
      · rw [hhead₃]
        rfl
      · rw [hcells₃]
        show (Function.update c₁.work i wq₂ i).cells = _
        rw [Function.update_self, hwq₂cells, regT_cells]
    · rw [Function.update_of_ne hir, hwork₃ i hir]
      show Function.update c₁.work q wq₂ i = work i
      rw [Function.update_of_ne hir]
      exact hwork₁ i hir
  · rw [hout₃, hout₁]
    exact hout

end IncReg

-- ════════════════════════════════════════════════════════════════════════
-- clearRegTM: blank a register
-- ════════════════════════════════════════════════════════════════════════

/-- Cells of a register holding `d` mid-clear: positions `1..k` blanked,
    `k+1..d` still marked. -/
def clearRegCells (d k : ℕ) : ℕ → Γ := fun j =>
  if j = 0 then Γ.start
  else if j ≤ k then Γ.blank
  else if j ≤ d then Γ.one
  else Γ.blank

/-- Before any blanking (`k = 0`), a mid-clear register is exactly `regCells d`. -/
theorem clearCells_zero (d : ℕ) : clearRegCells d 0 = regCells d := by
  funext j
  simp only [clearRegCells, regCells]
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rfl
  · rw [if_neg (show ¬ j = 0 from by omega), if_neg (show ¬ j ≤ 0 from by omega),
      if_neg (show ¬ j = 0 from by omega)]

/-- After blanking all `d` marks (`k = d`), a mid-clear register is `regCells 0`. -/
theorem clearCells_last (d : ℕ) : clearRegCells d d = regCells 0 := by
  funext j
  simp only [clearRegCells, regCells]
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rfl
  · rw [if_neg (show ¬ j = 0 from by omega), if_neg (show ¬ j = 0 from by omega),
      if_neg (show ¬ j ≤ 0 from by omega)]
    by_cases hd : j ≤ d
    · rw [if_pos hd]
    · rw [if_neg hd, if_neg hd]

/-- No mid-clear cell at position `j ≥ 1` is the `▷` sentinel. -/
theorem clearCells_ne_start {d k j : ℕ} (hj : 1 ≤ j) :
    clearRegCells d k j ≠ Γ.start := by
  simp only [clearRegCells]
  rw [if_neg (show ¬ j = 0 from by omega)]
  split
  · decide
  · split <;> decide

/-- Blanking cell `k + 1` of `clearRegCells d k` advances the sweep to
    `clearRegCells d (k + 1)`. -/
theorem clearCells_update_succ (d k : ℕ) :
    Function.update (clearRegCells d k) (k + 1) Γ.blank = clearRegCells d (k + 1) := by
  funext j
  rw [Function.update_apply]
  by_cases hj : j = k + 1
  · subst hj
    rw [if_pos rfl]
    show Γ.blank = clearRegCells d (k + 1) (k + 1)
    simp only [clearRegCells]
    rw [if_neg (show ¬ k + 1 = 0 from by omega), if_pos (le_refl (k + 1))]
  · rw [if_neg hj]
    simp only [clearRegCells]
    rcases Nat.eq_zero_or_pos j with rfl | hj1
    · rfl
    · rcases Nat.lt_or_ge j (k + 1) with hlt | hge
      · rw [if_neg (show ¬ j = 0 from by omega), if_neg (show ¬ j = 0 from by omega),
          if_pos (show j ≤ k from by omega), if_pos (show j ≤ k + 1 from by omega)]
      · rw [if_neg (show ¬ j = 0 from by omega), if_neg (show ¬ j = 0 from by omega),
          if_neg (show ¬ j ≤ k from by omega), if_neg (show ¬ j ≤ k + 1 from by omega)]

/-- **Clear register `q`**: sweep right blanking the marks, rewind to cell 1.
    From `regTape d` to `regTape 0` in `2d + 4` steps; every other tape untouched. -/
def clearRegTM (q : Fin n) : TM n where
  Q := IncPhase
  qstart := .scan
  qhalt := .done
  δ := fun s iHead wHeads oHead =>
    match s with
    | .scan =>
      if wHeads q = Γ.one then
        (.scan, fun i => if i = q then Γw.blank else readBackWrite (wHeads i),
         readBackWrite oHead, idleDir iHead,
         fun i => if i = q then Dir3.right else idleDir (wHeads i),
         idleDir oHead)
      else
        (.back, fun i => readBackWrite (wHeads i), readBackWrite oHead,
         idleDir iHead,
         fun i => if i = q then (if wHeads q = Γ.start then Dir3.right else Dir3.left)
                  else idleDir (wHeads i),
         idleDir oHead)
    | .back =>
      if wHeads q = Γ.start then
        (.park, fun i => readBackWrite (wHeads i), readBackWrite oHead,
         idleDir iHead, fun i => if i = q then Dir3.right else idleDir (wHeads i),
         idleDir oHead)
      else
        (.back, fun i => readBackWrite (wHeads i), readBackWrite oHead,
         idleDir iHead, fun i => if i = q then Dir3.left else idleDir (wHeads i),
         idleDir oHead)
    | .park =>
      (.done, fun i => readBackWrite (wHeads i), readBackWrite oHead,
       idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
    | .done => allIdle s iHead wHeads oHead
  δ_right_of_start := by
    intro s iHead wHeads oHead
    match s with
    | .scan =>
      dsimp only []
      split
      · next hone =>
        refine ⟨idleDir_right_of_start, fun i hi => ?_, idleDir_right_of_start⟩
        dsimp only []
        by_cases hir : i = q
        · subst hir; rw [hone] at hi; exact absurd hi (by decide)
        · rw [if_neg hir]; exact idleDir_right_of_start hi
      · next hnone =>
        refine ⟨idleDir_right_of_start, fun i hi => ?_, idleDir_right_of_start⟩
        dsimp only []
        by_cases hir : i = q
        · subst hir; rw [if_pos rfl, if_pos hi]
        · rw [if_neg hir]; exact idleDir_right_of_start hi
    | .back =>
      dsimp only []
      split
      · refine ⟨idleDir_right_of_start, fun i hi => ?_, idleDir_right_of_start⟩
        dsimp only []
        by_cases hir : i = q
        · rw [if_pos hir]
        · rw [if_neg hir]; exact idleDir_right_of_start hi
      · next hns =>
        refine ⟨idleDir_right_of_start, fun i hi => ?_, idleDir_right_of_start⟩
        dsimp only []
        by_cases hir : i = q
        · subst hir; exact absurd hi hns
        · rw [if_neg hir]; exact idleDir_right_of_start hi
    | .park =>
      exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start,
        idleDir_right_of_start⟩
    | .done => exact rightOfStart_allIdle iHead wHeads oHead

section ClearReg

variable {q : Fin n}

private theorem clearRegTM_ne_halt {s : IncPhase} (h : s ≠ .done)
    {c : Cfg n (clearRegTM (n := n) q).Q} (hst : c.state = s) :
    ¬ c.state = (clearRegTM (n := n) q).qhalt := by
  rw [hst]
  show ¬ s = IncPhase.done
  exact h

/-- `scan` over a mark: blank it and advance. -/
private theorem clearRegTM_step_scan_one (c : Cfg n (clearRegTM (n := n) q).Q)
    (hst : c.state = .scan) (hone : (c.work q).read = Γ.one)
    (hinp : Parked c.input) (hwork : ∀ i, i ≠ q → Parked (c.work i))
    (hout : Parked c.output) :
    (clearRegTM (n := n) q).step c = some
      { state := .scan, input := c.input,
        work := Function.update c.work q
          (((c.work q).write Γw.blank).move .right),
        output := c.output } := by
  rw [TM.step, if_neg (clearRegTM_ne_halt (by decide) hst)]
  simp only [clearRegTM, hst, hone, ↓reduceIte]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact hinp.move_idle
  · funext i
    by_cases hir : i = q
    · subst hir
      simp only [↓reduceIte, Function.update_self]
    · rw [if_neg hir, if_neg hir, Function.update_of_ne hir]
      exact (hwork i hir).writeAndMove_readBack_idle
  · exact hout.writeAndMove_readBack_idle

/-- `scan` at the first blank: turn around (no write). -/
private theorem clearRegTM_step_scan_blank (c : Cfg n (clearRegTM (n := n) q).Q)
    (hst : c.state = .scan) (hblank : (c.work q).read = Γ.blank)
    (hinp : Parked c.input) (hwork : ∀ i, i ≠ q → Parked (c.work i))
    (hout : Parked c.output) :
    (clearRegTM (n := n) q).step c = some
      { state := .back, input := c.input,
        work := Function.update c.work q ((c.work q).move .left),
        output := c.output } := by
  rw [TM.step, if_neg (clearRegTM_ne_halt (by decide) hst)]
  simp only [clearRegTM, hst, hblank, reduceCtorEq, ↓reduceIte]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact hinp.move_idle
  · funext i
    by_cases hir : i = q
    · subst hir
      simp only [↓reduceIte, Function.update_self]
      rw [writeAndMove_readBack _ (by rw [hblank]; decide)]
    · rw [if_neg hir, Function.update_of_ne hir]
      exact (hwork i hir).writeAndMove_readBack_idle
  · exact hout.writeAndMove_readBack_idle

/-- `back` off the sentinel: keep rewinding. -/
private theorem clearRegTM_step_back_left (c : Cfg n (clearRegTM (n := n) q).Q)
    (hst : c.state = .back) (hns : (c.work q).read ≠ Γ.start)
    (hinp : Parked c.input) (hwork : ∀ i, i ≠ q → Parked (c.work i))
    (hout : Parked c.output) :
    (clearRegTM (n := n) q).step c = some
      { state := .back, input := c.input,
        work := Function.update c.work q ((c.work q).move .left),
        output := c.output } := by
  rw [TM.step, if_neg (clearRegTM_ne_halt (by decide) hst)]
  simp only [clearRegTM, hst, hns, ↓reduceIte]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact hinp.move_idle
  · funext i
    by_cases hir : i = q
    · subst hir
      rw [if_pos rfl, Function.update_self, writeAndMove_readBack _ hns]
    · rw [if_neg hir, Function.update_of_ne hir]
      exact (hwork i hir).writeAndMove_readBack_idle
  · exact hout.writeAndMove_readBack_idle

/-- `back` on the sentinel: step right to cell 1 and park. -/
private theorem clearRegTM_step_back_start (c : Cfg n (clearRegTM (n := n) q).Q)
    (hst : c.state = .back) (hs : (c.work q).read = Γ.start)
    (hcr : ∀ j, 1 ≤ j → (c.work q).cells j ≠ Γ.start)
    (hinp : Parked c.input) (hwork : ∀ i, i ≠ q → Parked (c.work i))
    (hout : Parked c.output) :
    (clearRegTM (n := n) q).step c = some
      { state := .park, input := c.input,
        work := Function.update c.work q ((c.work q).move .right),
        output := c.output } := by
  have h0 : (c.work q).head = 0 := by
    by_contra hc
    exact hcr _ (by omega) hs
  rw [TM.step, if_neg (clearRegTM_ne_halt (by decide) hst)]
  simp only [clearRegTM, hst, hs, ↓reduceIte]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact hinp.move_idle
  · funext i
    by_cases hir : i = q
    · subst hir
      rw [if_pos rfl, Function.update_self]
      show ((c.work i).write _).move Dir3.right = (c.work i).move .right
      congr 1
      rw [Tape.write, if_pos h0]
    · rw [if_neg hir, Function.update_of_ne hir]
      exact (hwork i hir).writeAndMove_readBack_idle
  · exact hout.writeAndMove_readBack_idle

/-- `park`: one idle step into `done`. -/
private theorem clearRegTM_step_park (c : Cfg n (clearRegTM (n := n) q).Q)
    (hst : c.state = .park) (hinp : Parked c.input) (hwork : ∀ i, Parked (c.work i))
    (hout : Parked c.output) :
    (clearRegTM (n := n) q).step c = some
      { state := .done, input := c.input, work := c.work, output := c.output } := by
  rw [TM.step, if_neg (clearRegTM_ne_halt (by decide) hst)]
  simp only [clearRegTM, hst]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact hinp.move_idle
  · funext i
    exact (hwork i).writeAndMove_readBack_idle
  · exact hout.writeAndMove_readBack_idle

/-- The clearing sweep: from `scan` at head `k + 1` over `clearRegCells d k`,
    blank the remaining `d - k` marks. -/
private theorem clearRegTM_scan_run (d m : ℕ) :
    ∀ (k : ℕ), d = k + m →
      ∀ (c : Cfg n (clearRegTM (n := n) q).Q),
      c.state = .scan → Parked c.input → (∀ i, i ≠ q → Parked (c.work i)) →
      Parked c.output →
      (c.work q).cells = clearRegCells d k → (c.work q).head = k + 1 →
      ∃ c', (clearRegTM (n := n) q).reachesIn m c c' ∧
        c'.state = .scan ∧ c'.input = c.input ∧
        (∀ i, i ≠ q → c'.work i = c.work i) ∧
        (c'.work q).cells = clearRegCells d d ∧ (c'.work q).head = d + 1 ∧
        c'.output = c.output := by
  induction m with
  | zero =>
    intro k hk c hst hinp hwork hout hcells hhead
    obtain rfl : k = d := by omega
    exact ⟨c, .zero, hst, rfl, fun _ _ => rfl, hcells, hhead, rfl⟩
  | succ m ih =>
    intro k hk c hst hinp hwork hout hcells hhead
    have hone : (c.work q).read = Γ.one := by
      rw [Tape.read, hhead, hcells, clearRegCells, if_neg (by omega), if_neg (by omega),
        if_pos (by omega)]
    have hstep := clearRegTM_step_scan_one c hst hone hinp hwork hout
    set wq₁ : Tape := ((c.work q).write Γw.blank).move .right with hwq₁
    have hwq₁cells : wq₁.cells = clearRegCells d (k + 1) := by
      rw [hwq₁]
      show ((c.work q).write Γw.blank).cells = _
      rw [Tape.write, if_neg (by rw [hhead]; omega)]
      show Function.update (c.work q).cells (c.work q).head Γw.blank.toΓ = _
      rw [hhead, hcells]
      exact clearCells_update_succ d k
    have hwq₁head : wq₁.head = (k + 1) + 1 := by
      rw [hwq₁]
      show ((c.work q).write Γw.blank).head + 1 = _
      rw [Tape.write_head, hhead]
    obtain ⟨c', hreach, hst', hinp', hwork', hcells', hhead', hout'⟩ :=
      ih (k + 1) (by omega)
        { state := .scan, input := c.input,
          work := Function.update c.work q wq₁,
          output := c.output } rfl hinp
        (fun i hi => by
          show Parked (Function.update c.work q wq₁ i)
          rw [Function.update_of_ne hi]
          exact hwork i hi)
        hout
        (by
          show (Function.update c.work q wq₁ q).cells = _
          rw [Function.update_self, hwq₁cells])
        (by
          show (Function.update c.work q wq₁ q).head = _
          rw [Function.update_self, hwq₁head])
    refine ⟨c', .step hstep hreach, hst', hinp', ?_, hcells', hhead', hout'⟩
    intro i hi
    rw [hwork' i hi]
    show Function.update c.work q wq₁ i = c.work i
    rw [Function.update_of_ne hi]

/-- The rewind loop (identical shape to `incRegTM`'s). -/
private theorem clearRegTM_back_run (h : ℕ) :
    ∀ (c : Cfg n (clearRegTM (n := n) q).Q),
      c.state = .back → Parked c.input → (∀ i, i ≠ q → Parked (c.work i)) →
      Parked c.output →
      (c.work q).cells 0 = Γ.start →
      (∀ j, 1 ≤ j → (c.work q).cells j ≠ Γ.start) →
      (c.work q).head = h →
      ∃ c', (clearRegTM (n := n) q).reachesIn (h + 2) c c' ∧
        c'.state = .done ∧ c'.input = c.input ∧
        (∀ i, i ≠ q → c'.work i = c.work i) ∧
        (c'.work q).cells = (c.work q).cells ∧ (c'.work q).head = 1 ∧
        c'.output = c.output := by
  induction h with
  | zero =>
    intro c hst hinp hwork hout hc0 hcr hhead
    have hs : (c.work q).read = Γ.start := by rw [Tape.read, hhead]; exact hc0
    have hstep₁ := clearRegTM_step_back_start c hst hs hcr hinp hwork hout
    have hworkP : ∀ i, Parked (Function.update c.work q ((c.work q).move .right) i) := by
      intro i
      by_cases hir : i = q
      · subst hir
        rw [Function.update_self]
        exact ⟨by show (c.work i).head + 1 ≥ 1; omega, fun j hj => hcr j hj⟩
      · rw [Function.update_of_ne hir]
        exact hwork i hir
    have hstep₂ := clearRegTM_step_park (q := q)
      { state := .park, input := c.input,
        work := Function.update c.work q ((c.work q).move .right),
        output := c.output } rfl hinp hworkP hout
    refine ⟨_, .step hstep₁ (.step hstep₂ .zero), rfl, rfl, ?_, ?_, ?_, rfl⟩
    · intro i hi
      show Function.update c.work q ((c.work q).move .right) i = c.work i
      rw [Function.update_of_ne hi]
    · show (Function.update c.work q ((c.work q).move .right) q).cells = _
      rw [Function.update_self]
      rfl
    · show (Function.update c.work q ((c.work q).move .right) q).head = 1
      rw [Function.update_self]
      show (c.work q).head + 1 = 1
      rw [hhead]
  | succ h ih =>
    intro c hst hinp hwork hout hc0 hcr hhead
    have hns : (c.work q).read ≠ Γ.start := by
      rw [Tape.read, hhead]; exact hcr (h + 1) (by omega)
    have hstep₁ := clearRegTM_step_back_left c hst hns hinp hwork hout
    have hupd : (Function.update c.work q ((c.work q).move .left) q).cells
        = (c.work q).cells := by
      rw [Function.update_self]
      rfl
    obtain ⟨c', hreach, hst', hinp', hwork', hcells', hhead', hout'⟩ :=
      ih { state := .back, input := c.input,
           work := Function.update c.work q ((c.work q).move .left),
           output := c.output } rfl hinp
        (fun i hi => by
          show Parked (Function.update c.work q ((c.work q).move .left) i)
          rw [Function.update_of_ne hi]
          exact hwork i hi)
        hout
        (by rw [hupd]; exact hc0)
        (fun j hj => by rw [hupd]; exact hcr j hj)
        (by
          show (Function.update c.work q ((c.work q).move .left) q).head = h
          rw [Function.update_self]
          show (c.work q).head - 1 = h
          rw [hhead]
          omega)
    refine ⟨c', .step hstep₁ hreach, hst', hinp', ?_, ?_, hhead', hout'⟩
    · intro i hi
      rw [hwork' i hi]
      show Function.update c.work q ((c.work q).move .left) i = c.work i
      rw [Function.update_of_ne hi]
    · rw [hcells', hupd]

/-- **`clearRegTM` Hoare specification.** From `regTape d` in register `q`, reach
    `regTape 0` in `2d + 4` steps; everything else untouched. -/
theorem clearRegTM_hoareTime (q : Fin n) (d : ℕ) (inp₀ : Tape) (work₀ : Fin n → Tape)
    (ys : List Bool) (hinp₀ : Parked inp₀) (hwork₀ : ∀ i, i ≠ q → Parked (work₀ i))
    (hq : work₀ q = regTape d) :
    (clearRegTM (n := n) q).HoareTime
      (EmitPred inp₀ work₀ ys)
      (EmitPred inp₀ (Function.update work₀ q (regTape 0)) ys)
      (2 * d + 4) := by
  rintro inp work out ⟨rfl, rfl, hout⟩
  obtain ⟨c₁, hreach₁, hst₁, hinp₁, hwork₁, hcells₁, hhead₁, hout₁⟩ :=
    clearRegTM_scan_run d d 0 (by omega)
      { state := .scan, input := inp, work := work, output := out } rfl
      hinp₀ hwork₀ hout.parked
      (by show (work q).cells = clearRegCells d 0; rw [hq, regT_cells, clearCells_zero])
      (by show (work q).head = 0 + 1; rw [hq, regT_head])
  have hinpP₁ : Parked c₁.input := by rw [hinp₁]; exact hinp₀
  have hworkP₁ : ∀ i, i ≠ q → Parked (c₁.work i) := fun i hi => by
    rw [hwork₁ i hi]
    exact hwork₀ i hi
  have houtP₁ : Parked c₁.output := by rw [hout₁]; exact hout.parked
  have hblank₁ : (c₁.work q).read = Γ.blank := by
    rw [Tape.read, hhead₁, hcells₁, clearCells_last]
    exact regCells_blank (by omega)
  have hstep₂ := clearRegTM_step_scan_blank c₁ hst₁ hblank₁ hinpP₁ hworkP₁ houtP₁
  have hupd₂ : (Function.update c₁.work q ((c₁.work q).move .left) q).cells
      = regCells 0 := by
    rw [Function.update_self]
    show (c₁.work q).cells = _
    rw [hcells₁, clearCells_last]
  obtain ⟨c₃, hreach₃, hst₃, hinp₃, hwork₃, hcells₃, hhead₃, hout₃⟩ :=
    clearRegTM_back_run d
      { state := .back, input := c₁.input,
        work := Function.update c₁.work q ((c₁.work q).move .left),
        output := c₁.output } rfl hinpP₁
      (fun i hi => by
        show Parked (Function.update c₁.work q ((c₁.work q).move .left) i)
        rw [Function.update_of_ne hi]
        exact hworkP₁ i hi)
      houtP₁
      (by rw [hupd₂]; rfl)
      (fun j hj => by rw [hupd₂]; exact (reg_regT 0).cells_ne_start hj)
      (by
        show (Function.update c₁.work q ((c₁.work q).move .left) q).head = d
        rw [Function.update_self]
        show (c₁.work q).head - 1 = d
        rw [hhead₁]
        omega)
  refine ⟨c₃, d + ((d + 2) + 1), by omega,
    reachesIn_trans _ hreach₁ (.step hstep₂ hreach₃), hst₃, ?_, ?_, ?_⟩
  · rw [hinp₃]; exact hinp₁
  · funext i
    by_cases hir : i = q
    · subst hir
      rw [Function.update_self]
      refine Tape.ext ?_ ?_
      · rw [hhead₃]
        rfl
      · rw [hcells₃]
        show (Function.update c₁.work i ((c₁.work i).move .left) i).cells = _
        rw [hupd₂, regT_cells]
    · rw [Function.update_of_ne hir, hwork₃ i hir]
      show Function.update c₁.work q ((c₁.work q).move .left) i = work i
      rw [Function.update_of_ne hir]
      exact hwork₁ i hir
  · rw [hout₃, hout₁]
    exact hout

end ClearReg

end TM

end Complexity
