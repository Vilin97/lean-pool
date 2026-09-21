/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Registers.RegisterOps

/-!
# Input length into a register

`inputLenRegTM q` scans the input tape in lockstep with register `q`, writing
one mark per input bit, then rewinds both heads to cell 1: from the bumped
initial configuration it puts `regTape |x|` in register `q`, restoring the input
tape exactly. This is the reduction emitter's only input-reading machine
besides the start-clause emitter, and the last hand-rolled machine of the
campaign (`docs/A5-ReductionEmitter.md`).
-/


public section

namespace Complexity

namespace TM

variable {n : ℕ}

/-- **Measure the input length into register `q`**: lockstep scan right over
    the input bits writing marks, then lockstep rewind. -/
def inputLenRegTM (q : Fin n) : TM n where
  Q := IncPhase
  qstart := .scan
  qhalt := .done
  δ := fun s iHead wHeads oHead =>
    match s with
    | .scan =>
      if iHead = Γ.blank then
        (.back, fun i => readBackWrite (wHeads i), readBackWrite oHead,
         Dir3.left,
         fun i => if i = q then (if wHeads q = Γ.start then Dir3.right else Dir3.left)
                  else idleDir (wHeads i),
         idleDir oHead)
      else if iHead = Γ.start then
        (.scan, fun i => readBackWrite (wHeads i), readBackWrite oHead,
         Dir3.right, fun i => idleDir (wHeads i), idleDir oHead)
      else
        (.scan, fun i => if i = q then Γw.one else readBackWrite (wHeads i),
         readBackWrite oHead, Dir3.right,
         fun i => if i = q then Dir3.right else idleDir (wHeads i),
         idleDir oHead)
    | .back =>
      if wHeads q = Γ.start then
        (.park, fun i => readBackWrite (wHeads i), readBackWrite oHead,
         Dir3.right, fun i => if i = q then Dir3.right else idleDir (wHeads i),
         idleDir oHead)
      else
        (.back, fun i => readBackWrite (wHeads i), readBackWrite oHead,
         (if iHead = Γ.start then Dir3.right else Dir3.left),
         fun i => if i = q then Dir3.left else idleDir (wHeads i),
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
      · next hbl =>
        refine ⟨fun hi => absurd hi (by rw [hbl]; decide), fun i hi => ?_,
          idleDir_right_of_start⟩
        dsimp only []
        by_cases hir : i = q
        · subst hir; rw [ite_eq_left rfl, ite_eq_left hi]
        · rw [ite_eq_right hir]; exact idleDir_right_of_start hi
      · split
        · exact ⟨fun _ => rfl, fun i hi => idleDir_right_of_start hi,
            idleDir_right_of_start⟩
        · refine ⟨fun _ => rfl, fun i hi => ?_, idleDir_right_of_start⟩
          dsimp only []
          by_cases hir : i = q
          · rw [ite_eq_left hir]
          · rw [ite_eq_right hir]; exact idleDir_right_of_start hi
    | .back =>
      dsimp only []
      split
      · refine ⟨fun _ => rfl, fun i hi => ?_, idleDir_right_of_start⟩
        dsimp only []
        by_cases hir : i = q
        · rw [ite_eq_left hir]
        · rw [ite_eq_right hir]; exact idleDir_right_of_start hi
      · next hns =>
        refine ⟨fun hi => by rw [ite_eq_left hi], fun i hi => ?_, idleDir_right_of_start⟩
        dsimp only []
        by_cases hir : i = q
        · subst hir; exact absurd hi hns
        · rw [ite_eq_right hir]; exact idleDir_right_of_start hi
    | .park =>
      exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start,
        idleDir_right_of_start⟩
    | .done => exact rightOfStart_allIdle iHead wHeads oHead

section InputLen

variable {q : Fin n}

private theorem inputLenRegTM_ne_halt {s : IncPhase} (h : s ≠ .done)
    {c : Cfg n (inputLenRegTM (n := n) q).Q} (hst : c.state = s) :
    ¬ c.state = (inputLenRegTM (n := n) q).qhalt := by
  rw [hst]
  show ¬ s = IncPhase.done
  exact h

/-- `scan` over a bit: mark the register, advance both heads. -/
private theorem inputLenRegTM_step_scan_bit (c : Cfg n (inputLenRegTM (n := n) q).Q)
    (hst : c.state = .scan) (hbl : c.input.read ≠ Γ.blank)
    (hns : c.input.read ≠ Γ.start)
    (hwork : ∀ i, i ≠ q → Parked (c.work i)) (hout : Parked c.output) :
    (inputLenRegTM (n := n) q).step c = some
      { state := .scan, input := c.input.move .right,
        work := Function.update c.work q
          (((c.work q).write Γw.one).move .right),
        output := c.output } := by
  rw [TM.step, ite_eq_right (inputLenRegTM_ne_halt (by decide) hst)]
  simp only [inputLenRegTM, hst, hbl, hns, ↓reduceIte]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, rfl, ?_, ?_⟩)
  · funext i
    by_cases hir : i = q
    · subst hir
      simp only [↓reduceIte, Function.update_self]
    · rw [ite_eq_right hir, ite_eq_right hir, Function.update_of_ne hir]
      exact (hwork i hir).writeAndMove_readBack_idle
  · exact hout.writeAndMove_readBack_idle

/-- `scan` at the input's first blank: turn both heads around. -/
private theorem inputLenRegTM_step_scan_blank (c : Cfg n (inputLenRegTM (n := n) q).Q)
    (hst : c.state = .scan) (hbl : c.input.read = Γ.blank)
    (hqns : (c.work q).read ≠ Γ.start)
    (hwork : ∀ i, i ≠ q → Parked (c.work i)) (hout : Parked c.output) :
    (inputLenRegTM (n := n) q).step c = some
      { state := .back, input := c.input.move .left,
        work := Function.update c.work q ((c.work q).move .left),
        output := c.output } := by
  rw [TM.step, ite_eq_right (inputLenRegTM_ne_halt (by decide) hst)]
  simp only [inputLenRegTM, hst, hbl, ↓reduceIte]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, rfl, ?_, ?_⟩)
  · funext i
    by_cases hir : i = q
    · subst hir
      rw [ite_eq_left rfl, ite_eq_right hqns, Function.update_self,
        writeAndMove_readBack _ hqns]
    · rw [ite_eq_right hir, Function.update_of_ne hir]
      exact (hwork i hir).writeAndMove_readBack_idle
  · exact hout.writeAndMove_readBack_idle

/-- `back` off the sentinel: both heads keep rewinding. -/
private theorem inputLenRegTM_step_back_left (c : Cfg n (inputLenRegTM (n := n) q).Q)
    (hst : c.state = .back) (hqns : (c.work q).read ≠ Γ.start)
    (hins : c.input.read ≠ Γ.start)
    (hwork : ∀ i, i ≠ q → Parked (c.work i)) (hout : Parked c.output) :
    (inputLenRegTM (n := n) q).step c = some
      { state := .back, input := c.input.move .left,
        work := Function.update c.work q ((c.work q).move .left),
        output := c.output } := by
  rw [TM.step, ite_eq_right (inputLenRegTM_ne_halt (by decide) hst)]
  simp only [inputLenRegTM, hst, hqns, hins, ↓reduceIte]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, rfl, ?_, ?_⟩)
  · funext i
    by_cases hir : i = q
    · subst hir
      rw [ite_eq_left rfl, Function.update_self, writeAndMove_readBack _ hqns]
    · rw [ite_eq_right hir, Function.update_of_ne hir]
      exact (hwork i hir).writeAndMove_readBack_idle
  · exact hout.writeAndMove_readBack_idle

/-- `back` on the sentinel: both heads step right to cell 1 and park. -/
private theorem inputLenRegTM_step_back_start (c : Cfg n (inputLenRegTM (n := n) q).Q)
    (hst : c.state = .back) (hs : (c.work q).read = Γ.start)
    (hcr : ∀ j, 1 ≤ j → (c.work q).cells j ≠ Γ.start)
    (hwork : ∀ i, i ≠ q → Parked (c.work i)) (hout : Parked c.output) :
    (inputLenRegTM (n := n) q).step c = some
      { state := .park, input := c.input.move .right,
        work := Function.update c.work q ((c.work q).move .right),
        output := c.output } := by
  have h0 : (c.work q).head = 0 := by
    by_contra hc
    exact hcr _ (by omega) hs
  rw [TM.step, ite_eq_right (inputLenRegTM_ne_halt (by decide) hst)]
  simp only [inputLenRegTM, hst, hs, ↓reduceIte]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, rfl, ?_, ?_⟩)
  · funext i
    by_cases hir : i = q
    · subst hir
      rw [ite_eq_left rfl, Function.update_self]
      show ((c.work i).write _).move Dir3.right = (c.work i).move .right
      congr 1
      rw [Tape.write, ite_eq_left h0]
    · rw [ite_eq_right hir, Function.update_of_ne hir]
      exact (hwork i hir).writeAndMove_readBack_idle
  · exact hout.writeAndMove_readBack_idle

/-- `park`: one idle step into `done` (parked tapes everywhere). -/
private theorem inputLenRegTM_step_park (c : Cfg n (inputLenRegTM (n := n) q).Q)
    (hst : c.state = .park) (hinp : Parked c.input)
    (hwork : ∀ i, Parked (c.work i)) (hout : Parked c.output) :
    (inputLenRegTM (n := n) q).step c = some
      { state := .done, input := c.input, work := c.work, output := c.output } := by
  rw [TM.step, ite_eq_right (inputLenRegTM_ne_halt (by decide) hst)]
  simp only [inputLenRegTM, hst]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact hinp.move_idle
  · funext i
    exact (hwork i).writeAndMove_readBack_idle
  · exact hout.writeAndMove_readBack_idle

/-- The lockstep scan: one mark per input bit. -/
private theorem inputLenRegTM_scan_run (x : List Bool) (m : ℕ) :
    ∀ (k : ℕ), x.length = k + m →
      ∀ (c : Cfg n (inputLenRegTM (n := n) q).Q),
      c.state = .scan →
      c.input.cells = (Tape.init (x.map Γ.ofBool)).cells → c.input.head = k + 1 →
      (∀ i, i ≠ q → Parked (c.work i)) → Parked c.output →
      (c.work q).cells = regCells k → (c.work q).head = k + 1 →
      ∃ c', (inputLenRegTM (n := n) q).reachesIn m c c' ∧
        c'.state = .scan ∧
        c'.input.cells = (Tape.init (x.map Γ.ofBool)).cells ∧
        c'.input.head = x.length + 1 ∧
        (∀ i, i ≠ q → c'.work i = c.work i) ∧
        (c'.work q).cells = regCells x.length ∧
        (c'.work q).head = x.length + 1 ∧
        c'.output = c.output := by
  induction m with
  | zero =>
    intro k hk c hst hic hih hwork hout hqc hqh
    obtain rfl : x.length = k := by omega
    exact ⟨c, .zero, hst, hic, hih, fun _ _ => rfl, hqc, hqh, rfl⟩
  | succ m ih =>
    intro k hk c hst hic hih hwork hout hqc hqh
    have hread : c.input.read = Γ.ofBool (x[k]'(by omega)) := by
      rw [Tape.read, hih, hic]
      exact Tape.init_ofBool_cells_lt x k (by omega)
    have hbl : c.input.read ≠ Γ.blank := by
      rw [hread]
      exact Γ.ofBool_ne_blank _
    have hns : c.input.read ≠ Γ.start := by
      rw [hread]
      exact Γ.ofBool_ne_start _
    have hstep := inputLenRegTM_step_scan_bit c hst hbl hns hwork hout
    have hq₁cells : (((c.work q).write Γw.one).move .right).cells
        = regCells (k + 1) := by
      show ((c.work q).write Γw.one).cells = _
      rw [Tape.write, ite_eq_right (by rw [hqh]; omega)]
      show Function.update (c.work q).cells (c.work q).head Γw.one.toΓ = _
      rw [hqh, hqc]
      exact regCells_update_succ k
    have hq₁head : (((c.work q).write Γw.one).move .right).head = (k + 1) + 1 := by
      show ((c.work q).write Γw.one).head + 1 = _
      rw [Tape.write_head, hqh]
    obtain ⟨c', hreach, h1, h2, h3, h4, h5, h6, h7⟩ :=
      ih (k + 1) (by omega)
        { state := .scan, input := c.input.move .right,
          work := Function.update c.work q (((c.work q).write Γw.one).move .right),
          output := c.output } rfl
        (by show (c.input.move .right).cells = _
            rw [Tape.move_cells]
            exact hic)
        (by show c.input.head + 1 = (k + 1) + 1
            rw [hih])
        (fun i hi => by
          show Parked (Function.update c.work q _ i)
          rw [Function.update_of_ne hi]
          exact hwork i hi)
        hout
        (by show (Function.update c.work q _ q).cells = _
            rw [Function.update_self]
            exact hq₁cells)
        (by show (Function.update c.work q _ q).head = _
            rw [Function.update_self]
            exact hq₁head)
    refine ⟨c', .step hstep hreach, h1, h2, h3, ?_, h5, h6, h7⟩
    intro i hi
    rw [h4 i hi]
    show Function.update c.work q _ i = c.work i
    rw [Function.update_of_ne hi]

/-- The lockstep rewind: both heads return to cell 1. -/
private theorem inputLenRegTM_back_run (x : List Bool) (h : ℕ) :
    ∀ (c : Cfg n (inputLenRegTM (n := n) q).Q),
      c.state = .back →
      c.input.cells = (Tape.init (x.map Γ.ofBool)).cells → c.input.head = h →
      (∀ i, i ≠ q → Parked (c.work i)) → Parked c.output →
      (c.work q).cells 0 = Γ.start →
      (∀ j, 1 ≤ j → (c.work q).cells j ≠ Γ.start) →
      (c.work q).head = h →
      ∃ c', (inputLenRegTM (n := n) q).reachesIn (h + 2) c c' ∧
        c'.state = .done ∧
        c'.input.cells = (Tape.init (x.map Γ.ofBool)).cells ∧ c'.input.head = 1 ∧
        (∀ i, i ≠ q → c'.work i = c.work i) ∧
        (c'.work q).cells = (c.work q).cells ∧ (c'.work q).head = 1 ∧
        c'.output = c.output := by
  induction h with
  | zero =>
    intro c hst hic hih hwork hout hc0 hcr hqh
    have hs : (c.work q).read = Γ.start := by rw [Tape.read, hqh]; exact hc0
    have hstep₁ := inputLenRegTM_step_back_start c hst hs hcr hwork hout
    have hparkP : Parked (c.input.move .right) := by
      refine ⟨?_, fun j hj => ?_⟩
      · show c.input.head + 1 ≥ 1
        omega
      · show (c.input.move .right).cells j ≠ Γ.start
        rw [Tape.move_cells, hic]
        exact Tape.init_ofBool_cells_ne_start x j hj
    have hstep₂ := inputLenRegTM_step_park (q := q)
      { state := .park, input := c.input.move .right,
        work := Function.update c.work q ((c.work q).move .right),
        output := c.output } rfl hparkP
      (fun i => by
        by_cases hir : i = q
        · subst hir
          show Parked (Function.update c.work i ((c.work i).move .right) i)
          rw [Function.update_self]
          exact ⟨by show (c.work i).head + 1 ≥ 1; omega, fun j hj => hcr j hj⟩
        · show Parked (Function.update c.work q ((c.work q).move .right) i)
          rw [Function.update_of_ne hir]
          exact hwork i hir)
      hout
    refine ⟨_, .step hstep₁ (.step hstep₂ .zero), rfl, ?_, ?_, ?_, ?_, ?_, rfl⟩
    · show (c.input.move .right).cells = _
      rw [Tape.move_cells]
      exact hic
    · show c.input.head + 1 = 1
      rw [hih]
    · intro i hi
      show Function.update c.work q ((c.work q).move .right) i = c.work i
      rw [Function.update_of_ne hi]
    · show (Function.update c.work q ((c.work q).move .right) q).cells = _
      rw [Function.update_self]
      rfl
    · show (Function.update c.work q ((c.work q).move .right) q).head = 1
      rw [Function.update_self]
      show (c.work q).head + 1 = 1
      rw [hqh]
  | succ h ih =>
    intro c hst hic hih hwork hout hc0 hcr hqh
    have hqns : (c.work q).read ≠ Γ.start := by
      rw [Tape.read, hqh]
      exact hcr (h + 1) (by omega)
    have hins : c.input.read ≠ Γ.start := by
      rw [Tape.read, hih, hic]
      exact Tape.init_ofBool_cells_ne_start x _ (by omega)
    have hstep₁ := inputLenRegTM_step_back_left c hst hqns hins hwork hout
    obtain ⟨c', hreach, h1, h2, h3, h4, h5, h6, h7⟩ :=
      ih { state := .back, input := c.input.move .left,
           work := Function.update c.work q ((c.work q).move .left),
           output := c.output } rfl
        (by show (c.input.move .left).cells = _
            rw [Tape.move_cells]
            exact hic)
        (by show c.input.head - 1 = h
            rw [hih]
            omega)
        (fun i hi => by
          show Parked (Function.update c.work q ((c.work q).move .left) i)
          rw [Function.update_of_ne hi]
          exact hwork i hi)
        hout
        (by show (Function.update c.work q _ q).cells 0 = _
            rw [Function.update_self]
            exact hc0)
        (fun j hj => by
          show (Function.update c.work q _ q).cells j ≠ _
          rw [Function.update_self]
          exact hcr j hj)
        (by show (Function.update c.work q _ q).head = h
            rw [Function.update_self]
            show (c.work q).head - 1 = h
            rw [hqh]
            omega)
    refine ⟨c', .step hstep₁ hreach, h1, h2, h3, ?_, ?_, h6, h7⟩
    · intro i hi
      rw [h4 i hi]
      show Function.update c.work q ((c.work q).move .left) i = c.work i
      rw [Function.update_of_ne hi]
    · rw [h5]
      show (Function.update c.work q ((c.work q).move .left) q).cells = _
      rw [Function.update_self]
      rfl

/-- **`inputLenRegTM` Hoare specification.** From the bumped initial input and
    `regTape 0` in `q`, reach `regTape |x|` in `q`, restoring the input exactly. -/
theorem inputLenRegTM_hoareTime (q : Fin n) (x : List Bool)
    (work₀ : Fin n → Tape) (ys : List Bool)
    (hwork₀ : ∀ i, i ≠ q → Parked (work₀ i)) (hq : work₀ q = regTape 0) :
    (inputLenRegTM (n := n) q).HoareTime
      (EmitPred ⟨1, (Tape.init (x.map Γ.ofBool)).cells⟩ work₀ ys)
      (EmitPred ⟨1, (Tape.init (x.map Γ.ofBool)).cells⟩
        (Function.update work₀ q (regTape x.length)) ys)
      (2 * x.length + 4) := by
  rintro inp work out ⟨rfl, rfl, hout⟩
  obtain ⟨c₁, hreach₁, h1, h2, h3, h4, h5, h6, h7⟩ :=
    inputLenRegTM_scan_run x x.length 0 (by omega)
      { state := .scan, input := ⟨1, (Tape.init (x.map Γ.ofBool)).cells⟩,
        work := work, output := out } rfl rfl rfl
      hwork₀ hout.parked
      (by show (work q).cells = regCells 0; rw [hq, regT_cells])
      (by show (work q).head = 0 + 1; rw [hq, regT_head])
  have hworkP₁ : ∀ i, i ≠ q → Parked (c₁.work i) := fun i hi => by
    rw [h4 i hi]
    exact hwork₀ i hi
  have houtP₁ : Parked c₁.output := by rw [h7]; exact hout.parked
  have hibl : c₁.input.read = Γ.blank := by
    rw [Tape.read, h3, h2]
    exact Tape.init_ofBool_cells_ge x x.length (le_refl _)
  have hqns₁ : (c₁.work q).read ≠ Γ.start := by
    rw [Tape.read, h6, h5]
    show regCells x.length (x.length + 1) ≠ Γ.start
    rw [regCells_blank (le_refl _)]
    decide
  have hstep₂ := inputLenRegTM_step_scan_blank c₁ h1 hibl hqns₁ hworkP₁ houtP₁
  obtain ⟨c₃, hreach₃, g1, g2, g3, g4, g5, g6, g7⟩ :=
    inputLenRegTM_back_run x x.length
      { state := .back, input := c₁.input.move .left,
        work := Function.update c₁.work q ((c₁.work q).move .left),
        output := c₁.output } rfl
      (by show (c₁.input.move .left).cells = _
          rw [Tape.move_cells]
          exact h2)
      (by show c₁.input.head - 1 = x.length
          rw [h3]
          omega)
      (fun i hi => by
        show Parked (Function.update c₁.work q ((c₁.work q).move .left) i)
        rw [Function.update_of_ne hi]
        exact hworkP₁ i hi)
      houtP₁
      (by show (Function.update c₁.work q _ q).cells 0 = _
          rw [Function.update_self]
          show (c₁.work q).cells 0 = _
          rw [h5]
          rfl)
      (fun j hj => by
        show (Function.update c₁.work q _ q).cells j ≠ _
        rw [Function.update_self]
        show (c₁.work q).cells j ≠ _
        rw [h5]
        show regCells x.length j ≠ Γ.start
        rw [regCells, ite_eq_right (by omega)]
        split <;> decide)
      (by show (Function.update c₁.work q _ q).head = x.length
          rw [Function.update_self]
          show (c₁.work q).head - 1 = x.length
          rw [h6]
          omega)
  refine ⟨c₃, x.length + ((x.length + 2) + 1), by omega,
    reachesIn_trans _ hreach₁ (.step hstep₂ hreach₃), g1, ?_, ?_, ?_⟩
  · refine Tape.ext ?_ ?_
    · rw [g3]
    · rw [g2]
  · funext i
    by_cases hir : i = q
    · subst hir
      rw [Function.update_self]
      refine Tape.ext ?_ ?_
      · rw [g6]
        rfl
      · rw [g5]
        show (Function.update c₁.work i ((c₁.work i).move .left) i).cells = _
        rw [Function.update_self]
        show (c₁.work i).cells = _
        rw [h5, regT_cells]
    · rw [Function.update_of_ne hir, g4 i hir]
      show Function.update c₁.work q ((c₁.work q).move .left) i = work i
      rw [Function.update_of_ne hir]
      exact h4 i hir
  · rw [g7, h7]
    exact hout

end InputLen

end TM

end Complexity
