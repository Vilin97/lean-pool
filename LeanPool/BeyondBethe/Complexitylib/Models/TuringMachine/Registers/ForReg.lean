/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Registers.Emit

/-!
# forRegTM: the register-fueled loop combinator

`forRegTM body r` runs `body` once per mark of register `r`. The fuel is the
*head position* on `r`: the register's cells are never written; the test reads
the cell under the head — a mark means "iterate" (consume = move right, run
the body), the first blank means "exit" (rewind `r` to cell 1 and halt). The
body must leave `r` untouched (our ghost-style specs guarantee this for free,
since bodies preserve every non-target tape literally).

This is the only loop mechanism of the reduction emitter
(`docs/A5-ReductionEmitter.md`): unlike `loopTM`, its test reads a *work*
tape, so the output tape remains an append-only accumulator throughout.

The Hoare rule `forRegTM_hoareTime` threads an iteration-indexed family of
ghost work-tape functions and output words through the loop.
-/


@[expose] public section

namespace Complexity

namespace TM

variable {n : ℕ}

/-- Driver phases of `forRegTM`: `test` reads the fuel register's cell (mark = iterate,
    blank = exit), `rewind` returns the register head to cell 1, `done` is the halt state. -/
inductive ForPhase where
  | test | rewind | done
  deriving DecidableEq

/-- `ForPhase` is a finite type (it has exactly three constructors). -/
instance : Fintype ForPhase where
  elems := {.test, .rewind, .done}
  complete := fun x => by cases x <;> simp

/-- **Register-fueled loop**: run `body` once per mark of register `r`.
    States: the driver phases on the left, the body's states on the right. -/
def forRegTM (body : TM n) (r : Fin n) : TM n where
  Q := ForPhase ⊕ body.Q
  qstart := .inl .test
  qhalt := .inl .done
  δ := fun s iHead wHeads oHead =>
    match s with
    | .inl .test =>
      if wHeads r = Γ.one then
        (.inr body.qstart, fun i => readBackWrite (wHeads i), readBackWrite oHead,
         idleDir iHead, fun i => if i = r then Dir3.right else idleDir (wHeads i),
         idleDir oHead)
      else
        (.inl .rewind, fun i => readBackWrite (wHeads i), readBackWrite oHead,
         idleDir iHead,
         fun i => if i = r then (if wHeads r = Γ.start then Dir3.right else Dir3.left)
                  else idleDir (wHeads i),
         idleDir oHead)
    | .inl .rewind =>
      if wHeads r = Γ.start then
        (.inl .done, fun i => readBackWrite (wHeads i), readBackWrite oHead,
         idleDir iHead, fun i => if i = r then Dir3.right else idleDir (wHeads i),
         idleDir oHead)
      else
        (.inl .rewind, fun i => readBackWrite (wHeads i), readBackWrite oHead,
         idleDir iHead, fun i => if i = r then Dir3.left else idleDir (wHeads i),
         idleDir oHead)
    | .inl .done => allIdle s iHead wHeads oHead
    | .inr q =>
      if q = body.qhalt then
        (.inl .test, fun i => readBackWrite (wHeads i), readBackWrite oHead,
         idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
      else
        ((Sum.inr (body.δ q iHead wHeads oHead).1 : ForPhase ⊕ body.Q),
         (body.δ q iHead wHeads oHead).2.1,
         (body.δ q iHead wHeads oHead).2.2.1,
         (body.δ q iHead wHeads oHead).2.2.2.1,
         (body.δ q iHead wHeads oHead).2.2.2.2.1,
         (body.δ q iHead wHeads oHead).2.2.2.2.2)
  δ_right_of_start := by
    intro s iHead wHeads oHead
    match s with
    | .inl .test =>
      dsimp only []
      split
      · next hone =>
        refine ⟨idleDir_right_of_start, fun i hi => ?_, idleDir_right_of_start⟩
        dsimp only []
        by_cases hir : i = r
        · subst hir; rw [hone] at hi; exact absurd hi (by decide)
        · rw [if_neg hir]; exact idleDir_right_of_start hi
      · next hnone =>
        refine ⟨idleDir_right_of_start, fun i hi => ?_, idleDir_right_of_start⟩
        dsimp only []
        by_cases hir : i = r
        · subst hir; rw [if_pos rfl, if_pos hi]
        · rw [if_neg hir]; exact idleDir_right_of_start hi
    | .inl .rewind =>
      dsimp only []
      split
      · refine ⟨idleDir_right_of_start, fun i hi => ?_, idleDir_right_of_start⟩
        dsimp only []
        by_cases hir : i = r
        · rw [if_pos hir]
        · rw [if_neg hir]; exact idleDir_right_of_start hi
      · next hns =>
        refine ⟨idleDir_right_of_start, fun i hi => ?_, idleDir_right_of_start⟩
        dsimp only []
        by_cases hir : i = r
        · subst hir; exact absurd hi hns
        · rw [if_neg hir]; exact idleDir_right_of_start hi
    | .inl .done => exact rightOfStart_allIdle iHead wHeads oHead
    | .inr q =>
      dsimp only []
      split
      · exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start,
          idleDir_right_of_start⟩
      · exact body.δ_right_of_start q iHead wHeads oHead

section ForReg

variable {body : TM n} {r : Fin n}

/-- Retag a body configuration as a composite configuration. -/
private def wrapCfg (body : TM n) (r : Fin n) (c : Cfg n body.Q) :
    Cfg n (forRegTM body r).Q :=
  { state := .inr c.state, input := c.input, work := c.work, output := c.output }

/-- Body steps lift to composite steps. -/
private theorem forRegTM_lift_step (c c' : Cfg n body.Q)
    (hstep : body.step c = some c') :
    (forRegTM body r).step (wrapCfg body r c) = some (wrapCfg body r c') := by
  have hne : ¬ c.state = body.qhalt := by
    intro h
    rw [TM.step, if_pos h] at hstep
    simp at hstep
  rw [TM.step, if_neg hne] at hstep
  rw [TM.step, if_neg (show ¬ (wrapCfg body r c).state = (forRegTM body r).qhalt from
    by simp [wrapCfg, forRegTM])]
  simp only [wrapCfg, forRegTM, hne, ↓reduceIte]
  revert hstep
  generalize body.δ c.state c.input.read (fun i => (c.work i).read) c.output.read = bd
  obtain ⟨q', ww, ow, iD, wD, oD⟩ := bd
  intro hstep
  cases Option.some.inj hstep
  rfl

private theorem forRegTM_ne_halt {s : ForPhase ⊕ body.Q} (h : s ≠ .inl .done)
    {c : Cfg n (forRegTM body r).Q} (hst : c.state = s) :
    ¬ c.state = (forRegTM body r).qhalt := by
  rw [hst]
  show ¬ s = Sum.inl ForPhase.done
  exact h

/-- `test` over a mark: consume it (register head right) and enter the body. -/
private theorem forRegTM_step_test_one (c : Cfg n (forRegTM body r).Q)
    (hst : c.state = .inl .test) (hone : (c.work r).read = Γ.one)
    (hinp : Parked c.input) (hwork : ∀ i, i ≠ r → Parked (c.work i))
    (hout : Parked c.output) :
    (forRegTM body r).step c = some
      { state := .inr body.qstart, input := c.input,
        work := Function.update c.work r ((c.work r).move .right),
        output := c.output } := by
  rw [TM.step, if_neg (forRegTM_ne_halt (by simp) hst)]
  simp only [forRegTM, hst, hone, ↓reduceIte]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact hinp.move_idle
  · funext i
    by_cases hir : i = r
    · subst hir
      rw [if_pos rfl, Function.update_self,
        writeAndMove_readBack _ (by rw [hone]; decide)]
    · rw [if_neg hir, Function.update_of_ne hir]
      exact (hwork i hir).writeAndMove_readBack_idle
  · exact hout.writeAndMove_readBack_idle

/-- `test` at the first blank: exit toward the rewind. -/
private theorem forRegTM_step_test_blank (c : Cfg n (forRegTM body r).Q)
    (hst : c.state = .inl .test) (hblank : (c.work r).read = Γ.blank)
    (hinp : Parked c.input) (hwork : ∀ i, i ≠ r → Parked (c.work i))
    (hout : Parked c.output) :
    (forRegTM body r).step c = some
      { state := .inl .rewind, input := c.input,
        work := Function.update c.work r ((c.work r).move .left),
        output := c.output } := by
  rw [TM.step, if_neg (forRegTM_ne_halt (by simp) hst)]
  simp only [forRegTM, hst, hblank, reduceCtorEq, ↓reduceIte]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact hinp.move_idle
  · funext i
    by_cases hir : i = r
    · subst hir
      simp only [↓reduceIte, Function.update_self]
      rw [writeAndMove_readBack _ (by rw [hblank]; decide)]
    · rw [if_neg hir, Function.update_of_ne hir]
      exact (hwork i hir).writeAndMove_readBack_idle
  · exact hout.writeAndMove_readBack_idle

/-- `rewind` off the sentinel: keep rewinding. -/
private theorem forRegTM_step_rewind_left (c : Cfg n (forRegTM body r).Q)
    (hst : c.state = .inl .rewind) (hns : (c.work r).read ≠ Γ.start)
    (hinp : Parked c.input) (hwork : ∀ i, i ≠ r → Parked (c.work i))
    (hout : Parked c.output) :
    (forRegTM body r).step c = some
      { state := .inl .rewind, input := c.input,
        work := Function.update c.work r ((c.work r).move .left),
        output := c.output } := by
  rw [TM.step, if_neg (forRegTM_ne_halt (by simp) hst)]
  simp only [forRegTM, hst, hns, ↓reduceIte]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact hinp.move_idle
  · funext i
    by_cases hir : i = r
    · subst hir
      rw [if_pos rfl, Function.update_self, writeAndMove_readBack _ hns]
    · rw [if_neg hir, Function.update_of_ne hir]
      exact (hwork i hir).writeAndMove_readBack_idle
  · exact hout.writeAndMove_readBack_idle

/-- `rewind` on the sentinel: step right to cell 1 and halt. -/
private theorem forRegTM_step_rewind_start (c : Cfg n (forRegTM body r).Q)
    (hst : c.state = .inl .rewind) (hs : (c.work r).read = Γ.start)
    (hcr : ∀ j, 1 ≤ j → (c.work r).cells j ≠ Γ.start)
    (hinp : Parked c.input) (hwork : ∀ i, i ≠ r → Parked (c.work i))
    (hout : Parked c.output) :
    (forRegTM body r).step c = some
      { state := .inl .done, input := c.input,
        work := Function.update c.work r ((c.work r).move .right),
        output := c.output } := by
  have h0 : (c.work r).head = 0 := by
    by_contra hc
    exact hcr _ (by omega) hs
  rw [TM.step, if_neg (forRegTM_ne_halt (by simp) hst)]
  simp only [forRegTM, hst, hs, ↓reduceIte]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact hinp.move_idle
  · funext i
    by_cases hir : i = r
    · subst hir
      rw [if_pos rfl, Function.update_self]
      show ((c.work i).write _).move Dir3.right = (c.work i).move .right
      congr 1
      rw [Tape.write, if_pos h0]
    · rw [if_neg hir, Function.update_of_ne hir]
      exact (hwork i hir).writeAndMove_readBack_idle
  · exact hout.writeAndMove_readBack_idle

/-- The body has halted: one idle step loops back to the test. -/
private theorem forRegTM_step_loopback (c : Cfg n (forRegTM body r).Q)
    (hst : c.state = .inr body.qhalt)
    (hinp : Parked c.input) (hwork : ∀ i, Parked (c.work i))
    (hout : Parked c.output) :
    (forRegTM body r).step c = some
      { state := .inl .test, input := c.input, work := c.work,
        output := c.output } := by
  rw [TM.step, if_neg (forRegTM_ne_halt (by simp) hst)]
  simp only [forRegTM, hst, ↓reduceIte]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact hinp.move_idle
  · funext i
    exact (hwork i).writeAndMove_readBack_idle
  · exact hout.writeAndMove_readBack_idle

/-- The rewind loop: from `rewind` at head `h`, halt parked at cell 1 in
    `h + 1` steps. -/
private theorem forRegTM_rewind_run (h : ℕ) :
    ∀ (c : Cfg n (forRegTM body r).Q),
      c.state = .inl .rewind → Parked c.input → (∀ i, i ≠ r → Parked (c.work i)) →
      Parked c.output →
      (c.work r).cells 0 = Γ.start →
      (∀ j, 1 ≤ j → (c.work r).cells j ≠ Γ.start) →
      (c.work r).head = h →
      ∃ c', (forRegTM body r).reachesIn (h + 1) c c' ∧
        c'.state = .inl .done ∧ c'.input = c.input ∧
        (∀ i, i ≠ r → c'.work i = c.work i) ∧
        (c'.work r).cells = (c.work r).cells ∧ (c'.work r).head = 1 ∧
        c'.output = c.output := by
  induction h with
  | zero =>
    intro c hst hinp hwork hout hc0 hcr hhead
    have hs : (c.work r).read = Γ.start := by rw [Tape.read, hhead]; exact hc0
    have hstep := forRegTM_step_rewind_start c hst hs hcr hinp hwork hout
    refine ⟨_, .step hstep .zero, rfl, rfl, ?_, ?_, ?_, rfl⟩
    · intro i hi
      show Function.update c.work r ((c.work r).move .right) i = c.work i
      rw [Function.update_of_ne hi]
    · show (Function.update c.work r ((c.work r).move .right) r).cells = _
      rw [Function.update_self]
      rfl
    · show (Function.update c.work r ((c.work r).move .right) r).head = 1
      rw [Function.update_self]
      show (c.work r).head + 1 = 1
      rw [hhead]
  | succ h ih =>
    intro c hst hinp hwork hout hc0 hcr hhead
    have hns : (c.work r).read ≠ Γ.start := by
      rw [Tape.read, hhead]; exact hcr (h + 1) (by omega)
    have hstep := forRegTM_step_rewind_left c hst hns hinp hwork hout
    have hupd : (Function.update c.work r ((c.work r).move .left) r).cells
        = (c.work r).cells := by
      rw [Function.update_self]
      rfl
    obtain ⟨c', hreach, hst', hinp', hwork', hcells', hhead', hout'⟩ :=
      ih { state := .inl .rewind, input := c.input,
           work := Function.update c.work r ((c.work r).move .left),
           output := c.output } rfl hinp
        (fun i hi => by
          show Parked (Function.update c.work r ((c.work r).move .left) i)
          rw [Function.update_of_ne hi]
          exact hwork i hi)
        hout
        (by rw [hupd]; exact hc0)
        (fun j hj => by rw [hupd]; exact hcr j hj)
        (by
          show (Function.update c.work r ((c.work r).move .left) r).head = h
          rw [Function.update_self]
          show (c.work r).head - 1 = h
          rw [hhead]
          omega)
    refine ⟨c', .step hstep hreach, hst', hinp', ?_, ?_, hhead', hout'⟩
    · intro i hi
      rw [hwork' i hi]
      show Function.update c.work r ((c.work r).move .left) i = c.work i
      rw [Function.update_of_ne hi]
    · rw [hcells', hupd]

/-- The iteration loop: from the `i`-th test entry, run the remaining `m`
    iterations and the exit rewind. -/
private theorem forRegTM_loop_run (inp₀ : Tape) (w : ℕ → Fin n → Tape)
    (ys : ℕ → List Bool) (b_iter v : ℕ)
    (hinp₀ : Parked inp₀)
    (hwP : ∀ i j, j ≠ r → Parked (w i j))
    (hbody : ∀ i, i < v → body.HoareTime
        (fun inp work out => inp = inp₀ ∧
          work = Function.update (w i) r ⟨i + 2, regCells v⟩ ∧ OutAcc (ys i) out)
        (fun inp work out => inp = inp₀ ∧
          work = Function.update (w (i + 1)) r ⟨i + 2, regCells v⟩ ∧
          OutAcc (ys (i + 1)) out)
        b_iter) :
    ∀ (m i : ℕ), v = i + m →
      ∀ c : Cfg n (forRegTM body r).Q,
      c.state = .inl .test → c.input = inp₀ →
      c.work = Function.update (w i) r ⟨i + 1, regCells v⟩ →
      OutAcc (ys i) c.output →
      ∃ c' t, t ≤ m * (b_iter + 2) + (v + 2) ∧
        (forRegTM body r).reachesIn t c c' ∧
        c'.state = .inl .done ∧ c'.input = inp₀ ∧
        c'.work = Function.update (w v) r (regTape v) ∧
        OutAcc (ys v) c'.output := by
  intro m
  induction m with
  | zero =>
    intro i hi c hst hcin hcw hout
    obtain rfl : v = i := by omega
    have hcwr : c.work r = ⟨v + 1, regCells v⟩ := by
      rw [hcw, Function.update_self]
    have hblank : (c.work r).read = Γ.blank := by
      rw [hcwr]
      show regCells v (v + 1) = Γ.blank
      exact regCells_blank (le_refl _)
    have hworkP : ∀ j, j ≠ r → Parked (c.work j) := by
      intro j hj
      rw [hcw, Function.update_of_ne hj]
      exact hwP v j hj
    have hinpP : Parked c.input := by rw [hcin]; exact hinp₀
    have hstep₁ := forRegTM_step_test_blank c hst hblank hinpP hworkP hout.parked
    have hw₁ : Function.update c.work r ((c.work r).move .left)
        = Function.update (w v) r ⟨v, regCells v⟩ := by
      rw [hcwr, hcw, Function.update_idem]
      rfl
    obtain ⟨c', hreach, hst', hinp', hwork', hcells', hhead', hout'⟩ :=
      forRegTM_rewind_run (body := body) v
        { state := .inl .rewind, input := c.input,
          work := Function.update (w v) r ⟨v, regCells v⟩, output := c.output }
        rfl hinpP
        (fun j hj => by
          show Parked (Function.update (w v) r (⟨v, regCells v⟩ : Tape) j)
          rw [Function.update_of_ne hj]
          exact hwP v j hj)
        hout.parked
        (by
          show (Function.update (w v) r (⟨v, regCells v⟩ : Tape) r).cells 0 = Γ.start
          rw [Function.update_self]
          rfl)
        (fun j hj => by
          show (Function.update (w v) r (⟨v, regCells v⟩ : Tape) r).cells j ≠ Γ.start
          rw [Function.update_self]
          show regCells v j ≠ Γ.start
          rw [regCells, if_neg (by omega)]
          split <;> decide)
        (by
          show (Function.update (w v) r (⟨v, regCells v⟩ : Tape) r).head = v
          rw [Function.update_self])
    have hb0 : (v + 1) + 1 ≤ 0 * (b_iter + 2) + (v + 2) := by omega
    refine ⟨c', (v + 1) + 1, hb0, .step hstep₁ ?_, hst', ?_, ?_, ?_⟩
    · rw [hw₁]
      exact hreach
    · rw [hinp']
      show c.input = inp₀
      exact hcin
    · funext j
      by_cases hjr : j = r
      · subst hjr
        rw [Function.update_self]
        refine Tape.ext ?_ ?_
        · rw [hhead']
          rfl
        · rw [hcells']
          show (Function.update (w v) j (⟨v, regCells v⟩ : Tape) j).cells = _
          rw [Function.update_self, regT_cells]
      · rw [hwork' j hjr, Function.update_of_ne hjr]
        show Function.update (w v) r (⟨v, regCells v⟩ : Tape) j = w v j
        rw [Function.update_of_ne hjr]
    · rw [hout']
      exact hout
  | succ m ih =>
    intro i hi c hst hcin hcw hout
    have hcwr : c.work r = ⟨i + 1, regCells v⟩ := by
      rw [hcw, Function.update_self]
    have hone : (c.work r).read = Γ.one := by
      rw [hcwr]
      show regCells v (i + 1) = Γ.one
      exact regCells_one (by omega) (by omega)
    have hworkP : ∀ j, j ≠ r → Parked (c.work j) := by
      intro j hj
      rw [hcw, Function.update_of_ne hj]
      exact hwP i j hj
    have hinpP : Parked c.input := by rw [hcin]; exact hinp₀
    have hstep₁ := forRegTM_step_test_one c hst hone hinpP hworkP hout.parked
    have hw₁ : Function.update c.work r ((c.work r).move .right)
        = Function.update (w i) r ⟨i + 2, regCells v⟩ := by
      rw [hcwr, hcw, Function.update_idem]
      rfl
    obtain ⟨cb, tb, htb, hbreach, hbhalt, hbinp, hbwork, hbout⟩ :=
      hbody i (by omega) inp₀ (Function.update (w i) r ⟨i + 2, regCells v⟩) c.output
        ⟨rfl, rfl, hout⟩
    have hlift := reachesIn_map (wrapCfg body r)
      (fun a b h => forRegTM_lift_step a b h) hbreach
    have hbworkP : ∀ j, Parked (cb.work j) := by
      intro j
      rw [hbwork]
      by_cases hjr : j = r
      · subst hjr
        rw [Function.update_self]
        refine ⟨by show (1 : ℕ) ≤ i + 2; omega, fun p hp => ?_⟩
        show regCells v p ≠ Γ.start
        rw [regCells, if_neg (by omega)]
        split <;> decide
      · rw [Function.update_of_ne hjr]
        exact hwP (i + 1) j hjr
    have hstep₂ := forRegTM_step_loopback (wrapCfg body r cb)
      (by show Sum.inr cb.state = Sum.inr body.qhalt; rw [hbhalt])
      (by show Parked cb.input; rw [hbinp]; exact hinp₀)
      (fun j => hbworkP j)
      (by show Parked cb.output; exact hbout.parked)
    obtain ⟨c', t', ht', hreach', hst', hinp', hwork', hout'⟩ :=
      ih (i + 1) (by omega)
        { state := .inl .test, input := inp₀,
          work := Function.update (w (i + 1)) r ⟨i + 2, regCells v⟩,
          output := cb.output }
        rfl rfl rfl hbout
    have hbS : tb + (t' + 1) + 1 ≤ (m + 1) * (b_iter + 2) + (v + 2) := by
      have hmul : (m + 1) * (b_iter + 2) = m * (b_iter + 2) + (b_iter + 2) :=
        Nat.succ_mul ..
      omega
    refine ⟨c', tb + (t' + 1) + 1, hbS, .step hstep₁ ?_, hst', hinp', hwork', hout'⟩
    rw [hw₁, hcin]
    refine reachesIn_trans _ hlift (.step hstep₂ ?_)
    rw [show (⟨.inl .test, (wrapCfg body r cb).input, (wrapCfg body r cb).work,
        (wrapCfg body r cb).output⟩ : Cfg n (forRegTM body r).Q)
        = ⟨.inl .test, inp₀, Function.update (w (i + 1)) r ⟨i + 2, regCells v⟩,
           cb.output⟩ from by
      simp only [wrapCfg]
      rw [hbinp, hbwork]]
    exact hreach'

/-- **`forRegTM` Hoare rule.** Given a fuel register holding `v` (whose tape the
    iteration-indexed ghost family `w` never changes) and a body spec carrying
    `w i / ys i` to `w (i+1) / ys (i+1)`, the loop carries `w 0 / ys 0` to
    `w v / ys v` in at most `v·(b_iter + 2) + v + 3` steps. -/
theorem forRegTM_hoareTime (body : TM n) (r : Fin n) (v : ℕ) (inp₀ : Tape)
    (w : ℕ → Fin n → Tape) (ys : ℕ → List Bool) (b_iter : ℕ)
    (hinp₀ : Parked inp₀)
    (hwreg : ∀ i, w i r = regTape v)
    (hwP : ∀ i j, j ≠ r → Parked (w i j))
    (hbody : ∀ i, i < v → body.HoareTime
        (fun inp work out => inp = inp₀ ∧
          work = Function.update (w i) r ⟨i + 2, regCells v⟩ ∧ OutAcc (ys i) out)
        (fun inp work out => inp = inp₀ ∧
          work = Function.update (w (i + 1)) r ⟨i + 2, regCells v⟩ ∧
          OutAcc (ys (i + 1)) out)
        b_iter) :
    (forRegTM body r).HoareTime
      (EmitPred inp₀ (w 0) (ys 0))
      (EmitPred inp₀ (w v) (ys v))
      (v * (b_iter + 2) + (v + 2)) := by
  rintro inp work out ⟨rfl, rfl, hout⟩
  obtain ⟨c', t, ht, hreach, hst', hinp', hwork', hout'⟩ :=
    forRegTM_loop_run inp w ys b_iter v hinp₀ hwP hbody v 0 (by omega)
      { state := .inl .test, input := inp, work := w 0, output := out }
      rfl rfl
      (by
        show w 0 = Function.update (w 0) r ⟨0 + 1, regCells v⟩
        rw [show (⟨0 + 1, regCells v⟩ : Tape) = w 0 r from by rw [hwreg 0]; rfl,
          Function.update_eq_self])
      hout
  refine ⟨c', t, ht, hreach, hst', hinp', ?_, hout'⟩
  rw [hwork', show regTape v = w v r from (hwreg v).symm, Function.update_eq_self]

end ForReg

end TM

end Complexity
