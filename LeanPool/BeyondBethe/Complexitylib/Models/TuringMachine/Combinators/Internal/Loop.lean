/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Combinators.Internal.Generic

/-!
# loopTM simulation — proof internals

This file contains the simulation lemmas for `loopTM tmBody tmTest`.

## Key definitions

- `loopBodyWrap` — embed a `tmBody` config into the `loopTM` config space
- `loopTestWrap` — embed a `tmTest` config into the `loopTM` config space
- Tape transformations use the shared `transitionTape` / `transitionInput`
-/


@[expose] public section

namespace Complexity

variable {n : ℕ}

namespace TM

-- ════════════════════════════════════════════════════════════════════════
-- Config wrapping
-- ════════════════════════════════════════════════════════════════════════

/-- Embed a `tmBody` config into the `loopTM` config space (body phase). -/
def loopBodyWrap (tmBody : TM n) (tmTest : TM n) (c : Cfg n tmBody.Q) :
    Cfg n (LoopQ tmBody.Q tmTest.Q) where
  state := Sum.inl c.state
  input := c.input
  work := c.work
  output := c.output

/-- Embed a `tmTest` config into the `loopTM` config space (test phase). -/
def loopTestWrap (tmBody : TM n) (tmTest : TM n) (c : Cfg n tmTest.Q) :
    Cfg n (LoopQ tmBody.Q tmTest.Q) where
  state := Sum.inr (Sum.inr c.state)
  input := c.input
  work := c.work
  output := c.output

-- ════════════════════════════════════════════════════════════════════════
-- Sum discrimination helpers
-- ════════════════════════════════════════════════════════════════════════

private theorem loopQ_body_ne_halt {QBody QTest : Type} {q : QBody} :
    (Sum.inl q : LoopQ QBody QTest) ≠ Sum.inr (Sum.inl LoopPhase.done) := nofun

private theorem loopQ_test_ne_halt {QBody QTest : Type} {q : QTest} :
    (Sum.inr (Sum.inr q) : LoopQ QBody QTest) ≠
      Sum.inr (Sum.inl LoopPhase.done) := nofun

-- ════════════════════════════════════════════════════════════════════════
-- Body phase: loopTM simulates tmBody (via generic simulation lifting)
-- ════════════════════════════════════════════════════════════════════════

/-- A non-halting `tmBody` step is simulated by one `loopTM` step on
body-wrapped configurations. -/
theorem loopTM_body_step (tmBody tmTest : TM n) {c c' : Cfg n tmBody.Q}
    (hstep : tmBody.step c = some c') :
    (loopTM tmBody tmTest).step (loopBodyWrap tmBody tmTest c) =
      some (loopBodyWrap tmBody tmTest c') := by
  have hne : c.state ≠ tmBody.qhalt := state_ne_qhalt_of_step hstep
  simp only [step, hne, ↓reduceIte, Option.some.injEq] at hstep
  subst hstep
  show (if (loopBodyWrap tmBody tmTest c).state =
           (loopTM tmBody tmTest).qhalt then none else some _) = some _
  simp only [loopBodyWrap, loopTM, if_neg loopQ_body_ne_halt, if_neg hne]

/-- A `t`-step run of `tmBody` lifts to a `t`-step run of `loopTM` between the
body-wrapped configurations. -/
theorem loopTM_body_simulation (tmBody tmTest : TM n) {t : ℕ}
    {c_start c_end : Cfg n tmBody.Q}
    (hreach : tmBody.reachesIn t c_start c_end) :
    (loopTM tmBody tmTest).reachesIn t
      (loopBodyWrap tmBody tmTest c_start) (loopBodyWrap tmBody tmTest c_end) :=
  reachesIn_map (tm' := loopTM tmBody tmTest) (loopBodyWrap tmBody tmTest)
    (fun _ _ => loopTM_body_step tmBody tmTest) hreach

-- ════════════════════════════════════════════════════════════════════════
-- Body → test transition
-- ════════════════════════════════════════════════════════════════════════

/-- When `tmBody` has halted, one `loopTM` step moves from the body-wrapped
configuration to `tmTest`'s start state, applying the shared tape transition to
every tape. -/
theorem loopTM_body_to_test (tmBody tmTest : TM n) {c : Cfg n tmBody.Q}
    (hhalt : c.state = tmBody.qhalt) :
    (loopTM tmBody tmTest).step (loopBodyWrap tmBody tmTest c) =
      some (loopTestWrap tmBody tmTest
        { state := tmTest.qstart,
          input := transitionInput c.input,
          work := fun i => transitionTape (c.work i),
          output := transitionTape c.output }) := by
  show (if (loopBodyWrap tmBody tmTest c).state =
           (loopTM tmBody tmTest).qhalt then none else some _) = some _
  simp only [loopBodyWrap, loopTM, if_neg loopQ_body_ne_halt, hhalt, ↓reduceIte]
  congr 1

-- ════════════════════════════════════════════════════════════════════════
-- Test phase: loopTM simulates tmTest (via generic simulation lifting)
-- ════════════════════════════════════════════════════════════════════════

/-- A non-halting `tmTest` step is simulated by one `loopTM` step on
test-wrapped configurations. -/
theorem loopTM_test_step (tmBody tmTest : TM n) {c c' : Cfg n tmTest.Q}
    (hstep : tmTest.step c = some c') :
    (loopTM tmBody tmTest).step (loopTestWrap tmBody tmTest c) =
      some (loopTestWrap tmBody tmTest c') := by
  have hne : c.state ≠ tmTest.qhalt := state_ne_qhalt_of_step hstep
  simp only [step, hne, ↓reduceIte, Option.some.injEq] at hstep
  subst hstep
  show (if (loopTestWrap tmBody tmTest c).state =
           (loopTM tmBody tmTest).qhalt then none else some _) = some _
  simp only [loopTestWrap, loopTM, if_neg loopQ_test_ne_halt, if_neg hne]

/-- A `t`-step run of `tmTest` lifts to a `t`-step run of `loopTM` between the
test-wrapped configurations. -/
theorem loopTM_test_simulation (tmBody tmTest : TM n) {t : ℕ}
    {c_start c_end : Cfg n tmTest.Q}
    (hreach : tmTest.reachesIn t c_start c_end) :
    (loopTM tmBody tmTest).reachesIn t
      (loopTestWrap tmBody tmTest c_start) (loopTestWrap tmBody tmTest c_end) :=
  reachesIn_map (tm' := loopTM tmBody tmTest) (loopTestWrap tmBody tmTest)
    (fun _ _ => loopTM_test_step tmBody tmTest) hreach

-- ════════════════════════════════════════════════════════════════════════
-- Test → rewind transition
-- ════════════════════════════════════════════════════════════════════════

/-- When `tmTest` has halted, one `loopTM` step moves from the test-wrapped
configuration to the `rewindOut` phase, applying the shared tape transition to
every tape. -/
theorem loopTM_test_to_rewind (tmBody tmTest : TM n) {c : Cfg n tmTest.Q}
    (hhalt : c.state = tmTest.qhalt) :
    (loopTM tmBody tmTest).step (loopTestWrap tmBody tmTest c) =
      some { state := Sum.inr (Sum.inl LoopPhase.rewindOut),
             input := transitionInput c.input,
             work := fun i => transitionTape (c.work i),
             output := transitionTape c.output } := by
  show (if (loopTestWrap tmBody tmTest c).state =
           (loopTM tmBody tmTest).qhalt then none else some _) = some _
  simp only [loopTestWrap, loopTM, if_neg loopQ_test_ne_halt, hhalt, ↓reduceIte]
  congr 1

-- ════════════════════════════════════════════════════════════════════════
-- Rewind loop (via generic rewind)
-- ════════════════════════════════════════════════════════════════════════

private theorem loop_rewind_step_left (tmBody tmTest : TM n)
    (c : Cfg n (LoopQ tmBody.Q tmTest.Q))
    (hstate : c.state = Sum.inr (Sum.inl LoopPhase.rewindOut))
    (hread_ne : c.output.read ≠ Γ.start)
    (_ : c.output.cells 0 = Γ.start) (_ : ∀ j, j ≥ 1 → c.output.cells j ≠ Γ.start) :
    ∃ c', (loopTM tmBody tmTest).step c = some c' ∧
      c'.state = Sum.inr (Sum.inl LoopPhase.rewindOut) ∧
      c'.output.head = c.output.head - 1 ∧
      c'.output.cells = c.output.cells := by
  have hne : c.state ≠ (loopTM tmBody tmTest).qhalt := by
    rw [hstate]; nofun
  simp only [TM.step, ↓reduceIte, hstate, loopTM, hread_ne]
  refine ⟨_, rfl, rfl, ?_, ?_⟩
  · simp only [Tape.writeAndMove, Tape.move]
    rw [toΓ_readBackWrite_of_ne_start hread_ne]
    simp only [Tape.write, Tape.read]; split
    · omega
    · simp
  · simp only [Tape.writeAndMove, Tape.move_cells]
    rw [toΓ_readBackWrite_of_ne_start hread_ne]
    simp only [Tape.write, Tape.read]; split
    · rfl
    · exact Function.update_eq_self _ _

private theorem loop_rewind_step_base (tmBody tmTest : TM n)
    (c : Cfg n (LoopQ tmBody.Q tmTest.Q))
    (hstate : c.state = Sum.inr (Sum.inl LoopPhase.rewindOut))
    (hread : c.output.read = Γ.start)
    (_ : c.output.cells 0 = Γ.start)
    (hnostart : ∀ j, j ≥ 1 → c.output.cells j ≠ Γ.start) :
    ∃ c', (loopTM tmBody tmTest).step c = some c' ∧
      c'.state = Sum.inr (Sum.inl LoopPhase.check) ∧
      c'.output.head = 1 ∧
      c'.output.cells = c.output.cells := by
  have hne : c.state ≠ (loopTM tmBody tmTest).qhalt := by
    rw [hstate]; nofun
  have hhead : c.output.head = 0 := by
    by_contra hne
    have hge : c.output.head ≥ 1 := by omega
    exact hnostart c.output.head hge (by simp only [Tape.read] at hread; exact hread)
  simp only [TM.step, ↓reduceIte, hstate, loopTM, hread]
  refine ⟨_, rfl, rfl, ?_, ?_⟩
  · simp [Tape.writeAndMove, Tape.move, Tape.write, hhead]
  · simp [Tape.writeAndMove, Tape.move_cells, Tape.write, hhead]

/-- From the `rewindOut` phase with the output head at position `p`, `loopTM`
reaches the `check` phase in `p + 1` steps with the output head at cell 1 and
the output cells unchanged. -/
theorem loopTM_rewind_loop (tmBody tmTest : TM n) :
    ∀ (p : ℕ) (c : Cfg n (LoopQ tmBody.Q tmTest.Q)),
    c.state = Sum.inr (Sum.inl LoopPhase.rewindOut) →
    c.output.cells 0 = Γ.start →
    (∀ j, j ≥ 1 → c.output.cells j ≠ Γ.start) →
    c.output.head = p →
    ∃ c_check,
      (loopTM tmBody tmTest).reachesIn (p + 1) c c_check ∧
      c_check.state = Sum.inr (Sum.inl LoopPhase.check) ∧
      c_check.output.head = 1 ∧
      c_check.output.cells = c.output.cells :=
  exists_reachesIn_of_rewindStep_output (loopTM tmBody tmTest)
    (fun c hst hread hc0 hns => loop_rewind_step_left tmBody tmTest c hst hread hc0 hns)
    (fun c hst hread hc0 hns => loop_rewind_step_base tmBody tmTest c hst hread hc0 hns)

-- ════════════════════════════════════════════════════════════════════════
-- Check step: halt (output = 1) or continue (output ≠ 1)
-- ════════════════════════════════════════════════════════════════════════

/-- In the `check` phase, if output cell 1 holds `1` then one `loopTM` step
enters the `done` phase, leaving the output cells unchanged. -/
theorem loopTM_check_halt (tmBody tmTest : TM n)
    (c : Cfg n (LoopQ tmBody.Q tmTest.Q))
    (hstate : c.state = Sum.inr (Sum.inl LoopPhase.check))
    (hhead : c.output.head = 1)
    (hcell1 : c.output.cells 1 = Γ.one) :
    ∃ c', (loopTM tmBody tmTest).step c = some c' ∧
      c'.state = Sum.inr (Sum.inl LoopPhase.done) ∧
      c'.output.cells = c.output.cells := by
  have hne : c.state ≠ (loopTM tmBody tmTest).qhalt := by
    rw [hstate]; nofun
  have hread : c.output.read = Γ.one := by simp [Tape.read, hhead, hcell1]
  simp only [TM.step, ↓reduceIte, hstate, loopTM, hread]
  refine ⟨_, rfl, rfl, ?_⟩
  show (c.output.writeAndMove (readBackWrite Γ.one).toΓ (idleDir Γ.one)).cells = c.output.cells
  simp only [readBackWrite, Γw.toΓ, idleDir, Tape.writeAndMove, Tape.move_cells]
  simp only [Tape.write]; split
  · omega
  · dsimp only []; rw [hhead, ← hcell1]; exact Function.update_eq_self _ _

/-- In the `check` phase, if output cell 1 does not hold `1` then one `loopTM`
step restarts `tmBody` (state `Sum.inl tmBody.qstart`), leaving the output
cells unchanged. -/
theorem loopTM_check_continue (tmBody tmTest : TM n)
    (c : Cfg n (LoopQ tmBody.Q tmTest.Q))
    (hstate : c.state = Sum.inr (Sum.inl LoopPhase.check))
    (hhead : c.output.head = 1)
    (hcell1 : c.output.cells 1 ≠ Γ.one)
    (hnostart : ∀ j, j ≥ 1 → c.output.cells j ≠ Γ.start) :
    ∃ c', (loopTM tmBody tmTest).step c = some c' ∧
      c'.state = Sum.inl tmBody.qstart ∧
      c'.output.cells = c.output.cells := by
  have hne : c.state ≠ (loopTM tmBody tmTest).qhalt := by
    rw [hstate]; nofun
  have hread_ne : c.output.read ≠ Γ.one := by
    simp [Tape.read, hhead]; exact hcell1
  have hread_ne_start : c.output.read ≠ Γ.start := by
    simp only [Tape.read, hhead]; exact hnostart 1 (by omega)
  simp only [TM.step, ↓reduceIte, hstate, loopTM, hread_ne]
  refine ⟨_, rfl, rfl, ?_⟩
  simp only [Tape.writeAndMove, Tape.move_cells]
  rw [toΓ_readBackWrite_of_ne_start hread_ne_start]
  simp only [Tape.write, Tape.read]; split
  · omega
  · rw [hhead]; exact Function.update_eq_self _ _

-- ════════════════════════════════════════════════════════════════════════
-- Halting
-- ════════════════════════════════════════════════════════════════════════

/-- A `loopTM` configuration in the `done` phase is halted. -/
theorem loopTM_halted_done (tmBody tmTest : TM n)
    (c : Cfg n (LoopQ tmBody.Q tmTest.Q))
    (h : c.state = Sum.inr (Sum.inl LoopPhase.done)) :
    (loopTM tmBody tmTest).halted c := h

-- ════════════════════════════════════════════════════════════════════════
-- One full iteration ending in halt
-- ════════════════════════════════════════════════════════════════════════

/-- One full `loopTM` iteration ending in halt: if `tmBody` halts in `t_body`
steps, `tmTest` then halts in `t_test` steps, and the resulting output tape
(head at `p`, cell 1 = `1`, `▷` only at cell 0) passes the check, then `loopTM`
halts from the body-wrapped start in `t_body + 1 + t_test + 1 + (p + 1) + 1`
steps with output cell 1 equal to `1`. -/
theorem loopTM_iteration_halt (tmBody tmTest : TM n)
    {t_body : ℕ} {c_body_start c_body_end : Cfg n tmBody.Q}
    (hreach_body : tmBody.reachesIn t_body c_body_start c_body_end)
    (hhalt_body : c_body_end.state = tmBody.qhalt)
    {t_test : ℕ} {c_test_end : Cfg n tmTest.Q}
    (hreach_test : tmTest.reachesIn t_test
      { state := tmTest.qstart,
        input := transitionInput c_body_end.input,
        work := fun i => transitionTape (c_body_end.work i),
        output := transitionTape c_body_end.output }
      c_test_end)
    (hhalt_test : c_test_end.state = tmTest.qhalt)
    {p : ℕ}
    (hcell0 : (transitionTape c_test_end.output).cells 0 = Γ.start)
    (hnostart : ∀ j, j ≥ 1 →
      (transitionTape c_test_end.output).cells j ≠ Γ.start)
    (hhead : (transitionTape c_test_end.output).head = p)
    (hcell1 : (transitionTape c_test_end.output).cells 1 = Γ.one) :
    ∃ c_final,
      (loopTM tmBody tmTest).reachesIn (t_body + 1 + t_test + 1 + (p + 1) + 1)
        (loopBodyWrap tmBody tmTest c_body_start) c_final ∧
      (loopTM tmBody tmTest).halted c_final ∧
      c_final.output.cells 1 = Γ.one := by
  -- Phase 1: body simulation
  have hp1 := loopTM_body_simulation tmBody tmTest hreach_body
  -- Body → test transition (1 step)
  have h_tr1 : (loopTM tmBody tmTest).reachesIn 1
      (loopBodyWrap tmBody tmTest c_body_end) (loopTestWrap tmBody tmTest _) :=
    .step (loopTM_body_to_test tmBody tmTest hhalt_body) .zero
  -- Phase 2: test simulation
  have hp2 := loopTM_test_simulation tmBody tmTest hreach_test
  -- Test → rewind transition (1 step)
  have h_tr2 : (loopTM tmBody tmTest).reachesIn 1
      (loopTestWrap tmBody tmTest c_test_end)
      { state := Sum.inr (Sum.inl LoopPhase.rewindOut),
        input := transitionInput c_test_end.input,
        work := fun i => transitionTape (c_test_end.work i),
        output := transitionTape c_test_end.output } :=
    .step (loopTM_test_to_rewind tmBody tmTest hhalt_test) .zero
  -- Rewind (p + 1 steps)
  obtain ⟨c_check, hreach_rw, hst_check, hh_check, hcells_check⟩ :=
    loopTM_rewind_loop tmBody tmTest p
      { state := Sum.inr (Sum.inl LoopPhase.rewindOut),
        input := transitionInput c_test_end.input,
        work := fun i => transitionTape (c_test_end.work i),
        output := transitionTape c_test_end.output }
      rfl hcell0 hnostart hhead
  -- Check: output at cell 1 is Γ.one
  obtain ⟨c_done, hstep_done, hst_done, hcells_done⟩ :=
    loopTM_check_halt tmBody tmTest c_check hst_check hh_check
      (by rw [hcells_check]; exact hcell1)
  -- Combine all phases
  have h_check : (loopTM tmBody tmTest).reachesIn 1 c_check c_done :=
    .step hstep_done .zero
  have h_all := reachesIn_trans _ (reachesIn_trans _ (reachesIn_trans _
    (reachesIn_trans _ (reachesIn_trans _ hp1 h_tr1) hp2) h_tr2) hreach_rw) h_check
  refine ⟨c_done, ?_, hst_done, ?_⟩
  · exact h_all
  · rw [hcells_done, hcells_check]; exact hcell1

end TM

end Complexity
