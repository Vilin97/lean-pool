/-
Copyright (c) 2026 Julius Marx. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julius Marx
-/
import LeanPool.MRiscX.Tactics.GeneralCustomTactics
import LeanPool.MRiscX.AbstractSyntax.Instr
import LeanPool.MRiscX.AbstractSyntax.MState

/-!
# SpecificationTactics

This module provides tactics proving the per-instruction specifications.
-/

open Lean Elab Tactic

/- The proof for most specifications of instructions -/
/-- Unfold and simplify the Hoare specification in the goal. -/
elab "hoareSimpSpecification" : tactic => do
  evalTactic (← `(tactic| intro Hl))
  evalTactic (← `(tactic| rw [Hl]))
  evalTactic (← `(tactic| unfold $(mkIdent `hoare_triple_up_1)))
  evalTactic (← `(tactic| rintro _ _ s HCurr h_pc ⟨pre, h_terminated⟩))
  evalTactic (← `(tactic| simp at h_terminated))
  evalTactic (← `(tactic| unfold $(mkIdent `weak)))
  evalTactic (← `(tactic| exists s.runOneStep))
  evalTactic (← `(tactic| apply And.intro))
  evalTactic (← `(tactic|
    case left =>
      intros _
      exists 1
      apply And.intro
      simp
      case right =>
        simp [<- $(mkIdent `MState.run_one_step_eq_run_n_1)]
        unfold $(mkIdent `MState.runOneStep)
        rw [h_terminated, ←h_pc, HCurr]
        simp
        zeroLtNeZero
  ))
  evalTactic (← `(tactic|
    case right =>
      -- try rw [xor_iff_notation] at pre
      simp [<- $(mkIdent `MState.run_one_step_eq_run_n_1)]
      unfold $(mkIdent `MState.runOneStep)
      rw [HCurr]
      simp
      simp [pre, h_terminated, ←h_pc]
      simp at pre
      rw [h_terminated] at pre
      rw [h_pc]
      rw [h_pc] at pre
      exact pre
  ))


/- The proof of correctness for the specification of conditional jump instruction when the condition
is false -/
/-- Simplify a jump specification whose branch condition is false. -/
elab "simpJumpSpecFalse" : tactic => do
  evalTactic (← `(tactic| intro HL))
  evalTactic (← `(tactic| rw [HL]))
  evalTactic (← `(tactic| unfold $(mkIdent `hoare_triple_up_1)))
  evalTactic (← `(tactic| rintro _ _ state h_curr h_pc ⟨pre, h_cond, h_terminated⟩))
  evalTactic (← `(tactic| simp at h_terminated))
  evalTactic (← `(tactic| simp at h_cond))
  evalTactic (← `(tactic| simp at h_curr))
  evalTactic (← `(tactic| exists state.runOneStep))
  evalTactic (← `(tactic| unfold $(mkIdent `weak)))
  evalTactic (← `(tactic| apply And.intro))
  evalTactic (← `(tactic|
    case left =>
      intros _
      exists 1
      apply And.intro; simp
      · repeat (constructor <;> try simp)
        · simp [← $(mkIdent `MState.run_one_step_eq_run_n_1)]
          unfold $(mkIdent `MState.runOneStep) $(mkIdent `MState.jif') $(mkIdent `MState.jif)
            $(mkIdent `MState.jump)
          rw [h_terminated, ← h_pc]
          simp [h_curr, h_cond]
        · zeroLtNeZero
  ))
  evalTactic (← `(tactic|
    case right =>
      simp [← $(mkIdent `MState.run_one_step_eq_run_n_1)]
      unfold $(mkIdent `MState.runOneStep) $(mkIdent `MState.jif') $(mkIdent `MState.jif)
        $(mkIdent `MState.jump)
      rw [h_terminated]
      simp [h_curr, h_cond, pre]
      rw [← h_pc, h_terminated]
      simp
      simp [←h_pc, h_terminated] at pre
      exact pre
    ))



/- The proof of correctness for the specification of conditional jump instruction when the condition
is true -/
/-- Simplify a jump specification whose branch condition is true. -/
elab "simpJumpSpecTrue" : tactic => do
  evalTactic (← `(tactic| intro HL))
  evalTactic (← `(tactic| rw [HL]))
  evalTactic (← `(tactic| unfold $(mkIdent `hoare_triple_up_1)))
  evalTactic (← `(tactic| rintro _ _ state h_curr h_pc ⟨pre, h_label, h_cond, h_terminated⟩))
  evalTactic (← `(tactic| simp at h_terminated))
  evalTactic (← `(tactic| simp at h_label))
  evalTactic (← `(tactic| simp at h_cond))
  evalTactic (← `(tactic| unfold MState.currInstruction at h_curr))
  evalTactic (← `(tactic| exists state.runOneStep))
  evalTactic (← `(tactic| unfold $(mkIdent `weak)))
  evalTactic (← `(tactic| apply And.intro))
  evalTactic (← `(tactic|
    case left =>
    intros _
    exists 1
    apply And.intro; simp
    · repeat (constructor <;> try simp)
      · simp [← $(mkIdent `MState.run_one_step_eq_run_n_1)]
        unfold $(mkIdent `MState.runOneStep) $(mkIdent `MState.jif') $(mkIdent `MState.jif)
          $(mkIdent `MState.jump)
        rw [h_terminated]
        simp [h_curr, h_label, h_cond]
      · zeroLtNeZero
  ))
  evalTactic (← `(tactic|
    case right =>
      simp [<- $(mkIdent `MState.run_one_step_eq_run_n_1)]
      unfold $(mkIdent `MState.runOneStep) $(mkIdent `MState.jif') $(mkIdent `MState.jif)
        $(mkIdent `MState.jump)
      unfold $(mkIdent `MState.setPc) at pre
      rw [h_terminated]
      rw [h_terminated] at pre
      simp [h_curr, h_label, h_cond, pre]
    ))



/-- Simplify a jump specification in the goal. -/
elab "simpJumpSpec" : tactic => do
  evalTactic (← `(tactic | first
                          | simpJumpSpecFalse
                          | simpJumpSpecTrue)
  )
