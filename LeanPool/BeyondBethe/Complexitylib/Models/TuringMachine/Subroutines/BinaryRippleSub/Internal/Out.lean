/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.BinaryRippleSub.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.ClearWork.Internal

/-!
# Linear-time canonical binary subtraction -- output discipline

The borrow scan, backward cleanup, and operand rewinds leave the public output
tape one-way, so the core and complete machines are safe transducers.
-/


@[expose] public section

namespace Complexity

namespace TM

/-- The direct subtraction core never moves the public output head left. -/
theorem binaryRippleSubCoreTM_isTransducer_internal {n : ℕ}
    (lhsIdx rhsIdx resultIdx : Fin n) :
    (binaryRippleSubCoreTM lhsIdx rhsIdx resultIdx).IsTransducer := by
  intro phase iHead wHeads oHead
  cases phase with
  | scan borrow =>
      simp only [binaryRippleSubCoreTM]
      split <;> simp [idleDir] <;> split <;> decide
  | erase =>
      simp only [binaryRippleSubCoreTM]
      split <;> simp [idleDir] <;> split <;> decide
  | trim seenOne =>
      simp only [binaryRippleSubCoreTM]
      split
      · simp [idleDir]
        split <;> decide
      · split
        · simp [idleDir]
          split <;> decide
        · simp [idleDir]
          split <;> decide
  | done =>
      simp [binaryRippleSubCoreTM, allIdle, idleDir]
      split <;> decide

/-- Backward canonicalization followed by both operand rewinds remains a
transducer. -/
theorem binaryRippleSubTM_isTransducer_internal {n : ℕ}
    (lhsIdx rhsIdx resultIdx : Fin n) :
    (binaryRippleSubTM lhsIdx rhsIdx resultIdx).IsTransducer := by
  exact (binaryRippleSubCoreTM_isTransducer_internal
    lhsIdx rhsIdx resultIdx).seqTM
      ((rewindWorkTM_isTransducer_internal lhsIdx).seqTM
        (rewindWorkTM_isTransducer_internal rhsIdx))

end TM

end Complexity
