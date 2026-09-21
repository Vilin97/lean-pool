/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Combinators.ForBinaryWork
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Combinators.WorkSymbolBranch
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.BinaryCopy
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.BinaryShiftMul.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.ResetBinaryMany

/-!
# Width-driven binary shift-and-add multiplication -- output safety

This file composes the transducer certificates of every multiplication phase.
-/


public section

namespace Complexity

namespace TM

private theorem binaryShiftMulUpdateTM_isTransducer {n : ℕ}
    (abi : BinaryShiftMulABI n) :
    (binaryShiftMulUpdateTM abi).IsTransducer := by
  unfold binaryShiftMulUpdateTM
  exact (binaryRippleAddTM_isTransducer abi.acc abi.shift abi.tmp).seqTM
    ((binaryCopyIntoTM_isTransducer abi.tmp abi.acc abi.dbl).seqTM
      (resetBinaryWorkTM_isTransducer abi.tmp))

private theorem binaryShiftMulDoubleTM_isTransducer {n : ℕ}
    (abi : BinaryShiftMulABI n) :
    (binaryShiftMulDoubleTM abi).IsTransducer := by
  unfold binaryShiftMulDoubleTM
  exact (binaryCopyIntoTM_isTransducer abi.shift abi.tmp abi.dbl).seqTM
    ((binaryRippleAddTM_isTransducer abi.shift abi.tmp abi.dbl).seqTM
      ((resetBinaryWorkTM_isTransducer abi.tmp).seqTM
        ((binaryCopyIntoTM_isTransducer abi.dbl abi.shift abi.tmp).seqTM
          (resetBinaryWorkTM_isTransducer abi.dbl))))

private theorem binaryShiftMulBitBodyTM_isTransducer {n : ℕ}
    (abi : BinaryShiftMulABI n) :
    (binaryShiftMulBitBodyTM abi).IsTransducer := by
  unfold binaryShiftMulBitBodyTM binaryShiftMulOneTM
  exact (binaryShiftMulUpdateTM_isTransducer abi).seqTM
    (binaryShiftMulDoubleTM_isTransducer abi) |>.branchWorkSymbolTM
      (binaryShiftMulDoubleTM_isTransducer abi)

/-- Shift-and-add multiplication never moves the public output head left. -/
theorem binaryShiftMulTM_isTransducer_internal {n : ℕ}
    (abi : BinaryShiftMulABI n) :
    (binaryShiftMulTM abi).IsTransducer := by
  unfold binaryShiftMulTM binaryShiftMulInitTM binaryShiftMulLoopTM
    binaryShiftMulCleanupTM
  exact (binaryCopyIntoTM_isTransducer abi.lhs abi.shift abi.acc).seqTM
    ((binaryShiftMulBitBodyTM_isTransducer abi).forBinaryWorkTM.seqTM
      ((rewindWorkTM_isTransducer abi.rhs).seqTM
        (resetBinaryWorkManyTM_isTransducer [abi.shift, abi.tmp, abi.dbl])))

end TM

end Complexity
