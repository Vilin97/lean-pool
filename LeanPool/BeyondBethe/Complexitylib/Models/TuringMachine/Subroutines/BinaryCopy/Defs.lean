/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.BinaryRippleAdd.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.ClearWork.Defs

/-!
# Copying canonical binary naturals

This definitions layer composes work-tape clearing with width-linear canonical
binary addition. The source and zero scratch tapes are preserved, while the
destination is replaced by an exact copy of the source.
-/


@[expose] public section

namespace Complexity

namespace TM

/-- Clear `dstIdx`, then copy the canonical binary natural on `srcIdx` into it.
The distinct `counterIdx` supplies the preserved zero operand to ripple
addition, and `dstIdx` is its fresh result tape. -/
def binaryCopyIntoTM {n : ℕ}
    (srcIdx dstIdx counterIdx : Fin n) : TM n :=
  seqTM (clearWorkTM dstIdx)
    (binaryRippleAddTM srcIdx counterIdx dstIdx)

/-- Compositional running-time bound for canonical binary copying. -/
def binaryCopyTime (srcValue dstValue : ℕ) : ℕ :=
  clearWorkTimeBound dstValue.size + 1 + binaryRippleAddTime srcValue 0

/-- All-prefix auxiliary-space bound for canonical binary copying. -/
def binaryCopySpace (initialSpace srcValue dstValue : ℕ) : ℕ :=
  max (initialSpace + clearWorkTimeBound dstValue.size)
    (initialSpace + binaryRippleAddTime srcValue 0)

end TM

end Complexity
