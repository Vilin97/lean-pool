/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.ClearWork.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines

/-!
# Resetting a binary work tape — definitions

`resetBinaryWorkTM` first rewinds an arbitrary cursor over canonical binary
contents and then clears the resulting completed string to the standard blank
work tape.
-/


@[expose] public section

namespace Complexity

namespace TM

/-- Rewind and clear one canonical binary work tape. -/
def resetBinaryWorkTM {n : ℕ} (idx : Fin n) : TM n :=
  seqTM (rewindWorkTM idx) (clearWorkTM idx)

/-- Time bound in terms of the initial head bound and represented bit length. -/
def resetBinaryWorkTime (headBound bitLength : ℕ) : ℕ :=
  headBound + 2 + 1 + clearWorkTimeBound bitLength

end TM

end Complexity
