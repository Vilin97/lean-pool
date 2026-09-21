/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Registers.RegisterOps
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.ResetBinary.Defs

/-!
# Resetting several binary work tapes — definitions

`resetBinaryWorkManyTM targets` sequentially rewinds and clears every work
tape named by `targets`. The executable machine depends only on the tape-index
list; represented contents and resource bounds occur only in its contracts.
-/


@[expose] public section

namespace Complexity

namespace TM

/-- The standard parked blank work tape produced by binary reset. -/
def resetBinaryBlank : Tape :=
  (Tape.init []).move Dir3.right

/-- Sequentially reset every work tape in `targets`, with `skipTM` as the
empty-list identity. -/
def resetBinaryWorkManyTM {n : ℕ} : List (Fin n) → TM n
  | [] => skipTM
  | idx :: rest => seqTM (resetBinaryWorkTM idx) (resetBinaryWorkManyTM rest)

/-- Exact work family obtained by applying the advertised resets in order. -/
def resetBinaryWorkManyResult {n : ℕ} :
    (Fin n → Tape) → List (Fin n) → Fin n → Tape
  | work, [] => work
  | work, idx :: rest =>
      resetBinaryWorkManyResult (Function.update work idx resetBinaryBlank) rest

/-- Compositional time bound: every reset is followed by one sequencing seam,
and the empty-list `skipTM` costs one final step. -/
def resetBinaryWorkManyTime {n : ℕ} (bits : Fin n → List Bool)
    (headBound : Fin n → ℕ) : List (Fin n) → ℕ
  | [] => 1
  | idx :: rest =>
      resetBinaryWorkTime (headBound idx) (bits idx).length + 1 +
        resetBinaryWorkManyTime bits headBound rest

end TM

end Complexity
