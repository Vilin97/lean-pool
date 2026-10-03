/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Combinators

/-!
# Binary work-tape equality — definitions

`TM.binaryEqTM` compares two canonical binary strings and writes the Boolean
result on a third work tape. Unlike the legacy output-oriented comparator, it
preserves the public output tape and every unrelated work tape.
-/


@[expose] public section

namespace Complexity

namespace TM

/-- The binary comparator scans until the first mismatch or simultaneous
termination, then halts immediately. -/
inductive BinaryEqPhase where
  | scan
  | done
  deriving DecidableEq

instance : Fintype BinaryEqPhase where
  elems := {.scan, .done}
  complete := fun state => by cases state <;> simp

/-- Pairwise distinct work tapes used by `binaryEqTM`. -/
structure BinaryEqDistinct {n : ℕ} (lhsIdx rhsIdx resultIdx : Fin n) : Prop where
  lhs_rhs : lhsIdx ≠ rhsIdx
  lhs_result : lhsIdx ≠ resultIdx
  rhs_result : rhsIdx ≠ resultIdx

/-- Compare canonical binary strings on `lhsIdx` and `rhsIdx`, writing one to
`resultIdx` exactly when they agree. The compared heads advance together over
matching bits; all tape contents are preserved except the single result cell. -/
def binaryEqTM {n : ℕ} (lhsIdx rhsIdx resultIdx : Fin n) : TM n where
  Q := BinaryEqPhase
  qstart := .scan
  qhalt := .done
  δ := fun state iHead wHeads oHead =>
    match state with
    | .scan =>
      if wHeads lhsIdx = Γ.blank ∧ wHeads rhsIdx = Γ.blank then
        (.done,
          fun i => if i = resultIdx then Γw.one else readBackWrite (wHeads i),
          readBackWrite oHead,
          idleDir iHead,
          fun i => if i = resultIdx then Dir3.right else idleDir (wHeads i),
          idleDir oHead)
      else if wHeads lhsIdx = wHeads rhsIdx then
        (.scan, fun i => readBackWrite (wHeads i), readBackWrite oHead,
          idleDir iHead,
          fun i => if i = lhsIdx then Dir3.right
            else if i = rhsIdx then Dir3.right else idleDir (wHeads i),
          idleDir oHead)
      else
        (.done,
          fun i => if i = resultIdx then Γw.zero else readBackWrite (wHeads i),
          readBackWrite oHead,
          idleDir iHead,
          fun i => if i = resultIdx then Dir3.right else idleDir (wHeads i),
          idleDir oHead)
    | .done => allIdle .done iHead wHeads oHead
  δ_right_of_start := by
    intro state iHead wHeads oHead
    cases state with
    | scan =>
        dsimp only []
        split
        · refine ⟨idleDir_right_of_start, ?_, idleDir_right_of_start⟩
          intro i hstart
          simp only
          split
          · rfl
          · exact idleDir_right_of_start hstart
        · split
          · refine ⟨idleDir_right_of_start, ?_, idleDir_right_of_start⟩
            intro i hstart
            simp only
            split
            · rfl
            · split
              · rfl
              · exact idleDir_right_of_start hstart
          · refine ⟨idleDir_right_of_start, ?_, idleDir_right_of_start⟩
            intro i hstart
            simp only
            split
            · rfl
            · exact idleDir_right_of_start hstart
    | done => exact rightOfStart_allIdle iHead wHeads oHead

/-- Linear scan bound for binary equality. -/
def binaryEqTime (lhs rhs : List Bool) : ℕ :=
  max lhs.length rhs.length + 1

end TM

end Complexity
