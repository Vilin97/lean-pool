/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines
public import Mathlib.Data.Nat.Bits

/-!
# Linear-time canonical binary subtraction -- definitions

This module defines a full-borrow scan over two preserved little-endian binary
work tapes. The scan writes a fixed-width difference to a fresh result tape.
A single backward pass then erases the complete result on underflow or removes
only its redundant high zeros, while returning the result head to cell one.
-/


@[expose] public section

namespace Complexity

namespace BinaryRippleSub

/-- The low output bit of one binary-subtraction column. -/
def diffBit (borrow lhs rhs : Bool) : Bool :=
  (lhs.xor rhs).xor borrow

/-- The outgoing borrow of one binary-subtraction column. -/
def borrowBit (borrow lhs rhs : Bool) : Bool :=
  (!lhs && rhs) || (!lhs && borrow) || (rhs && borrow)

/-- Raw fixed-width output of a borrow scan. -/
structure ScanResult where
  /-- Little-endian difference bits produced so far. -/
  bits : List Bool
  /-- Borrow propagated beyond the most-significant scanned column. -/
  borrow : Bool
  deriving DecidableEq

/-- Scan two little-endian bit strings with an incoming borrow. A missing side
is padded by zero; the final borrow is retained separately from the raw bits. -/
def scan : Bool → List Bool → List Bool → ScanResult
  | borrow, [], [] => ⟨[], borrow⟩
  | borrow, lhs :: lhsTail, [] =>
      let tail := scan (borrowBit borrow lhs false) lhsTail []
      ⟨diffBit borrow lhs false :: tail.bits, tail.borrow⟩
  | borrow, [], rhs :: rhsTail =>
      let tail := scan (borrowBit borrow false rhs) [] rhsTail
      ⟨diffBit borrow false rhs :: tail.bits, tail.borrow⟩
  | borrow, lhs :: lhsTail, rhs :: rhsTail =>
      let tail := scan (borrowBit borrow lhs rhs) lhsTail rhsTail
      ⟨diffBit borrow lhs rhs :: tail.bits, tail.borrow⟩

/-- Remove redundant most-significant zeros from a little-endian bit string. -/
def trimHighZeros : List Bool → List Bool
  | [] => []
  | bit :: rest =>
      match trimHighZeros rest with
      | [] => if bit then [true] else []
      | high :: tail => bit :: high :: tail

/-- Canonical truncated subtraction semantics on arbitrary little-endian bit
strings. Underflow is represented by canonical zero. -/
def subtract (lhs rhs : List Bool) : List Bool :=
  let raw := scan false lhs rhs
  if raw.borrow then [] else trimHighZeros raw.bits

end BinaryRippleSub

namespace TM

/-- Forward-borrow states, backward cleanup states, and the unique halt state. -/
inductive BinaryRippleSubPhase where
  | scan (borrow : Bool)
  | erase
  | trim (seenOne : Bool)
  | done
  deriving DecidableEq

/-- `BinaryRippleSubPhase` is finite, as required by the concrete TM model. -/
instance instFintypeBinaryRippleSubPhase : Fintype BinaryRippleSubPhase where
  elems := {.scan false, .scan true, .erase, .trim false, .trim true, .done}
  complete := by
    intro phase
    cases phase with
    | scan borrow => cases borrow <;> simp
    | erase => simp
    | trim seenOne => cases seenOne <;> simp
    | done => simp

/-- Pairwise distinct work tapes owned by the ripple-borrow subtractor. -/
structure BinaryRippleSubDistinct {n : ℕ}
    (lhsIdx rhsIdx resultIdx : Fin n) : Prop where
  lhs_rhs : lhsIdx ≠ rhsIdx
  lhs_result : lhsIdx ≠ resultIdx
  rhs_result : rhsIdx ≠ resultIdx

/-- Scan two canonical operands, write their fixed-width raw difference, and
canonicalize the result while moving backward. A final borrow erases the whole
result; otherwise high zeros are erased until the first high one is seen. -/
def binaryRippleSubCoreTM {n : ℕ}
    (lhsIdx rhsIdx resultIdx : Fin n) : TM n where
  Q := BinaryRippleSubPhase
  qstart := .scan false
  qhalt := .done
  δ := fun state iHead wHeads oHead =>
    match state with
    | .scan borrow =>
        if wHeads lhsIdx = Γ.blank ∧ wHeads rhsIdx = Γ.blank then
          (if borrow then .erase else .trim false,
            fun i => readBackWrite (wHeads i), readBackWrite oHead,
            idleDir iHead,
            fun i => if i = resultIdx then moveLeftDir (wHeads resultIdx)
              else idleDir (wHeads i),
            idleDir oHead)
        else
          let lhsBit := decide (wHeads lhsIdx = Γ.one)
          let rhsBit := decide (wHeads rhsIdx = Γ.one)
          let diff := BinaryRippleSub.diffBit borrow lhsBit rhsBit
          let nextBorrow := BinaryRippleSub.borrowBit borrow lhsBit rhsBit
          (.scan nextBorrow,
            fun i => if i = resultIdx then Γw.ofBool diff
              else readBackWrite (wHeads i),
            readBackWrite oHead,
            idleDir iHead,
            fun i =>
              if i = resultIdx then Dir3.right
              else if i = lhsIdx then
                if wHeads lhsIdx = Γ.blank then Dir3.stay else Dir3.right
              else if i = rhsIdx then
                if wHeads rhsIdx = Γ.blank then Dir3.stay else Dir3.right
              else idleDir (wHeads i),
            idleDir oHead)
    | .erase =>
        if wHeads resultIdx = Γ.start then
          (.done, fun i => readBackWrite (wHeads i), readBackWrite oHead,
            idleDir iHead,
            fun i => if i = resultIdx then Dir3.right else idleDir (wHeads i),
            idleDir oHead)
        else
          (.erase,
            fun i => if i = resultIdx then Γw.blank
              else readBackWrite (wHeads i),
            readBackWrite oHead,
            idleDir iHead,
            fun i => if i = resultIdx then moveLeftDir (wHeads resultIdx)
              else idleDir (wHeads i),
            idleDir oHead)
    | .trim seenOne =>
        if wHeads resultIdx = Γ.start then
          (.done, fun i => readBackWrite (wHeads i), readBackWrite oHead,
            idleDir iHead,
            fun i => if i = resultIdx then Dir3.right else idleDir (wHeads i),
            idleDir oHead)
        else if seenOne ∨ wHeads resultIdx = Γ.one then
          (.trim true, fun i => readBackWrite (wHeads i), readBackWrite oHead,
            idleDir iHead,
            fun i => if i = resultIdx then moveLeftDir (wHeads resultIdx)
              else idleDir (wHeads i),
            idleDir oHead)
        else
          (.trim false,
            fun i => if i = resultIdx then Γw.blank
              else readBackWrite (wHeads i),
            readBackWrite oHead,
            idleDir iHead,
            fun i => if i = resultIdx then moveLeftDir (wHeads resultIdx)
              else idleDir (wHeads i),
            idleDir oHead)
    | .done => allIdle .done iHead wHeads oHead
  δ_right_of_start := by
    intro state iHead wHeads oHead
    cases state with
    | scan borrow =>
        dsimp only
        split
        · refine ⟨idleDir_right_of_start, ?_, idleDir_right_of_start⟩
          intro i hi
          simp only
          by_cases hresult : i = resultIdx
          · subst i
            rw [if_pos rfl]
            exact moveLeftDir_right_of_start hi
          · rw [if_neg hresult]
            exact idleDir_right_of_start hi
        · refine ⟨idleDir_right_of_start, ?_, idleDir_right_of_start⟩
          intro i hi
          dsimp only
          by_cases hresult : i = resultIdx
          · rw [if_pos hresult]
          · rw [if_neg hresult]
            by_cases hlhs : i = lhsIdx
            · rw [if_pos hlhs]
              subst i
              simp [hi]
            · rw [if_neg hlhs]
              by_cases hrhs : i = rhsIdx
              · rw [if_pos hrhs]
                subst i
                simp [hi]
              · rw [if_neg hrhs]
                exact idleDir_right_of_start hi
    | erase =>
        dsimp only
        split
        · refine ⟨idleDir_right_of_start, ?_, idleDir_right_of_start⟩
          intro i hi
          simp only
          by_cases hresult : i = resultIdx
          · rw [if_pos hresult]
          · rw [if_neg hresult]
            exact idleDir_right_of_start hi
        · rename_i hnotStart
          refine ⟨idleDir_right_of_start, ?_, idleDir_right_of_start⟩
          intro i hi
          simp only
          by_cases hresult : i = resultIdx
          · subst i
            rw [if_pos rfl]
            exact moveLeftDir_right_of_start hi
          · rw [if_neg hresult]
            exact idleDir_right_of_start hi
    | trim seenOne =>
        dsimp only
        split
        · refine ⟨idleDir_right_of_start, ?_, idleDir_right_of_start⟩
          intro i hi
          simp only
          by_cases hresult : i = resultIdx
          · rw [if_pos hresult]
          · rw [if_neg hresult]
            exact idleDir_right_of_start hi
        · rename_i hnotStart
          split <;>
            refine ⟨idleDir_right_of_start, ?_, idleDir_right_of_start⟩
          all_goals
            intro i hi
            simp only
            by_cases hresult : i = resultIdx
            · subst i
              rw [if_pos rfl]
              exact moveLeftDir_right_of_start hi
            · rw [if_neg hresult]
              exact idleDir_right_of_start hi
    | done => exact rightOfStart_allIdle iHead wHeads oHead

/-- Forward scan time, including the simultaneous-blank turn. -/
def binaryRippleSubScanTime (lhs rhs : List Bool) : ℕ :=
  max lhs.length rhs.length + 1

/-- Backward cleanup time, including the final marker bounce. -/
def binaryRippleSubCleanupTime (lhs rhs : List Bool) : ℕ :=
  max lhs.length rhs.length + 1

/-- Exact time of the forward scan followed by backward canonicalization. -/
def binaryRippleSubCoreTime (lhs rhs : List Bool) : ℕ :=
  2 * max lhs.length rhs.length + 2

/-- Canonical subtraction followed by rewinds of the two preserved operands. -/
def binaryRippleSubTM {n : ℕ}
    (lhsIdx rhsIdx resultIdx : Fin n) : TM n :=
  seqTM (binaryRippleSubCoreTM lhsIdx rhsIdx resultIdx)
    (seqTM (rewindWorkTM lhsIdx) (rewindWorkTM rhsIdx))

/-- Width-linear time bound for the core, two rewinds, and two seams. -/
def binaryRippleSubTime (lhs rhs : ℕ) : ℕ :=
  2 * max lhs.size rhs.size + lhs.size + rhs.size + 10

end TM

end Complexity
