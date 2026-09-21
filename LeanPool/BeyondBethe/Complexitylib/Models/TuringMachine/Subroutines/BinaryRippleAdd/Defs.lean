/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines
public import Mathlib.Data.Nat.Bits

/-!
# Linear-time canonical binary addition -- definitions

This module defines a finite-state ripple-carry scan over two preserved
little-endian binary work tapes. Each scan step appends one sum bit to a fresh
result tape. A composed wrapper then rewinds all three owned tapes.
-/


@[expose] public section

namespace Complexity

namespace BinaryRippleAdd

/-- The output bit of a one-column binary addition with incoming carry. -/
def sumBit (carry lhs rhs : Bool) : Bool :=
  (lhs.xor rhs).xor carry

/-- The outgoing carry of a one-column binary addition. -/
def carryBit (carry lhs rhs : Bool) : Bool :=
  (lhs && rhs) || (carry && lhs) || (carry && rhs)

/-- Ripple-carry addition on little-endian bit strings, padding a missing side
with zero and emitting a final high bit exactly when the carry remains set. -/
def ripple : Bool → List Bool → List Bool → List Bool
  | false, [], [] => []
  | true, [], [] => [true]
  | carry, lhs :: lhsTail, [] =>
      sumBit carry lhs false :: ripple (carryBit carry lhs false) lhsTail []
  | carry, [], rhs :: rhsTail =>
      sumBit carry false rhs :: ripple (carryBit carry false rhs) [] rhsTail
  | carry, lhs :: lhsTail, rhs :: rhsTail =>
      sumBit carry lhs rhs :: ripple (carryBit carry lhs rhs) lhsTail rhsTail

end BinaryRippleAdd

namespace TM

/-- Carry-bearing scan states followed by the unique halt state. -/
inductive BinaryRippleAddPhase where
  | scan (carry : Bool)
  | done
  deriving DecidableEq

/-- `BinaryRippleAddPhase` is finite, as required by the concrete machine model. -/
instance instFintypeBinaryRippleAddPhase : Fintype BinaryRippleAddPhase where
  elems := {.scan false, .scan true, .done}
  complete := by
    intro phase
    cases phase with
    | scan carry => cases carry <;> simp
    | done => simp

/-- Pairwise distinct work tapes used by the ripple-carry adder. -/
structure BinaryRippleAddDistinct {n : ℕ}
    (lhsIdx rhsIdx resultIdx : Fin n) : Prop where
  lhs_rhs : lhsIdx ≠ rhsIdx
  lhs_result : lhsIdx ≠ resultIdx
  rhs_result : rhsIdx ≠ resultIdx

/-- Scan two canonical little-endian operands and append their sum to a fresh
result tape. Operand cells are written back unchanged. An exhausted operand
stays on its first blank while the longer operand continues to advance. -/
def binaryRippleAddScanTM {n : ℕ}
    (lhsIdx rhsIdx resultIdx : Fin n) : TM n where
  Q := BinaryRippleAddPhase
  qstart := .scan false
  qhalt := .done
  δ := fun state iHead wHeads oHead =>
    match state with
    | .scan carry =>
        if wHeads lhsIdx = Γ.blank ∧ wHeads rhsIdx = Γ.blank then
          if carry then
            (.done,
              fun i => if i = resultIdx then Γw.one else readBackWrite (wHeads i),
              readBackWrite oHead,
              idleDir iHead,
              fun i => if i = resultIdx then Dir3.right else idleDir (wHeads i),
              idleDir oHead)
          else
            allReadBack .done iHead wHeads oHead
        else
          let lhsBit := decide (wHeads lhsIdx = Γ.one)
          let rhsBit := decide (wHeads rhsIdx = Γ.one)
          let sum := BinaryRippleAdd.sumBit carry lhsBit rhsBit
          let nextCarry := BinaryRippleAdd.carryBit carry lhsBit rhsBit
          (.scan nextCarry,
            fun i => if i = resultIdx then Γw.ofBool sum else readBackWrite (wHeads i),
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
    | .done => allIdle .done iHead wHeads oHead
  δ_right_of_start := by
    intro state iHead wHeads oHead
    cases state with
    | scan carry =>
        dsimp only
        split
        · split
          · refine ⟨idleDir_right_of_start, ?_, idleDir_right_of_start⟩
            intro i hi
            dsimp only
            by_cases hresult : i = resultIdx
            · rw [if_pos hresult]
            · rw [if_neg hresult]
              exact idleDir_right_of_start hi
          · exact rightOfStart_allReadBack iHead wHeads oHead
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
    | done => exact rightOfStart_allIdle iHead wHeads oHead

/-- Exact number of scan transitions, including the final simultaneous-blank
transition. -/
def binaryRippleAddScanTime (lhs rhs : List Bool) : ℕ :=
  max lhs.length rhs.length + 1

/-- Scan the operands into a fresh result and then rewind both operands and the
result to cell one. -/
def binaryRippleAddTM {n : ℕ}
    (lhsIdx rhsIdx resultIdx : Fin n) : TM n :=
  seqTM (binaryRippleAddScanTM lhsIdx rhsIdx resultIdx)
    (seqTM (rewindWorkTM lhsIdx)
      (seqTM (rewindWorkTM rhsIdx) (rewindWorkTM resultIdx)))

/-- Linear width bound for the scan, three rewinds, and three composition seams. -/
def binaryRippleAddTime (lhs rhs : ℕ) : ℕ :=
  max lhs.size rhs.size + lhs.size + rhs.size + (lhs + rhs).size + 13

end TM

end Complexity
