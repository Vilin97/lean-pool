/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Mathlib.NatBits
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.BinaryRippleSub.Defs
public import Mathlib.Algebra.Order.Ring.Nat
public import Std.Tactic.BVDecide.Normalize.Bool

/-!
# Linear-time canonical binary subtraction -- pure proofs

The raw scan is verified through the standard full-subtractor invariant. Its
final borrow decides underflow, while trimming is proved to recover the
canonical `Nat.bits` representation of the raw fixed-width value.
-/


@[expose] public section

namespace Complexity

namespace BinaryRippleSub

/-- Interpret a Boolean bit as a natural number. -/
def boolValue (bit : Bool) : ℕ :=
  if bit then 1 else 0

private theorem fullSub_value (borrow lhs rhs : Bool) :
    boolValue lhs + 2 * boolValue (borrowBit borrow lhs rhs) =
      boolValue rhs + boolValue borrow + boolValue (diffBit borrow lhs rhs) := by
  cases borrow <;> cases lhs <;> cases rhs <;>
    simp [boolValue, borrowBit, diffBit]

private theorem scan_value_step
    (borrow lhsBit rhsBit tailBorrow : Bool)
    (lhs rhs tailValue width : ℕ)
    (htail : lhs + (if tailBorrow then 2 ^ width else 0) =
      rhs + boolValue (borrowBit borrow lhsBit rhsBit) + tailValue) :
    (boolValue lhsBit + 2 * lhs) +
        (if tailBorrow then 2 ^ (width + 1) else 0) =
      (boolValue rhsBit + 2 * rhs) + boolValue borrow +
        (boolValue (diffBit borrow lhsBit rhsBit) + 2 * tailValue) := by
  cases borrow <;> cases lhsBit <;> cases rhsBit <;> cases tailBorrow <;>
    simp [boolValue, borrowBit, diffBit, pow_succ] at htail ⊢ <;> omega

/-- The raw borrow scan writes exactly the larger input width. -/
theorem scan_bits_length_internal (borrow : Bool) (lhs rhs : List Bool) :
    (scan borrow lhs rhs).bits.length = max lhs.length rhs.length := by
  induction lhs generalizing rhs borrow with
  | nil =>
      induction rhs generalizing borrow with
      | nil => simp [scan]
      | cons rhsBit rhsTail ih => simp [scan, ih]
  | cons lhsBit lhsTail ih =>
      cases rhs with
      | nil => simp [scan, ih]
      | cons rhsBit rhsTail => simp [scan, ih]

/-- Arithmetic invariant for the fixed-width borrow scan. The final borrow is
the coefficient of the width-sized wraparound term. -/
theorem scan_value_internal (borrow : Bool) (lhs rhs : List Bool) :
    Nat.fromBitsLE lhs +
        (if (scan borrow lhs rhs).borrow then
          2 ^ max lhs.length rhs.length else 0) =
      Nat.fromBitsLE rhs + boolValue borrow +
        Nat.fromBitsLE (scan borrow lhs rhs).bits := by
  induction lhs generalizing rhs borrow with
  | nil =>
      induction rhs generalizing borrow with
      | nil =>
          cases borrow <;> simp [scan, boolValue, Nat.fromBitsLE, Nat.fromBits]
      | cons rhsBit rhsTail ih =>
          let nextBorrow := borrowBit borrow false rhsBit
          let tail := scan nextBorrow [] rhsTail
          have htail : 0 + (if tail.borrow then 2 ^ rhsTail.length else 0) =
              Nat.fromBitsLE rhsTail + boolValue nextBorrow +
                Nat.fromBitsLE tail.bits := by
            simpa [tail, nextBorrow, Nat.fromBitsLE, Nat.fromBits] using
              ih nextBorrow
          have hstep := scan_value_step borrow false rhsBit tail.borrow 0
            (Nat.fromBitsLE rhsTail) (Nat.fromBitsLE tail.bits)
            rhsTail.length htail
          simpa [scan, tail, nextBorrow, Nat.fromBitsLE_cons] using! hstep
  | cons lhsBit lhsTail ih =>
      cases rhs with
      | nil =>
          let nextBorrow := borrowBit borrow lhsBit false
          let tail := scan nextBorrow lhsTail []
          have htail : Nat.fromBitsLE lhsTail +
              (if tail.borrow then 2 ^ lhsTail.length else 0) =
              0 + boolValue nextBorrow + Nat.fromBitsLE tail.bits := by
            simpa [tail, nextBorrow, Nat.fromBitsLE, Nat.fromBits] using
              ih nextBorrow []
          have hstep := scan_value_step borrow lhsBit false tail.borrow
            (Nat.fromBitsLE lhsTail) 0 (Nat.fromBitsLE tail.bits)
            lhsTail.length htail
          simpa [scan, tail, nextBorrow, Nat.fromBitsLE_cons] using! hstep
      | cons rhsBit rhsTail =>
          let nextBorrow := borrowBit borrow lhsBit rhsBit
          let tail := scan nextBorrow lhsTail rhsTail
          have htail : Nat.fromBitsLE lhsTail +
              (if tail.borrow then
                2 ^ max lhsTail.length rhsTail.length else 0) =
              Nat.fromBitsLE rhsTail + boolValue nextBorrow +
                Nat.fromBitsLE tail.bits := by
            simpa [tail, nextBorrow] using ih nextBorrow rhsTail
          have hstep := scan_value_step borrow lhsBit rhsBit tail.borrow
            (Nat.fromBitsLE lhsTail) (Nat.fromBitsLE rhsTail)
            (Nat.fromBitsLE tail.bits) (max lhsTail.length rhsTail.length) htail
          simpa [scan, tail, nextBorrow, Nat.fromBitsLE_cons] using! hstep

/-- Appending a redundant high zero does not change canonical trimming. -/
theorem trimHighZeros_append_false_internal (bits : List Bool) :
    trimHighZeros (bits ++ [false]) = trimHighZeros bits := by
  induction bits with
  | nil => simp [trimHighZeros]
  | cons bit rest ih =>
      rw [List.cons_append, trimHighZeros, ih]
      cases rest <;> rfl

/-- A high one makes the entire lower prefix significant. -/
theorem trimHighZeros_append_true_internal (bits : List Bool) :
    trimHighZeros (bits ++ [true]) = bits ++ [true] := by
  induction bits with
  | nil => simp [trimHighZeros]
  | cons bit rest ih =>
      rw [List.cons_append, trimHighZeros, ih]
      cases rest <;> rfl

/-- Trimming arbitrary little-endian bits produces the canonical bits of their
decoded natural value. -/
theorem trimHighZeros_eq_natBits_internal (bits : List Bool) :
    trimHighZeros bits = (Nat.fromBitsLE bits).bits := by
  induction bits with
  | nil => simp [trimHighZeros, Nat.fromBitsLE, Nat.fromBits]
  | cons bit rest ih =>
      rw [Nat.fromBitsLE_cons]
      simp only [trimHighZeros, ih]
      by_cases hrest : Nat.fromBitsLE rest = 0
      · rw [hrest]
        cases bit <;> simp
      · have hbits : (Nat.fromBitsLE rest).bits ≠ [] := by
          intro hnil
          have hsize : (Nat.fromBitsLE rest).size = 0 := by
            rw [← Nat.size_eq_bits_len, hnil]
            rfl
          exact hrest (Nat.size_eq_zero.mp hsize)
        have hvalue : (if bit then 1 else 0) + 2 * Nat.fromBitsLE rest =
            Nat.bit bit (Nat.fromBitsLE rest) := by
          cases bit
          · simp [Nat.bit]
          · simp [Nat.bit, Nat.add_comm]
        rw [hvalue, Nat.bits_append_bit _ bit (fun h => (hrest h).elim)]
        cases htail : (Nat.fromBitsLE rest).bits with
        | nil => exact (hbits htail).elim
        | cons high tail => rfl

/-- The canonical pure subtraction result agrees with natural-number monus. -/
theorem subtract_natBits_internal (lhs rhs : ℕ) :
    subtract lhs.bits rhs.bits = (lhs - rhs).bits := by
  let raw := scan false lhs.bits rhs.bits
  have hinvariant := scan_value_internal false lhs.bits rhs.bits
  have hlength := scan_bits_length_internal false lhs.bits rhs.bits
  have hrawBound := Nat.fromBitsLE_lt_pow_length raw.bits
  have hlength' : raw.bits.length = max lhs.size rhs.size := by
    simpa [raw, Nat.size_eq_bits_len] using hlength
  have hinvariant' : lhs +
        (if raw.borrow then 2 ^ max lhs.size rhs.size else 0) =
      rhs + Nat.fromBitsLE raw.bits := by
    simpa [raw, Nat.fromBitsLE_bits, Nat.size_eq_bits_len] using! hinvariant
  have hrawBound' : Nat.fromBitsLE raw.bits < 2 ^ max lhs.size rhs.size := by
    rw [hlength'] at hrawBound
    exact hrawBound
  change (if raw.borrow then [] else trimHighZeros raw.bits) = (lhs - rhs).bits
  cases hborrow : raw.borrow with
  | false =>
      simp only [Bool.false_eq_true, ite_false]
      rw [trimHighZeros_eq_natBits_internal]
      have hvalue : Nat.fromBitsLE raw.bits = lhs - rhs := by
        simp [hborrow] at hinvariant'
        omega
      rw [hvalue]
  | true =>
      simp only [if_true]
      have hlt : lhs < rhs := by
        simp [hborrow] at hinvariant'
        omega
      rw [Nat.sub_eq_zero_of_le (Nat.le_of_lt hlt), Nat.zero_bits]

/-- Canonical subtraction has exactly the width of natural-number monus. -/
theorem length_subtract_natBits_internal (lhs rhs : ℕ) :
    (subtract lhs.bits rhs.bits).length = (lhs - rhs).size := by
  rw [subtract_natBits_internal, Nat.size_eq_bits_len]

end BinaryRippleSub

namespace TM

/-- The scan bound on canonical operands is the larger natural-number width. -/
theorem binaryRippleSubScanTime_natBits_internal (lhs rhs : ℕ) :
    binaryRippleSubScanTime lhs.bits rhs.bits = max lhs.size rhs.size + 1 := by
  simp [binaryRippleSubScanTime, Nat.size_eq_bits_len]

/-- The cleanup bound equals the scan bound on canonical operands. -/
theorem binaryRippleSubCleanupTime_natBits_internal (lhs rhs : ℕ) :
    binaryRippleSubCleanupTime lhs.bits rhs.bits = max lhs.size rhs.size + 1 := by
  simp [binaryRippleSubCleanupTime, Nat.size_eq_bits_len]

/-- The core bound is twice the larger width plus its two turning steps. -/
theorem binaryRippleSubCoreTime_natBits_internal (lhs rhs : ℕ) :
    binaryRippleSubCoreTime lhs.bits rhs.bits =
      2 * max lhs.size rhs.size + 2 := by
  simp [binaryRippleSubCoreTime, Nat.size_eq_bits_len]

/-- The complete subtractor is linear in the sum of the operand widths. -/
theorem binaryRippleSubTime_le_internal (lhs rhs : ℕ) :
    binaryRippleSubTime lhs rhs ≤ 3 * (lhs.size + rhs.size) + 10 := by
  simp only [binaryRippleSubTime]
  have hmax : max lhs.size rhs.size ≤ lhs.size + rhs.size :=
    max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)
  omega

end TM

end Complexity
