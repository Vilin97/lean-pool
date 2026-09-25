/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.BinaryShiftMul.Defs
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Tactic.Ring.RingNF

/-!
# Width-driven binary shift-and-add multiplication -- pure proofs

This file proves the generalized arithmetic invariant of the little-endian
shift-and-add fold, its multiplication specialization, and width bounds for
every partial accumulator and shifted multiplicand.
-/


@[expose] public section

namespace Complexity

namespace BinaryShiftMul

/-- The generalized shift-and-add fold accumulates `shift` times the decoded
bit string and doubles `shift` once per consumed bit. -/
theorem fold_eq_internal (bits : List Bool) (acc shift : ℕ) :
    fold bits acc shift =
      (acc + shift * Nat.fromBitsLE bits, shift * 2 ^ bits.length) := by
  induction bits generalizing acc shift with
  | nil => simp [fold, Nat.fromBitsLE, Nat.fromBits]
  | cons bit bits ih =>
      cases bit <;>
        simp [fold, step, ih, Nat.fromBitsLE_cons, pow_succ,
          Prod.ext_iff] <;>
        constructor <;> ring

/-- Taking a low-order prefix cannot increase its little-endian decoded
value. -/
theorem fromBitsLE_take_le_internal (bits : List Bool) (i : ℕ) :
    Nat.fromBitsLE (bits.take i) ≤ Nat.fromBitsLE bits := by
  induction bits generalizing i with
  | nil => simp [Nat.fromBitsLE]
  | cons bit bits ih =>
      cases i with
      | zero =>
          simp only [List.take_zero]
          exact Nat.zero_le _
      | succ i =>
          rw [List.take_succ_cons, Nat.fromBitsLE_cons,
            Nat.fromBitsLE_cons]
          exact Nat.add_le_add_left (Nat.mul_le_mul_left 2 (ih i)) _

/-- If the iteration index is within the canonical multiplier width, folding
its prefix produces the advertised partial accumulator and shift. -/
theorem fold_take_eq_internal (lhs rhs i : ℕ) (hi : i ≤ rhs.size) :
    fold (rhs.bits.take i) 0 lhs =
      (partialAcc lhs rhs i, partialShift lhs i) := by
  rw [fold_eq_internal]
  simp [partialAcc, partialShift, List.length_take, Nat.size_eq_bits_len,
    min_eq_left hi]

private theorem fold_append (xs ys : List Bool) (acc shift : ℕ) :
    fold (xs ++ ys) acc shift =
      let middle := fold xs acc shift
      fold ys middle.1 middle.2 := by
  induction xs generalizing acc shift with
  | nil => rfl
  | cons bit xs ih =>
      simp only [List.cons_append, fold]
      rw [ih]

/-- One live multiplier bit advances the partial arithmetic invariant by one
iteration. -/
theorem step_partial_internal (lhs rhs i : ℕ) (hi : i < rhs.size) :
    step (rhs.bits.get ⟨i, by simpa [Nat.size_eq_bits_len] using hi⟩)
        (partialAcc lhs rhs i) (partialShift lhs i) =
      (partialAcc lhs rhs (i + 1), partialShift lhs (i + 1)) := by
  have hcurrent := fold_take_eq_internal lhs rhs i (Nat.le_of_lt hi)
  have hnext := fold_take_eq_internal lhs rhs (i + 1) (by omega)
  rw [List.take_succ_eq_append_getElem (by
    simpa [Nat.size_eq_bits_len] using hi), fold_append, hcurrent] at hnext
  simpa [fold] using hnext

/-- Folding all canonical multiplier bits computes multiplication and leaves
the shift advanced by the multiplier width. -/
theorem fold_natBits_internal (lhs rhs : ℕ) :
    fold rhs.bits 0 lhs = (lhs * rhs, lhs * 2 ^ rhs.size) := by
  rw [fold_eq_internal, Nat.fromBitsLE_bits, Nat.size_eq_bits_len]
  simp

/-- The complete partial accumulator is the product. -/
theorem partialAcc_full_internal (lhs rhs : ℕ) :
    partialAcc lhs rhs rhs.size = lhs * rhs := by
  unfold partialAcc
  rw [← Nat.size_eq_bits_len, List.take_length, Nat.fromBitsLE_bits]

/-- The complete partial shift has advanced by the multiplier width. -/
theorem partialShift_full_internal (lhs rhs : ℕ) :
    partialShift lhs rhs.size = lhs * 2 ^ rhs.size := by
  rfl

/-- The accumulator component of the complete pure fold is the product. -/
theorem fold_natBits_fst_internal (lhs rhs : ℕ) :
    (fold rhs.bits 0 lhs).1 = lhs * rhs := by
  rw [fold_natBits_internal]

/-- Every partial accumulator is bounded by the complete product. -/
theorem partialAcc_le_mul_internal (lhs rhs i : ℕ) :
    partialAcc lhs rhs i ≤ lhs * rhs := by
  unfold partialAcc
  simpa only [Nat.fromBitsLE_bits] using
    Nat.mul_le_mul_left lhs (fromBitsLE_take_le_internal rhs.bits i)

/-- Binary width is subadditive under multiplication. -/
theorem size_mul_le_add_internal (lhs rhs : ℕ) :
    (lhs * rhs).size ≤ lhs.size + rhs.size := by
  by_cases hrhs : rhs = 0
  · simp [hrhs]
  rw [Nat.size_le]
  calc
    lhs * rhs < 2 ^ lhs.size * rhs :=
      Nat.mul_lt_mul_of_pos_right (Nat.lt_size_self lhs) (Nat.pos_of_ne_zero hrhs)
    _ < 2 ^ lhs.size * 2 ^ rhs.size :=
      Nat.mul_lt_mul_of_pos_left (Nat.lt_size_self rhs) (Nat.two_pow_pos _)
    _ = 2 ^ (lhs.size + rhs.size) := by rw [pow_add]

/-- Every partial accumulator fits in the combined input width. -/
theorem partialAcc_size_le_width_internal (lhs rhs i : ℕ) :
    (partialAcc lhs rhs i).size ≤ lhs.size + rhs.size := by
  exact le_trans (Nat.size_le_size (partialAcc_le_mul_internal lhs rhs i))
    (size_mul_le_add_internal lhs rhs)

/-- Shifting left by `i` grows binary width by at most `i`. -/
theorem partialShift_size_le_internal (lhs i : ℕ) :
    (partialShift lhs i).size ≤ lhs.size + i := by
  by_cases hlhs : lhs = 0
  · simp [partialShift, hlhs]
  rw [partialShift, ← Nat.shiftLeft_eq_mul_pow, Nat.size_shiftLeft hlhs]

/-- At any live multiplier iteration, both arithmetic values fit in the
combined input width. -/
theorem partial_widths_le_internal (lhs rhs i : ℕ) (hi : i ≤ rhs.size) :
    (partialAcc lhs rhs i).size ≤ lhs.size + rhs.size ∧
      (partialShift lhs i).size ≤ lhs.size + rhs.size := by
  exact ⟨partialAcc_size_le_width_internal lhs rhs i,
    le_trans (partialShift_size_le_internal lhs i)
      (Nat.add_le_add_left hi lhs.size)⟩

end BinaryShiftMul

end Complexity
