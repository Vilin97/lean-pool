/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.RawRational
import LeanPool.BeyondBethe.BeyondBethe.RationalEncodingBounds
import Mathlib.Tactic

/-! # Raw Rational Bit Bounds -/

namespace BeyondBethe

/-!
# Bit growth of the explicit unreduced rational arithmetic

`RawRat` deliberately does not hide normalization inside field operations.
This file proves the elementary size bounds needed by the eventual machine
simulation.  The common width counts the larger of the signed numerator's
absolute-value width and the positive denominator's width.
-/

/-- Binary width of an unreduced signed fraction. -/
def rawRatWidth (q : RawRat) : ℕ :=
  max q.num.natAbs.size q.den.size

theorem rawRat_num_size_le_width (q : RawRat) :
    q.num.natAbs.size ≤ rawRatWidth q :=
  le_max_left _ _

theorem rawRat_den_size_le_width (q : RawRat) :
    q.den.size ≤ rawRatWidth q :=
  le_max_right _ _

theorem rawRat_num_lt_two_pow_width (q : RawRat) :
    q.num.natAbs < 2 ^ rawRatWidth q := by
  exact (Nat.lt_size_self q.num.natAbs).trans_le
    (Nat.pow_le_pow_right (by decide) (rawRat_num_size_le_width q))

theorem rawRat_den_lt_two_pow_width (q : RawRat) :
    q.den < 2 ^ rawRatWidth q := by
  exact (Nat.lt_size_self q.den).trans_le
    (Nat.pow_le_pow_right (by decide) (rawRat_den_size_le_width q))

theorem rawRatWidth_zero : rawRatWidth RawRat.zero = 1 := by
  norm_num [rawRatWidth, RawRat.zero]

theorem rawRatWidth_one : rawRatWidth RawRat.one = 1 := by
  norm_num [rawRatWidth, RawRat.one]

theorem rawRatWidth_neg (q : RawRat) :
    rawRatWidth q.neg = rawRatWidth q := by
  simp [rawRatWidth, RawRat.neg]

namespace RawRat

/-- Total reciprocal in the unreduced representation.  The zero branch
agrees with the field convention `0⁻¹ = 0`; nonzero branches swap the
absolute numerator with the denominator and retain the sign. -/
def inv (q : RawRat) : RawRat :=
  match q.num with
  | .ofNat 0 => zero
  | .ofNat (n + 1) => ⟨q.den, n + 1, by omega⟩
  | .negSucc n => ⟨-(q.den : ℤ), n + 1, by omega⟩

@[simp] theorem value_inv (q : RawRat) : q.inv.value = q.value⁻¹ := by
  rcases q with ⟨num, den, hden⟩
  cases num with
  | ofNat n =>
      cases n with
      | zero => simp [inv, value, zero]
      | succ n =>
          simp only [inv, value, Int.cast_ofNat, Nat.cast_add, Nat.cast_one]
          field_simp
          <;> norm_num
          <;> ring
  | negSucc n =>
      simp only [inv, value, Int.cast_negSucc, Nat.cast_add, Nat.cast_one,
        Int.cast_neg, Int.cast_ofNat, inv_div]
      field_simp
      <;> norm_num
      <;> ring

def div (q r : RawRat) : RawRat := q.mul r.inv

@[simp] theorem value_div (q r : RawRat) :
    (q.div r).value = q.value / r.value := by
  simp [div, div_eq_mul_inv]

end RawRat

theorem rawRatWidth_inv_le (q : RawRat) :
    rawRatWidth q.inv ≤ rawRatWidth q := by
  rcases q with ⟨num, den, hden⟩
  cases num with
  | ofNat n =>
      cases n with
      | zero =>
          simp only [RawRat.inv, rawRatWidth_zero]
          have hsize : 1 ≤ den.size := by
            exact Nat.size_pos.mpr hden
          exact hsize.trans (le_max_right _ _)
      | succ n =>
          change max den.size (n + 1).size ≤
            max (Int.ofNat (n + 1)).natAbs.size den.size
          rw [Int.natAbs_ofNat', max_comm]
  | negSucc n =>
      change max (-(den : ℤ)).natAbs.size (n + 1).size ≤
        max (Int.negSucc n).natAbs.size den.size
      simp only [Int.natAbs_neg, Int.natAbs_natCast, Int.natAbs_negSucc]
      rw [max_comm]

private theorem mul_lt_two_pow_add
    {a b u v : ℕ} (ha : a < 2 ^ u) (hb : b < 2 ^ v) :
    a * b < 2 ^ (u + v) := by
  rw [pow_add]
  nlinarith [show 0 < 2 ^ u by positivity,
    show 0 < 2 ^ v by positivity]

private theorem add_of_two_lt_two_pow_lt
    {a b k : ℕ} (ha : a < 2 ^ k) (hb : b < 2 ^ k) :
    a + b < 2 ^ (k + 1) := by
  rw [pow_succ]
  omega

/-- Multiplication adds the operand widths. -/
theorem rawRatWidth_mul_le (q r : RawRat) :
    rawRatWidth (q.mul r) ≤ rawRatWidth q + rawRatWidth r := by
  apply max_le
  · rw [RawRat.mul, Int.natAbs_mul, Nat.size_le]
    exact mul_lt_two_pow_add
      (rawRat_num_lt_two_pow_width q)
      (rawRat_num_lt_two_pow_width r)
  · rw [RawRat.mul, Nat.size_le]
    exact mul_lt_two_pow_add
      (rawRat_den_lt_two_pow_width q)
      (rawRat_den_lt_two_pow_width r)

theorem rawRatWidth_div_le (q r : RawRat) :
    rawRatWidth (q.div r) ≤ rawRatWidth q + rawRatWidth r := by
  exact (rawRatWidth_mul_le q r.inv).trans
    (Nat.add_le_add_left (rawRatWidth_inv_le r) _)

/-- Addition costs at most one carry bit beyond the sum of the operand
widths.  This includes the cross-multiplied denominator representation. -/
theorem rawRatWidth_add_le (q r : RawRat) :
    rawRatWidth (q.add r) ≤ rawRatWidth q + rawRatWidth r + 1 := by
  apply max_le
  · rw [RawRat.add, Nat.size_le]
    apply lt_of_le_of_lt (Int.natAbs_add_le _ _)
    rw [Int.natAbs_mul, Int.natAbs_mul]
    apply add_of_two_lt_two_pow_lt
    · exact mul_lt_two_pow_add
        (rawRat_num_lt_two_pow_width q)
        (rawRat_den_lt_two_pow_width r)
    · have h := mul_lt_two_pow_add
        (rawRat_num_lt_two_pow_width r)
        (rawRat_den_lt_two_pow_width q)
      simpa only [Nat.add_comm] using! h
  · rw [RawRat.add, Nat.size_le]
    exact (mul_lt_two_pow_add
      (rawRat_den_lt_two_pow_width q)
      (rawRat_den_lt_two_pow_width r)).trans_le
        (Nat.pow_le_pow_right (by decide) (by omega))

theorem rawRatWidth_sub_le (q r : RawRat) :
    rawRatWidth (q.sub r) ≤ rawRatWidth q + rawRatWidth r + 1 := by
  simpa only [RawRat.sub, rawRatWidth_neg] using! rawRatWidth_add_le q r.neg

theorem rawRat_value_den_dvd (q : RawRat) : q.value.den ∣ q.den := by
  have hz : (((q.value.den : ℕ) : ℤ) ∣ (q.den : ℤ)) := by
    rw [RawRat.value,
      show ((q.den : ℕ) : ℚ) = ((q.den : ℤ) : ℚ) by norm_num,
      Rat.intCast_div_eq_divInt]
    exact Rat.den_dvd q.num (q.den : ℤ)
  exact_mod_cast hz

theorem rawRat_value_den_le (q : RawRat) : q.value.den ≤ q.den :=
  Nat.le_of_dvd q.den_pos (rawRat_value_den_dvd q)

theorem rawRat_value_abs_le_two_pow_width (q : RawRat) :
    abs q.value ≤ (2 : ℚ) ^ rawRatWidth q := by
  have hden : (1 : ℚ) ≤ q.den := by
    exact_mod_cast q.den_pos
  have hnum : (q.num.natAbs : ℚ) ≤ (2 : ℚ) ^ rawRatWidth q := by
    exact_mod_cast (rawRat_num_lt_two_pow_width q).le
  have habsnum : abs (q.num : ℚ) = (q.num.natAbs : ℚ) := by
    rw [← Int.cast_abs]
    norm_num
  rw [RawRat.value, abs_div, habsnum, abs_of_nonneg (by positivity)]
  exact (div_le_self (by positivity) hden).trans hnum

/-- Canonicalization cannot create a large denominator and its exact
canonical `DataEncode` output has linear length in the unreduced width. -/
theorem binaryNormalizeRawRat_encodedBitLength_le (q : RawRat) :
    encodedBitLength ℚ (binaryNormalizeRawRat q) ≤
      20 + 12 * rawRatWidth q := by
  rw [binaryNormalizeRawRat_eq_value]
  have hden : q.value.den ≤ 2 ^ rawRatWidth q :=
    (rawRat_value_den_le q).trans (rawRat_den_lt_two_pow_width q).le
  have h := rational_encodedBitLength_le_of_abs_and_den_bounds
    (rawRat_value_abs_le_two_pow_width q) hden
  omega

namespace RawRat

/-- Repeated multiplication in the unreduced representation.  This is a
semantic reference for the fixed-budget machine loop; normalization can be
postponed until the end. -/
def pow (q : RawRat) : ℕ → RawRat
  | 0 => one
  | k + 1 => (pow q k).mul q

@[simp] theorem value_pow (q : RawRat) : ∀ k : ℕ,
    (q.pow k).value = q.value ^ k := by
  intro k
  induction k with
  | zero => simp [pow]
  | succ k ih => simp [pow, ih, pow_succ]

/-- A length-`k` product has width at most the sum of the operand widths,
apart from the one-bit representation of the initial value `1`. -/
theorem width_pow_le (q : RawRat) : ∀ k : ℕ,
    rawRatWidth (q.pow k) ≤ 1 + k * rawRatWidth q := by
  intro k
  induction k with
  | zero => simp [pow, rawRatWidth_one]
  | succ k ih =>
      rw [pow]
      exact (rawRatWidth_mul_le _ _).trans (by
        rw [Nat.succ_mul]
        omega)

/-- Unreduced left fold for a finite sum. -/
def sum : List RawRat → RawRat
  | [] => zero
  | q :: qs => q.add (sum qs)

@[simp] theorem value_sum : ∀ qs : List RawRat,
    (sum qs).value = (qs.map value).sum := by
  intro qs
  induction qs with
  | nil => simp [sum]
  | cons q qs ih => simp [sum, ih]

theorem width_sum_le : ∀ qs : List RawRat,
    rawRatWidth (sum qs) ≤
      1 + (qs.map fun q ↦ rawRatWidth q + 1).sum := by
  intro qs
  induction qs with
  | nil => simp [sum, rawRatWidth_zero]
  | cons q qs ih =>
      rw [sum]
      exact (rawRatWidth_add_le _ _).trans (by
        simp only [List.map_cons, List.sum_cons]
        omega)

/-- Unreduced left fold for a finite product. -/
def product : List RawRat → RawRat
  | [] => one
  | q :: qs => q.mul (product qs)

@[simp] theorem value_product : ∀ qs : List RawRat,
    (product qs).value = (qs.map value).prod := by
  intro qs
  induction qs with
  | nil => simp [product]
  | cons q qs ih => simp [product, ih]

theorem width_product_le : ∀ qs : List RawRat,
    rawRatWidth (product qs) ≤
      1 + (qs.map rawRatWidth).sum := by
  intro qs
  induction qs with
  | nil => simp [product, rawRatWidth_one]
  | cons q qs ih =>
      rw [product]
      exact (rawRatWidth_mul_le _ _).trans (by
        simp only [List.map_cons, List.sum_cons]
        omega)

end RawRat

/-- Canonical rationals embed into `RawRat` without changing their value. -/
def rawRatOfRat (q : ℚ) : RawRat :=
  ⟨q.num, q.den, q.den_pos⟩

@[simp] theorem rawRatOfRat_value (q : ℚ) :
    (rawRatOfRat q).value = q := by
  simpa only [rawRatOfRat, RawRat.value] using! q.num_div_den

/-- The raw width of a canonical input is bounded by its exact project
encoding length. -/
theorem rawRatOfRat_width_le_encodedBitLength (q : ℚ) :
    rawRatWidth (rawRatOfRat q) ≤ encodedBitLength ℚ q := by
  apply max_le
  · exact (nat_size_le_encodedBitLength q.num.natAbs).trans
      ((natAbs_encodedBitLength_lt_integer q.num).le.trans
        (numerator_encodedBitLength_lt_rational q).le)
  · exact (nat_size_le_encodedBitLength q.den).trans
      (denominator_encodedBitLength_lt_rational q).le

/-- Fully explicit addition: cross-multiply in `RawRat`, run verified bounded
Euclid, and return the canonical rational. -/
def binaryRatAdd (q r : ℚ) : ℚ :=
  binaryNormalizeRawRat ((rawRatOfRat q).add (rawRatOfRat r))

theorem binaryRatAdd_eq_add (q r : ℚ) : binaryRatAdd q r = q + r := by
  simp [binaryRatAdd, binaryNormalizeRawRat_eq_value]

def binaryRatSub (q r : ℚ) : ℚ :=
  binaryNormalizeRawRat ((rawRatOfRat q).sub (rawRatOfRat r))

theorem binaryRatSub_eq_sub (q r : ℚ) : binaryRatSub q r = q - r := by
  simp [binaryRatSub, binaryNormalizeRawRat_eq_value]

def binaryRatNeg (q : ℚ) : ℚ :=
  binaryNormalizeRawRat (rawRatOfRat q).neg

theorem binaryRatNeg_eq_neg (q : ℚ) : binaryRatNeg q = -q := by
  simp [binaryRatNeg, binaryNormalizeRawRat_eq_value]

def binaryRatMul (q r : ℚ) : ℚ :=
  binaryNormalizeRawRat ((rawRatOfRat q).mul (rawRatOfRat r))

theorem binaryRatMul_eq_mul (q r : ℚ) : binaryRatMul q r = q * r := by
  simp [binaryRatMul, binaryNormalizeRawRat_eq_value]

def binaryRatInv (q : ℚ) : ℚ :=
  binaryNormalizeRawRat (rawRatOfRat q).inv

theorem binaryRatInv_eq_inv (q : ℚ) : binaryRatInv q = q⁻¹ := by
  simp [binaryRatInv, binaryNormalizeRawRat_eq_value]

def binaryRatDiv (q r : ℚ) : ℚ :=
  binaryNormalizeRawRat ((rawRatOfRat q).div (rawRatOfRat r))

theorem binaryRatDiv_eq_div (q r : ℚ) : binaryRatDiv q r = q / r := by
  simp [binaryRatDiv, binaryNormalizeRawRat_eq_value]

def binaryRatPow (q : ℚ) (k : ℕ) : ℚ :=
  binaryNormalizeRawRat ((rawRatOfRat q).pow k)

theorem binaryRatPow_eq_pow (q : ℚ) (k : ℕ) :
    binaryRatPow q k = q ^ k := by
  simp [binaryRatPow, binaryNormalizeRawRat_eq_value]

theorem binaryRatAdd_encodedBitLength_le (q r : ℚ) :
    encodedBitLength ℚ (binaryRatAdd q r) ≤
      32 + 12 * (encodedBitLength ℚ q + encodedBitLength ℚ r) := by
  have hw := rawRatWidth_add_le (rawRatOfRat q) (rawRatOfRat r)
  have hq := rawRatOfRat_width_le_encodedBitLength q
  have hr := rawRatOfRat_width_le_encodedBitLength r
  have hn := binaryNormalizeRawRat_encodedBitLength_le
    ((rawRatOfRat q).add (rawRatOfRat r))
  change encodedBitLength ℚ
      (binaryNormalizeRawRat ((rawRatOfRat q).add (rawRatOfRat r))) ≤ _
  calc
    _ ≤ 20 + 12 * rawRatWidth
        ((rawRatOfRat q).add (rawRatOfRat r)) := hn
    _ ≤ 20 + 12 * (encodedBitLength ℚ q +
        encodedBitLength ℚ r + 1) := by omega
    _ = 32 + 12 * (encodedBitLength ℚ q +
        encodedBitLength ℚ r) := by ring

theorem binaryRatSub_encodedBitLength_le (q r : ℚ) :
    encodedBitLength ℚ (binaryRatSub q r) ≤
      32 + 12 * (encodedBitLength ℚ q + encodedBitLength ℚ r) := by
  have hw := rawRatWidth_sub_le (rawRatOfRat q) (rawRatOfRat r)
  have hq := rawRatOfRat_width_le_encodedBitLength q
  have hr := rawRatOfRat_width_le_encodedBitLength r
  have hn := binaryNormalizeRawRat_encodedBitLength_le
    ((rawRatOfRat q).sub (rawRatOfRat r))
  change encodedBitLength ℚ
      (binaryNormalizeRawRat ((rawRatOfRat q).sub (rawRatOfRat r))) ≤ _
  calc
    _ ≤ 20 + 12 * rawRatWidth
        ((rawRatOfRat q).sub (rawRatOfRat r)) := hn
    _ ≤ 20 + 12 * (encodedBitLength ℚ q +
        encodedBitLength ℚ r + 1) := by omega
    _ = 32 + 12 * (encodedBitLength ℚ q +
        encodedBitLength ℚ r) := by ring

theorem binaryRatNeg_encodedBitLength_le (q : ℚ) :
    encodedBitLength ℚ (binaryRatNeg q) ≤
      20 + 12 * encodedBitLength ℚ q := by
  have hw := rawRatOfRat_width_le_encodedBitLength q
  have hn := binaryNormalizeRawRat_encodedBitLength_le
    (rawRatOfRat q).neg
  change encodedBitLength ℚ
      (binaryNormalizeRawRat (rawRatOfRat q).neg) ≤ _
  rw [rawRatWidth_neg] at hn
  omega

theorem binaryRatMul_encodedBitLength_le (q r : ℚ) :
    encodedBitLength ℚ (binaryRatMul q r) ≤
      20 + 12 * (encodedBitLength ℚ q + encodedBitLength ℚ r) := by
  have hw := rawRatWidth_mul_le (rawRatOfRat q) (rawRatOfRat r)
  have hq := rawRatOfRat_width_le_encodedBitLength q
  have hr := rawRatOfRat_width_le_encodedBitLength r
  have hn := binaryNormalizeRawRat_encodedBitLength_le
    ((rawRatOfRat q).mul (rawRatOfRat r))
  change encodedBitLength ℚ
      (binaryNormalizeRawRat ((rawRatOfRat q).mul (rawRatOfRat r))) ≤ _
  calc
    _ ≤ 20 + 12 * rawRatWidth
        ((rawRatOfRat q).mul (rawRatOfRat r)) := hn
    _ ≤ 20 + 12 * (encodedBitLength ℚ q +
        encodedBitLength ℚ r) := by omega

theorem binaryRatInv_encodedBitLength_le (q : ℚ) :
    encodedBitLength ℚ (binaryRatInv q) ≤
      20 + 12 * encodedBitLength ℚ q := by
  have hw := rawRatWidth_inv_le (rawRatOfRat q)
  have hq := rawRatOfRat_width_le_encodedBitLength q
  have hn := binaryNormalizeRawRat_encodedBitLength_le
    (rawRatOfRat q).inv
  change encodedBitLength ℚ
      (binaryNormalizeRawRat (rawRatOfRat q).inv) ≤ _
  omega

theorem binaryRatDiv_encodedBitLength_le (q r : ℚ) :
    encodedBitLength ℚ (binaryRatDiv q r) ≤
      20 + 12 * (encodedBitLength ℚ q + encodedBitLength ℚ r) := by
  have hw := rawRatWidth_div_le (rawRatOfRat q) (rawRatOfRat r)
  have hq := rawRatOfRat_width_le_encodedBitLength q
  have hr := rawRatOfRat_width_le_encodedBitLength r
  have hn := binaryNormalizeRawRat_encodedBitLength_le
    ((rawRatOfRat q).div (rawRatOfRat r))
  change encodedBitLength ℚ
      (binaryNormalizeRawRat ((rawRatOfRat q).div (rawRatOfRat r))) ≤ _
  omega

theorem binaryRatPow_encodedBitLength_le (q : ℚ) (k : ℕ) :
    encodedBitLength ℚ (binaryRatPow q k) ≤
      32 + 12 * k * encodedBitLength ℚ q := by
  have hw := RawRat.width_pow_le (rawRatOfRat q) k
  have hq := rawRatOfRat_width_le_encodedBitLength q
  have hn := binaryNormalizeRawRat_encodedBitLength_le
    ((rawRatOfRat q).pow k)
  have hw' : rawRatWidth ((rawRatOfRat q).pow k) ≤
      1 + k * encodedBitLength ℚ q :=
    hw.trans (Nat.add_le_add_left (Nat.mul_le_mul_left k hq) 1)
  change encodedBitLength ℚ
      (binaryNormalizeRawRat ((rawRatOfRat q).pow k)) ≤ _
  calc
    _ ≤ 20 + 12 * rawRatWidth ((rawRatOfRat q).pow k) := hn
    _ ≤ 20 + 12 * (1 + k * encodedBitLength ℚ q) := by omega
    _ = 32 + 12 * k * encodedBitLength ℚ q := by ring

end BeyondBethe
