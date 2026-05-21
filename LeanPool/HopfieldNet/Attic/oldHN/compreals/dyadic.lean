/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Data.Rat.Star

namespace Computable

/-- Approximate rationals: a computational carrier with certified rounding. -/
class ApproxRationals (AQ : Type) extends
    Zero AQ, One AQ, Add AQ, Neg AQ, Sub AQ, Mul AQ where
  /-- Specification semantics. -/
  toRat : AQ → ℚ
  /-- Arithmetic compatibility (simp lemmas). -/
  toRat_zero : toRat 0 = 0
  toRat_one : toRat 1 = 1
  toRat_add : ∀ a b, toRat (a + b) = toRat a + toRat b
  toRat_neg : ∀ a, toRat (-a) = - toRat a
  toRat_sub : ∀ a b, toRat (a - b) = toRat a - toRat b
  toRat_mul : ∀ a b, toRat (a * b) = toRat a * toRat b
  /-- Rounding/compression. -/
  approx : AQ → ℕ → AQ
  /-- Certified error bound. -/
  abs_toRat_approx_sub_le : ∀ x n,
    |toRat (approx x n) - toRat x| ≤ (1 : ℚ) / (2 ^ n)

  /-- Approximate a rational number into the carrier at precision `n`. -/
  approxRat : ℚ → ℕ → AQ

  /-- Certified error bound for `approxRat`. -/
  abs_toRat_approxRat_sub_le : ∀ q n,
    |toRat (approxRat q n) - q| ≤ (1 : ℚ) / (2 ^ n)

namespace ApproxRationals

variable {AQ : Type} [ApproxRationals AQ]

attribute [simp] ApproxRationals.toRat_zero ApproxRationals.toRat_one
attribute [simp] ApproxRationals.toRat_add ApproxRationals.toRat_neg
attribute [simp] ApproxRationals.toRat_sub ApproxRationals.toRat_mul

end ApproxRationals

/-! ## Trivial exact instance for `ℚ` -/

instance : ApproxRationals ℚ where
  toRat := id
  toRat_zero := rfl
  toRat_one := rfl
  toRat_add := by intro a b; rfl
  toRat_neg := by intro a; rfl
  toRat_sub := by intro a b; rfl
  toRat_mul := by intro a b; rfl
  approx := fun q _ => q
  abs_toRat_approx_sub_le := by
    intro q n
    simp
  approxRat := fun q _ => q
  abs_toRat_approxRat_sub_le := by
    intro q n
    simp

/-! ## `Dyadic` instance using Lean core rounding -/

namespace DyadicApprox

/-- The unit in the last place at precision `n` - this is `2^(-n)` -/
def dyadicUlp (n : ℕ) : Dyadic :=
  Dyadic.ofIntWithPrec 1 n

/-- Approximate a rational by rounding it downward to precision `n`. -/
@[inline] def approxRat (q : ℚ) (n : Nat) : Dyadic :=
  Rat.toDyadic q n

/-- Approximate a dyadic by rounding its semantic value downward to precision `n`. -/
@[inline] def approx (x : Dyadic) (n : Nat) : Dyadic :=
  Rat.toDyadic x.toRat n

/--
Rounding error bound for `DyadicApprox.approx`, obtained from the core theorems
about `Rat.toDyadic`.

This uses the bracketing property:
* `toRat (q.toDyadic n) ≤ q`
* `q < toRat (q.toDyadic n) + dyadicUlp n`
-/
theorem abs_toRat_approx_sub_le (x : Dyadic) (n : Nat) :
    |(approx x n).toRat - x.toRat| ≤ (1 : ℚ) / (2 ^ n) := by
  -- Abbreviate `y = x.toRat.toDyadic n`.
  let y : Dyadic := Rat.toDyadic x.toRat n
  have hle : y.toRat ≤ x.toRat := by
    -- Use the lemma directly, not as a function
    exact Rat.toRat_toDyadic_le
  have hlt : x.toRat < (y + dyadicUlp n).toRat := by
    -- Use the lemma directly, not as a function
    exact Rat.lt_toRat_toDyadic_add
  have h_nonneg : 0 ≤ x.toRat - y.toRat := sub_nonneg.mpr hle
  have h_le_ulp : x.toRat - y.toRat ≤ (dyadicUlp n).toRat := by
    have : x.toRat - y.toRat < (dyadicUlp n).toRat := by
      -- from `x < y + ulp`, we have x.toRat < y.toRat + (dyadicUlp n).toRat
      have h : x.toRat < y.toRat + (dyadicUlp n).toRat := by
        have heq : (y + dyadicUlp n).toRat = y.toRat + (dyadicUlp n).toRat := Dyadic.toRat_add y (dyadicUlp n)
        rw [heq] at hlt
        exact hlt
      linarith
    exact le_of_lt this
  have habs : |y.toRat - x.toRat| = x.toRat - y.toRat := by
    -- `y.toRat ≤ x.toRat`.
    rw [abs_sub_comm]
    exact abs_of_nonneg h_nonneg
  calc
    |(approx x n).toRat - x.toRat|
        = |y.toRat - x.toRat| := by simp [DyadicApprox.approx, y]
    _ = x.toRat - y.toRat := habs
    _ ≤ (dyadicUlp n).toRat := h_le_ulp
    _ = (1 : ℚ) / (2 ^ n) := by
      -- `dyadicUlp n` is `2^{-n}` by definition
      simp [dyadicUlp, Dyadic.toRat_ofIntWithPrec_eq_mul_two_pow]

theorem abs_toRat_approxRat_sub_le (q : ℚ) (n : Nat) :
    |(approxRat q n).toRat - q| ≤ (1 : ℚ) / (2 ^ n) := by
  let y : Dyadic := Rat.toDyadic q n
  have hle : y.toRat ≤ q := by
    -- Use the lemma directly, not as a function
    exact Rat.toRat_toDyadic_le
  have hlt : q < (y + dyadicUlp n).toRat := by
    -- Use the lemma directly, not as a function
    exact Rat.lt_toRat_toDyadic_add
  have h_nonneg : 0 ≤ q - y.toRat := sub_nonneg.mpr hle
  have h_le_ulp : q - y.toRat ≤ (dyadicUlp n).toRat := by
    have : q - y.toRat < (dyadicUlp n).toRat := by
      have h : q < y.toRat + (dyadicUlp n).toRat := by
        have heq : (y + dyadicUlp n).toRat = y.toRat + (dyadicUlp n).toRat :=
          Dyadic.toRat_add y (dyadicUlp n)
        rw [heq] at hlt
        exact hlt
      linarith
    exact le_of_lt this
  have habs : |y.toRat - q| = q - y.toRat := by
    rw [abs_sub_comm]
    exact abs_of_nonneg h_nonneg
  calc
    |(approxRat q n).toRat - q|
        = |y.toRat - q| := by simp [DyadicApprox.approxRat, y]
    _ = q - y.toRat := habs
    _ ≤ (dyadicUlp n).toRat := h_le_ulp
    _ = (1 : ℚ) / (2 ^ n) := by
      simp [dyadicUlp, Dyadic.toRat_ofIntWithPrec_eq_mul_two_pow]

end DyadicApprox

instance : ApproxRationals Dyadic where
  toRat := Dyadic.toRat
  toRat_zero := by simp
  toRat_one := by
    -- `1 : Dyadic` is `Dyadic.ofIntWithPrec 1 0`, so its rational value is `1`.
    change Dyadic.toRat (Dyadic.ofInt 1) = 1
    simp [Dyadic.ofInt, Dyadic.toRat_ofIntWithPrec_eq_mul_two_pow]
  toRat_add := by intro a b; simp
  toRat_neg := by intro a; simp
  toRat_sub := by intro a b; simp [sub_eq_add_neg]
  toRat_mul := by intro a b; simp
  approx := DyadicApprox.approx
  abs_toRat_approx_sub_le := DyadicApprox.abs_toRat_approx_sub_le
  approxRat := DyadicApprox.approxRat
  abs_toRat_approxRat_sub_le := DyadicApprox.abs_toRat_approxRat_sub_le

end Computable
