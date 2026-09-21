/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.Markoff.ExplicitNumerics

/-!
# Numerical certificates for the explicit strong-approximation cutoff

This file packages the closed real-power and natural-power calculations used
by the explicit middle game, endgame, cage, and small-order argument.
-/

namespace BGS.Markoff

open scoped Topology

/-! The certificates for the first explicit record remain available for
comparison, but the canonical declarations below use the ninth-moment cutoff. -/
namespace Legacy

private theorem fixed_pow_thirtyTwo_le_explicitDivisorConstant_of_le_32_pow
    {fixed : ℕ} (hfixed : fixed ≤ 32 ^ 32) :
    fixed ^ 32 ≤ BGS.NumberTheory.explicitDivisorConstant := by
  rw [BGS.NumberTheory.explicitDivisorConstant_eq]
  calc
    fixed ^ 32 ≤ (32 ^ 32) ^ 32 := Nat.pow_le_pow_left hfixed 32
    _ ≤ (32 ^ 32) ^ (2 ^ 32) :=
      pow_le_pow_right₀ (by norm_num) (by norm_num)

private theorem explicit_prime_one_lt
    {p : ℕ} (hp : explicitStrongApproximationCutoff ≤ p) :
    (1 : ℝ) < p := by
  exact_mod_cast explicitCutoff_gt_one.trans_le hp

private theorem rpow_lt_self_of_exponent_lt_one
    {p : ℕ} (hp : explicitStrongApproximationCutoff ≤ p)
    {a : ℝ} (ha : a < 1) :
    (p : ℝ) ^ a < p := by
  simpa only [Real.rpow_one] using
    Real.rpow_lt_rpow_of_exponent_lt (explicit_prime_one_lt hp) ha

/-- At the explicit cutoff, the all-divisors Corvaja--Zannier estimate obeys
both finite size conditions throughout the range
`p^(7/32) < currentOrder < p^(25/32)`. -/
theorem explicit_middleGame_corvajaZannier_sizeBounds
    {p currentOrder : ℕ} (hp : explicitStrongApproximationCutoff ≤ p)
    (hLower : (p : ℝ) ^ (7 / 32 : ℝ) < currentOrder)
    (hUpper : (currentOrder : ℝ) < (p : ℝ) ^ (25 / 32 : ℝ)) :
    (corvajaZannierCorollaryTwoSafeCoefficient *
        ((p - 1).divisors.card + (p + 1).divisors.card)) ^ 3 < currentOrder ∧
      corvajaZannierCorollaryTwoSafeCoefficient *
        ((p - 1).divisors.card + (p + 1).divisors.card) * currentOrder < p := by
  let A : ℕ := corvajaZannierCorollaryTwoSafeCoefficient *
    ((p - 1).divisors.card + (p + 1).divisors.card)
  have hpRealPos : (0 : ℝ) < p := (explicit_prime_one_lt hp).trans' zero_lt_one
  have hpRealNonneg : (0 : ℝ) ≤ p := hpRealPos.le
  have hA : (A : ℝ) ≤ 144 * (p : ℝ) ^ (2 / 32 : ℝ) := by
    dsimp [A]
    convert explicit_corvajaZannier_divisor_term_le hp using 1 <;> norm_num
  have h144cube : (144 ^ 3 : ℝ) < (p : ℝ) ^ (1 / 32 : ℝ) :=
    by
      have h := fixed_lt_rpow_one_div_thirtyTwo_of_explicitCutoff hp
        (fixed_pow_thirtyTwo_le_explicitDivisorConstant_of_le_32_pow
          (fixed := 144 ^ 3) (by norm_num))
      norm_num at h ⊢
      exact h
  have h144 : (144 : ℝ) < (p : ℝ) ^ (1 / 32 : ℝ) :=
    fixed_lt_rpow_one_div_thirtyTwo_of_explicitCutoff hp
      (fixed_pow_thirtyTwo_le_explicitDivisorConstant_of_le_32_pow
        (fixed := 144) (by norm_num))
  have hCubePower :
      (144 * (p : ℝ) ^ (2 / 32 : ℝ)) ^ 3 =
        144 ^ 3 * (p : ℝ) ^ (6 / 32 : ℝ) := by
    rw [mul_pow, ← Real.rpow_mul_natCast hpRealNonneg (2 / 32 : ℝ) 3]
    congr 2
    norm_num
  have hCube : (A : ℝ) ^ 3 < (currentOrder : ℝ) := by
    calc
      (A : ℝ) ^ 3 ≤ (144 * (p : ℝ) ^ (2 / 32 : ℝ)) ^ 3 := by
        exact pow_le_pow_left₀ (Nat.cast_nonneg A) hA 3
      _ = 144 ^ 3 * (p : ℝ) ^ (6 / 32 : ℝ) := hCubePower
      _ < (p : ℝ) ^ (1 / 32 : ℝ) *
          (p : ℝ) ^ (6 / 32 : ℝ) := by
        exact mul_lt_mul_of_pos_right h144cube
          (Real.rpow_pos_of_pos hpRealPos _)
      _ = (p : ℝ) ^ (7 / 32 : ℝ) := by
        rw [← Real.rpow_add hpRealPos]
        congr 1
        norm_num
      _ < currentOrder := hLower
  have hLinear : (A : ℝ) * currentOrder < p := by
    calc
      (A : ℝ) * currentOrder ≤
          (144 * (p : ℝ) ^ (2 / 32 : ℝ)) * currentOrder := by
        exact mul_le_mul_of_nonneg_right hA (Nat.cast_nonneg currentOrder)
      _ < (144 * (p : ℝ) ^ (2 / 32 : ℝ)) *
          (p : ℝ) ^ (25 / 32 : ℝ) := by
        exact mul_lt_mul_of_pos_left hUpper
          (mul_pos (by norm_num) (Real.rpow_pos_of_pos hpRealPos _))
      _ = 144 * ((p : ℝ) ^ (2 / 32 : ℝ) *
          (p : ℝ) ^ (25 / 32 : ℝ)) := by ring
      _ < (p : ℝ) ^ (1 / 32 : ℝ) *
          ((p : ℝ) ^ (2 / 32 : ℝ) *
            (p : ℝ) ^ (25 / 32 : ℝ)) := by
        exact mul_lt_mul_of_pos_right h144
          (mul_pos (Real.rpow_pos_of_pos hpRealPos _)
            (Real.rpow_pos_of_pos hpRealPos _))
      _ = (p : ℝ) ^ (28 / 32 : ℝ) := by
        rw [← Real.rpow_add hpRealPos, ← Real.rpow_add hpRealPos]
        congr 1
        norm_num
      _ < p := rpow_lt_self_of_exponent_lt_one hp (by norm_num)
  constructor
  · exact_mod_cast hCube
  · exact_mod_cast hLinear

/-- The primitive-inclusion--exclusion error is strictly smaller than its
main term for an exponent at most `2*p^(9/32)` and every coefficient at most
`34`. -/
theorem explicit_endgamePrimitiveTrace_explicitInequality
    {p orbitExponent coefficient : ℕ}
    (hp : explicitStrongApproximationCutoff ≤ p)
    (horbit : (orbitExponent : ℝ) ≤ 2 * (p : ℝ) ^ (9 / 32 : ℝ))
    (hcoefficient : coefficient ≤ 34) :
    (orbitExponent : ℝ) * ((p - 1).divisors.card : ℝ) ^ 2 *
        ((coefficient : ℝ) * Real.sqrt (p : ℝ)) < p := by
  have hpRealPos : (0 : ℝ) < p := (explicit_prime_one_lt hp).trans' zero_lt_one
  have hdivisorSum := explicit_divisor_sum_le_three_mul_rpow hp
  have hdivisor : ((p - 1).divisors.card : ℝ) ≤
      3 * (p : ℝ) ^ (2 / 32 : ℝ) := by
    norm_num only [Nat.cast_add] at hdivisorSum
    have hle : ((p - 1).divisors.card : ℝ) ≤
        ((p - 1).divisors.card : ℝ) + ((p + 1).divisors.card : ℝ) := by
      exact le_add_of_nonneg_right (Nat.cast_nonneg _)
    calc
      ((p - 1).divisors.card : ℝ) ≤
          ((p - 1).divisors.card : ℝ) + ((p + 1).divisors.card : ℝ) := hle
      _ ≤ 3 * (p : ℝ) ^ (1 / 16 : ℝ) := hdivisorSum
      _ = 3 * (p : ℝ) ^ (2 / 32 : ℝ) := by norm_num
  have hfixed : (2 * 3 ^ 2 * 34 : ℝ) <
      (p : ℝ) ^ (1 / 32 : ℝ) :=
    by
      have h := fixed_lt_rpow_one_div_thirtyTwo_of_explicitCutoff hp
        (fixed_pow_thirtyTwo_le_explicitDivisorConstant_of_le_32_pow
          (fixed := 2 * 3 ^ 2 * 34) (by norm_num))
      norm_num at h ⊢
      exact h
  have hsqrt : Real.sqrt (p : ℝ) = (p : ℝ) ^ (16 / 32 : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    congr 1
    norm_num
  calc
    (orbitExponent : ℝ) * ((p - 1).divisors.card : ℝ) ^ 2 *
        ((coefficient : ℝ) * Real.sqrt (p : ℝ)) ≤
      (2 * (p : ℝ) ^ (9 / 32 : ℝ)) *
        (3 * (p : ℝ) ^ (2 / 32 : ℝ)) ^ 2 *
        (34 * Real.sqrt (p : ℝ)) := by
      gcongr
      exact_mod_cast hcoefficient
    _ = (2 * 3 ^ 2 * 34) *
        ((p : ℝ) ^ (9 / 32 : ℝ) *
          ((p : ℝ) ^ (2 / 32 : ℝ)) ^ 2 *
          (p : ℝ) ^ (16 / 32 : ℝ)) := by rw [hsqrt]; ring
    _ = (2 * 3 ^ 2 * 34) * (p : ℝ) ^ (29 / 32 : ℝ) := by
      rw [← Real.rpow_mul_natCast hpRealPos.le (2 / 32 : ℝ) 2,
        ← Real.rpow_add hpRealPos, ← Real.rpow_add hpRealPos]
      congr 2
      norm_num
    _ < (p : ℝ) ^ (1 / 32 : ℝ) *
        (p : ℝ) ^ (29 / 32 : ℝ) := by
      exact mul_lt_mul_of_pos_right hfixed (Real.rpow_pos_of_pos hpRealPos _)
    _ = (p : ℝ) ^ (30 / 32 : ℝ) := by
      rw [← Real.rpow_add hpRealPos]
      congr 1
      norm_num
    _ < p := rpow_lt_self_of_exponent_lt_one hp (by norm_num)

/-- Split-torus form of the explicit primitive-trace certificate. -/
theorem explicit_endgamePrimitiveTrace_explicitInequality_of_card_sub_one
    {p orbitExponent orbitOrder coefficient : ℕ}
    (hp : explicitStrongApproximationCutoff ≤ p)
    (hmul : orbitExponent * orbitOrder = p - 1)
    (horder : (p : ℝ) ^ (23 / 32 : ℝ) ≤ orbitOrder)
    (hcoefficient : coefficient ≤ 34) :
    (orbitExponent : ℝ) * ((p - 1).divisors.card : ℝ) ^ 2 *
        ((coefficient : ℝ) * Real.sqrt (p : ℝ)) < p := by
  apply explicit_endgamePrimitiveTrace_explicitInequality hp ?_ hcoefficient
  have hpNat : 0 < p := by
    exact Nat.zero_lt_one.trans (explicitCutoff_gt_one.trans_le hp)
  have horder' : (p : ℝ) ^ ((1 : ℝ) / 2 + 7 / 32) ≤ orbitOrder := by
    convert horder using 1 <;> norm_num
  have horbit := orbitExponent_le_rpow_of_mul_order_eq_card_sub_one
    p orbitExponent orbitOrder hpNat hmul horder'
  calc
    (orbitExponent : ℝ) ≤ (p : ℝ) ^ ((1 : ℝ) / 2 - 7 / 32) := horbit
    _ = (p : ℝ) ^ (9 / 32 : ℝ) := by norm_num
    _ ≤ 2 * (p : ℝ) ^ (9 / 32 : ℝ) := by
      have hnonneg : (0 : ℝ) ≤ (p : ℝ) ^ (9 / 32 : ℝ) :=
        Real.rpow_nonneg (Nat.cast_nonneg p) _
      linarith

/-- Nonsplit-torus form of the explicit primitive-trace certificate. -/
theorem explicit_endgamePrimitiveTrace_explicitInequality_of_card_add_one
    {p orbitExponent orbitOrder coefficient : ℕ}
    (hp : explicitStrongApproximationCutoff ≤ p)
    (hmul : orbitExponent * orbitOrder = p + 1)
    (horder : (p : ℝ) ^ (23 / 32 : ℝ) ≤ orbitOrder)
    (hcoefficient : coefficient ≤ 34) :
    (orbitExponent : ℝ) * ((p - 1).divisors.card : ℝ) ^ 2 *
        ((coefficient : ℝ) * Real.sqrt (p : ℝ)) < p := by
  apply explicit_endgamePrimitiveTrace_explicitInequality hp ?_ hcoefficient
  have hpNat : 0 < p := by
    exact Nat.zero_lt_one.trans (explicitCutoff_gt_one.trans_le hp)
  have horder' : (p : ℝ) ^ ((1 : ℝ) / 2 + 7 / 32) ≤ orbitOrder := by
    convert horder using 1 <;> norm_num
  have horbit := orbitExponent_le_two_mul_rpow_of_mul_order_eq_card_add_one
    p orbitExponent orbitOrder hpNat hmul horder'
  convert horbit using 1 <;> norm_num

/-- The trace-zero order bound `4` lies below the explicit endgame threshold. -/
theorem explicit_four_lt_rpow_twentyThree_div_thirtyTwo
    {p : ℕ} (hp : explicitStrongApproximationCutoff ≤ p) :
    (4 : ℝ) < (p : ℝ) ^ (23 / 32 : ℝ) := by
  have hfour : (4 : ℝ) < (p : ℝ) ^ (1 / 32 : ℝ) :=
    small_fixed_lt_rpow_one_div_thirtyTwo_of_explicitCutoff hp (by norm_num)
  have hpOne := explicit_prime_one_lt hp
  exact hfour.trans (Real.rpow_lt_rpow_of_exponent_lt hpOne (by norm_num))

/-- The middle-game lower threshold also dominates the order-four exceptional
case. -/
theorem explicit_four_lt_rpow_seven_div_thirtyTwo
    {p : ℕ} (hp : explicitStrongApproximationCutoff ≤ p) :
    (4 : ℝ) < (p : ℝ) ^ (7 / 32 : ℝ) := by
  have hfour : (4 : ℝ) < (p : ℝ) ^ (1 / 32 : ℝ) :=
    small_fixed_lt_rpow_one_div_thirtyTwo_of_explicitCutoff hp (by norm_num)
  have hpOne := explicit_prime_one_lt hp
  exact hfour.trans (Real.rpow_lt_rpow_of_exponent_lt hpOne (by norm_num))

/-- The coefficient `100522` cage error is dominated by `p` at the explicit
cutoff. -/
theorem explicit_cageWitness_explicitInequality
    {p coefficient : ℕ} (hp : explicitStrongApproximationCutoff ≤ p)
    (hcoefficient : coefficient ≤ 100522) :
    ((p - 1).divisors.card : ℝ) ^ 2 *
        ((coefficient : ℝ) * Real.sqrt (p : ℝ)) < p := by
  have hpRealPos : (0 : ℝ) < p := (explicit_prime_one_lt hp).trans' zero_lt_one
  have hdivisorSum := explicit_divisor_sum_le_three_mul_rpow hp
  have hdivisor : ((p - 1).divisors.card : ℝ) ≤
      3 * (p : ℝ) ^ (2 / 32 : ℝ) := by
    norm_num only [Nat.cast_add] at hdivisorSum
    have hle : ((p - 1).divisors.card : ℝ) ≤
        ((p - 1).divisors.card : ℝ) + ((p + 1).divisors.card : ℝ) := by
      exact le_add_of_nonneg_right (Nat.cast_nonneg _)
    calc
      ((p - 1).divisors.card : ℝ) ≤
          ((p - 1).divisors.card : ℝ) + ((p + 1).divisors.card : ℝ) := hle
      _ ≤ 3 * (p : ℝ) ^ (1 / 16 : ℝ) := hdivisorSum
      _ = 3 * (p : ℝ) ^ (2 / 32 : ℝ) := by norm_num
  have hfixed : (3 ^ 2 * 100522 : ℝ) <
      (p : ℝ) ^ (1 / 32 : ℝ) :=
    by
      have h := fixed_lt_rpow_one_div_thirtyTwo_of_explicitCutoff hp
        (fixed_pow_thirtyTwo_le_explicitDivisorConstant_of_le_32_pow
          (fixed := 3 ^ 2 * 100522) (by norm_num))
      norm_num at h ⊢
      exact h
  have hsqrt : Real.sqrt (p : ℝ) = (p : ℝ) ^ (16 / 32 : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    congr 1
    norm_num
  calc
    ((p - 1).divisors.card : ℝ) ^ 2 *
        ((coefficient : ℝ) * Real.sqrt (p : ℝ)) ≤
      (3 * (p : ℝ) ^ (2 / 32 : ℝ)) ^ 2 *
        (100522 * Real.sqrt (p : ℝ)) := by
      gcongr
      exact_mod_cast hcoefficient
    _ = (3 ^ 2 * 100522) *
        (((p : ℝ) ^ (2 / 32 : ℝ)) ^ 2 *
          (p : ℝ) ^ (16 / 32 : ℝ)) := by rw [hsqrt]; ring
    _ = (3 ^ 2 * 100522) * (p : ℝ) ^ (20 / 32 : ℝ) := by
      rw [← Real.rpow_mul_natCast hpRealPos.le (2 / 32 : ℝ) 2,
        ← Real.rpow_add hpRealPos]
      congr 2
      norm_num
    _ < (p : ℝ) ^ (1 / 32 : ℝ) *
        (p : ℝ) ^ (20 / 32 : ℝ) := by
      exact mul_lt_mul_of_pos_right hfixed (Real.rpow_pos_of_pos hpRealPos _)
    _ = (p : ℝ) ^ (21 / 32 : ℝ) := by
      rw [← Real.rpow_add hpRealPos]
      congr 1
      norm_num
    _ < p := rpow_lt_self_of_exponent_lt_one hp (by norm_num)

/-- The elementary low-order count cannot contain a nonempty orbit whose
cardinality is divisible by `p` once `d ≤ p^(7/32)`. -/
theorem explicit_lowOrder_contradiction
    {p d : ℕ} (hp : explicitStrongApproximationCutoff ≤ p)
    (hpLe : p ≤ 32 * d ^ 4)
    (hd : (d : ℝ) ≤ (p : ℝ) ^ (7 / 32 : ℝ)) : False := by
  have hpRealPos : (0 : ℝ) < p := (explicit_prime_one_lt hp).trans' zero_lt_one
  have hfixed : (32 : ℝ) < (p : ℝ) ^ (1 / 32 : ℝ) :=
    small_fixed_lt_rpow_one_div_thirtyTwo_of_explicitCutoff hp (by norm_num)
  have hpLeReal : (p : ℝ) ≤ 32 * (d : ℝ) ^ 4 := by exact_mod_cast hpLe
  have hbound : (32 : ℝ) * (d : ℝ) ^ 4 < p := by
    calc
      (32 : ℝ) * (d : ℝ) ^ 4 ≤
          32 * ((p : ℝ) ^ (7 / 32 : ℝ)) ^ 4 := by
        gcongr
      _ < (p : ℝ) ^ (1 / 32 : ℝ) *
          ((p : ℝ) ^ (7 / 32 : ℝ)) ^ 4 := by
        exact mul_lt_mul_of_pos_right hfixed (pow_pos (Real.rpow_pos_of_pos hpRealPos _) _)
      _ = (p : ℝ) ^ (29 / 32 : ℝ) := by
        rw [← Real.rpow_mul_natCast hpRealPos.le (7 / 32 : ℝ) 4,
          ← Real.rpow_add hpRealPos]
        congr 1
        norm_num
      _ < p := rpow_lt_self_of_exponent_lt_one hp (by norm_num)
  exact (not_lt_of_ge hpLeReal) hbound

/-- Variant of `explicit_lowOrder_contradiction` for the `d + 1` cutoff used
when maximality turns a strict order bound into a finite-set inclusion. -/
theorem explicit_lowOrder_contradiction_512
    {p d : ℕ} (hp : explicitStrongApproximationCutoff ≤ p)
    (hpLe : p ≤ 512 * d ^ 4)
    (hd : (d : ℝ) ≤ (p : ℝ) ^ (7 / 32 : ℝ)) : False := by
  have hpRealPos : (0 : ℝ) < p := (explicit_prime_one_lt hp).trans' zero_lt_one
  have hfixed : (512 : ℝ) < (p : ℝ) ^ (1 / 32 : ℝ) :=
    small_fixed_lt_rpow_one_div_thirtyTwo_of_explicitCutoff hp (by norm_num)
  have hpLeReal : (p : ℝ) ≤ 512 * (d : ℝ) ^ 4 := by exact_mod_cast hpLe
  have hbound : (512 : ℝ) * (d : ℝ) ^ 4 < p := by
    calc
      (512 : ℝ) * (d : ℝ) ^ 4 ≤
          512 * ((p : ℝ) ^ (7 / 32 : ℝ)) ^ 4 := by
        gcongr
      _ < (p : ℝ) ^ (1 / 32 : ℝ) *
          ((p : ℝ) ^ (7 / 32 : ℝ)) ^ 4 := by
        exact mul_lt_mul_of_pos_right hfixed (pow_pos (Real.rpow_pos_of_pos hpRealPos _) _)
      _ = (p : ℝ) ^ (29 / 32 : ℝ) := by
        rw [← Real.rpow_mul_natCast hpRealPos.le (7 / 32 : ℝ) 4,
          ← Real.rpow_add hpRealPos]
        congr 1
        norm_num
      _ < p := rpow_lt_self_of_exponent_lt_one hp (by norm_num)
  exact (not_lt_of_ge hpLeReal) hbound

end Legacy

private theorem explicit_prime_one_lt
    {p : ℕ} (hp : explicitStrongApproximationCutoff ≤ p) :
    (1 : ℝ) < p := by
  exact_mod_cast explicitCutoff_gt_one.trans_le hp

private theorem rpow_lt_self_of_exponent_lt_one
    {p : ℕ} (hp : explicitStrongApproximationCutoff ≤ p)
    {a : ℝ} (ha : a < 1) :
    (p : ℝ) ^ a < p := by
  simpa only [Real.rpow_one] using
    Real.rpow_lt_rpow_of_exponent_lt (explicit_prime_one_lt hp) ha

/-- Below the five-sixths threshold, the coefficient-48 divisor term times
the current order is strictly smaller than `p`. -/
theorem explicit_middleGame_corvajaZannier_linear_of_lt_fiveSixths
    {p currentOrder : ℕ} (hp : explicitStrongApproximationCutoff ≤ p)
    (hUpper : (currentOrder : ℝ) < (p : ℝ) ^ (5 / 6 : ℝ)) :
    corvajaZannierCorollaryTwoSafeCoefficient *
        ((p - 1).divisors.card + (p + 1).divisors.card) * currentOrder < p := by
  let A : ℕ := corvajaZannierCorollaryTwoSafeCoefficient *
    ((p - 1).divisors.card + (p + 1).divisors.card)
  have hpRealPos : (0 : ℝ) < p := (explicit_prime_one_lt hp).trans' zero_lt_one
  have hA : (A : ℝ) < (p : ℝ) ^ (1 / 6 : ℝ) := by
    simpa [A] using explicit_corvajaZannier_divisor_term_lt_rpow_one_div_six hp
  have hLinearPower : (p : ℝ) ^ (1 / 6 : ℝ) *
      (p : ℝ) ^ (5 / 6 : ℝ) = (p : ℝ) := by
    rw [← Real.rpow_add hpRealPos]
    norm_num
  have hLinear : (A : ℝ) * currentOrder < p := by
    calc
      (A : ℝ) * currentOrder ≤
          (p : ℝ) ^ (1 / 6 : ℝ) * currentOrder :=
        mul_le_mul_of_nonneg_right hA.le (Nat.cast_nonneg currentOrder)
      _ < (p : ℝ) ^ (1 / 6 : ℝ) * (p : ℝ) ^ (5 / 6 : ℝ) :=
        mul_lt_mul_of_pos_left hUpper (Real.rpow_pos_of_pos hpRealPos _)
      _ = (p : ℝ) := hLinearPower
  exact_mod_cast hLinear

/-- Assembly-facing alias for the five-sixths middle-game certificate. -/
theorem explicit_middleGame_corvajaZannier_linearBound
    {p currentOrder : ℕ} (hp : explicitStrongApproximationCutoff ≤ p)
    (hUpper : (currentOrder : ℝ) < (p : ℝ) ^ (5 / 6 : ℝ)) :
    corvajaZannierCorollaryTwoSafeCoefficient *
        ((p - 1).divisors.card + (p + 1).divisors.card) * currentOrder < p :=
  explicit_middleGame_corvajaZannier_linear_of_lt_fiveSixths hp hUpper

/-- Primitive-trace inclusion--exclusion at exponent at most `2*p^(1/6)`. -/
theorem explicit_endgamePrimitiveTrace_explicitInequality
    {p orbitExponent coefficient : ℕ}
    (hp : explicitStrongApproximationCutoff ≤ p)
    (horbit : (orbitExponent : ℝ) ≤ 2 * (p : ℝ) ^ (1 / 6 : ℝ))
    (hcoefficient : coefficient ≤ 34) :
    (orbitExponent : ℝ) * ((p - 1).divisors.card : ℝ) ^ 2 *
        ((coefficient : ℝ) * Real.sqrt (p : ℝ)) < p := by
  let T := (p - 1).divisors.card + (p + 1).divisors.card
  have hpRealPos : (0 : ℝ) < p := (explicit_prime_one_lt hp).trans' zero_lt_one
  have hdivisor : ((p - 1).divisors.card : ℝ) ≤ (T : ℝ) := by
    exact_mod_cast (show (p - 1).divisors.card ≤ T by
      dsimp [T]
      omega)
  have hweighted : (68 : ℝ) * (T : ℝ) ^ 2 <
      (p : ℝ) ^ (1 / 3 : ℝ) := by
    simpa [T] using explicit_weighted_divisor_sum_sq_lt_rpow_one_div_three hp
  calc
    (orbitExponent : ℝ) * ((p - 1).divisors.card : ℝ) ^ 2 *
        ((coefficient : ℝ) * Real.sqrt (p : ℝ)) ≤
      (2 * (p : ℝ) ^ (1 / 6 : ℝ)) * (T : ℝ) ^ 2 *
        (34 * Real.sqrt (p : ℝ)) := by
      gcongr
      exact_mod_cast hcoefficient
    _ = (68 * (T : ℝ) ^ 2) *
        ((p : ℝ) ^ (1 / 6 : ℝ) * Real.sqrt (p : ℝ)) := by ring
    _ < (p : ℝ) ^ (1 / 3 : ℝ) *
        ((p : ℝ) ^ (1 / 6 : ℝ) * Real.sqrt (p : ℝ)) := by
      exact mul_lt_mul_of_pos_right hweighted <|
        mul_pos (Real.rpow_pos_of_pos hpRealPos _) (Real.sqrt_pos.2 hpRealPos)
    _ = (p : ℝ) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hpRealPos,
        ← Real.rpow_add hpRealPos]
      norm_num

/-- Split-torus form of the improved primitive-trace certificate. -/
theorem explicit_endgamePrimitiveTrace_explicitInequality_of_card_sub_one
    {p orbitExponent orbitOrder coefficient : ℕ}
    (hp : explicitStrongApproximationCutoff ≤ p)
    (hmul : orbitExponent * orbitOrder = p - 1)
    (horder : (p : ℝ) ^ (5 / 6 : ℝ) ≤ orbitOrder)
    (hcoefficient : coefficient ≤ 34) :
    (orbitExponent : ℝ) * ((p - 1).divisors.card : ℝ) ^ 2 *
        ((coefficient : ℝ) * Real.sqrt (p : ℝ)) < p := by
  apply explicit_endgamePrimitiveTrace_explicitInequality hp ?_ hcoefficient
  have hpNat : 0 < p := Nat.zero_lt_one.trans (explicitCutoff_gt_one.trans_le hp)
  have horbit := orbitExponent_le_rpow_of_mul_order_eq_card_sub_one
    p orbitExponent orbitOrder (δ := (1 / 3 : ℝ)) hpNat hmul (by
      convert horder using 1 <;> norm_num)
  calc
    (orbitExponent : ℝ) ≤ (p : ℝ) ^ (1 / 6 : ℝ) := by
      convert horbit using 1 <;> norm_num
    _ ≤ 2 * (p : ℝ) ^ (1 / 6 : ℝ) := by
      nlinarith [Real.rpow_nonneg (Nat.cast_nonneg p) (1 / 6 : ℝ)]

/-- Nonsplit-torus form of the improved primitive-trace certificate. -/
theorem explicit_endgamePrimitiveTrace_explicitInequality_of_card_add_one
    {p orbitExponent orbitOrder coefficient : ℕ}
    (hp : explicitStrongApproximationCutoff ≤ p)
    (hmul : orbitExponent * orbitOrder = p + 1)
    (horder : (p : ℝ) ^ (5 / 6 : ℝ) ≤ orbitOrder)
    (hcoefficient : coefficient ≤ 34) :
    (orbitExponent : ℝ) * ((p - 1).divisors.card : ℝ) ^ 2 *
        ((coefficient : ℝ) * Real.sqrt (p : ℝ)) < p := by
  apply explicit_endgamePrimitiveTrace_explicitInequality hp ?_ hcoefficient
  have hpNat : 0 < p := Nat.zero_lt_one.trans (explicitCutoff_gt_one.trans_le hp)
  have horbit := orbitExponent_le_two_mul_rpow_of_mul_order_eq_card_add_one
    p orbitExponent orbitOrder (δ := (1 / 3 : ℝ)) hpNat hmul (by
      convert horder using 1 <;> norm_num)
  convert horbit using 1 <;> norm_num

/-- The trace-zero order bound lies below the improved endgame threshold. -/
theorem explicit_four_lt_rpow_five_div_six
    {p : ℕ} (hp : explicitStrongApproximationCutoff ≤ p) :
    (4 : ℝ) < (p : ℝ) ^ (5 / 6 : ℝ) := by
  have hfour : (4 : ℝ) < (p : ℝ) ^ (1 / 8 : ℝ) :=
    small_fixed_lt_rpow_one_div_eight_of_explicitCutoff hp (by norm_num)
  exact hfour.trans <|
    Real.rpow_lt_rpow_of_exponent_lt (explicit_prime_one_lt hp) (by norm_num)

/-- The coefficient-`100522` cage error is dominated by `p`. -/
theorem explicit_cageWitness_explicitInequality
    {p coefficient : ℕ} (hp : explicitStrongApproximationCutoff ≤ p)
    (hcoefficient : coefficient ≤ 100522) :
    ((p - 1).divisors.card : ℝ) ^ 2 *
        ((coefficient : ℝ) * Real.sqrt (p : ℝ)) < p := by
  have hpRealPos : (0 : ℝ) < p := (explicit_prime_one_lt hp).trans' zero_lt_one
  have hpRealNonneg : (0 : ℝ) ≤ p := hpRealPos.le
  have hsum := explicit_divisor_sum_lt_rpow_one_div_eight hp
  have hdivisor : ((p - 1).divisors.card : ℝ) ≤
      (p : ℝ) ^ (1 / 8 : ℝ) := by
    norm_num only [Nat.cast_add] at hsum
    exact (le_add_of_nonneg_right (Nat.cast_nonneg _)).trans hsum.le
  have hfixed : (100522 : ℝ) < (p : ℝ) ^ (1 / 8 : ℝ) :=
    small_fixed_lt_rpow_one_div_eight_of_explicitCutoff hp (by norm_num)
  have hsqrt : Real.sqrt (p : ℝ) = (p : ℝ) ^ (4 / 8 : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    congr 1
    norm_num
  have hpower : ((p : ℝ) ^ (1 / 8 : ℝ)) ^ 2 * Real.sqrt (p : ℝ) =
      (p : ℝ) ^ (6 / 8 : ℝ) := by
    rw [hsqrt, ← Real.rpow_mul_natCast hpRealNonneg, ← Real.rpow_add hpRealPos]
    congr 1
    norm_num
  calc
    ((p - 1).divisors.card : ℝ) ^ 2 *
        ((coefficient : ℝ) * Real.sqrt (p : ℝ)) ≤
      ((p : ℝ) ^ (1 / 8 : ℝ)) ^ 2 *
        (100522 * Real.sqrt (p : ℝ)) := by
      gcongr
      exact_mod_cast hcoefficient
    _ = 100522 * (p : ℝ) ^ (6 / 8 : ℝ) := by rw [← hpower]; ring
    _ < (p : ℝ) ^ (1 / 8 : ℝ) * (p : ℝ) ^ (6 / 8 : ℝ) := by
      exact mul_lt_mul_of_pos_right hfixed (Real.rpow_pos_of_pos hpRealPos _)
    _ = (p : ℝ) ^ (7 / 8 : ℝ) := by
      rw [← Real.rpow_add hpRealPos]
      congr 1
      norm_num
    _ < p := rpow_lt_self_of_exponent_lt_one hp (by norm_num)

/-- A divisor-sensitive small-order set large enough to contain a nonempty
`p`-divisible orbit forces the Corvaja--Zannier cube below the maximal order. -/
theorem explicit_lowOrder_forces_corvajaZannier_cube
    {p d : ℕ} (hp : explicitStrongApproximationCutoff ≤ p)
    (hdPos : 0 < d)
    (hpLe : p ≤ 2 * (2 + d *
      ((p - 1).divisors.card + (p + 1).divisors.card)) ^ 2) :
    (corvajaZannierCorollaryTwoSafeCoefficient *
      ((p - 1).divisors.card + (p + 1).divisors.card)) ^ 3 < d := by
  let T := (p - 1).divisors.card + (p + 1).divisors.card
  let B := 48 ^ 3 + 1
  have hpTwo : 2 ≤ p := by
    have := explicitCutoff_gt_one.trans_le hp
    omega
  have hminusNonempty : (p - 1).divisors.Nonempty :=
    (Nat.nonempty_divisors).2 (by omega)
  have hplusNonempty : (p + 1).divisors.Nonempty :=
    (Nat.nonempty_divisors).2 (by omega)
  have hTtwo : 2 ≤ T := by
    have hm : 0 < (p - 1).divisors.card := Finset.card_pos.mpr hminusNonempty
    have hp' : 0 < (p + 1).divisors.card := Finset.card_pos.mpr hplusNonempty
    dsimp [T]
    omega
  have hTfour : 2 ≤ T ^ 4 := by
    calc
      2 ≤ T := hTtwo
      _ = T * 1 := by ring
      _ ≤ T * T ^ 3 := by
        gcongr
        exact Nat.one_le_pow 3 T (by omega)
      _ = T ^ 4 := by ring
  change (48 * T) ^ 3 < d
  by_contra hcube
  have hdUpper : d ≤ (48 * T) ^ 3 := by omega
  have hinner : 2 + d * T ≤ B * T ^ 4 := by
    calc
      2 + d * T ≤ T ^ 4 + d * T := Nat.add_le_add_right hTfour _
      _ ≤ T ^ 4 + (48 * T) ^ 3 * T := by gcongr
      _ = B * T ^ 4 := by dsimp [B]; ring
  have hpLeCoarse : p ≤ 2 * B ^ 2 * T ^ 8 := by
    calc
      p ≤ 2 * (2 + d * T) ^ 2 := by simpa [T] using hpLe
      _ ≤ 2 * (B * T ^ 4) ^ 2 := by gcongr
      _ = 2 * B ^ 2 * T ^ 8 := by ring
  have hmoment : T ^ 9 ≤ explicitDivisorMomentConstant * p := by
    simpa [T] using explicit_divisor_sum_pow_nine_le hpTwo
  have hpPowLe : p ^ 9 ≤
      (2 ^ 9 * B ^ 18 * explicitDivisorMomentConstant ^ 8) * p ^ 8 := by
    calc
      p ^ 9 ≤ (2 * B ^ 2 * T ^ 8) ^ 9 := Nat.pow_le_pow_left hpLeCoarse _
      _ = 2 ^ 9 * B ^ 18 * (T ^ 9) ^ 8 := by ring
      _ ≤ 2 ^ 9 * B ^ 18 *
          (explicitDivisorMomentConstant * p) ^ 8 := by gcongr
      _ = (2 ^ 9 * B ^ 18 * explicitDivisorMomentConstant ^ 8) * p ^ 8 := by
        ring
  have hconstant :
      2 ^ 9 * B ^ 18 * explicitDivisorMomentConstant ^ 8 < p := by
    simpa [B] using explicitCutoff_constant_lt hp
  have hstrict :
      (2 ^ 9 * B ^ 18 * explicitDivisorMomentConstant ^ 8) * p ^ 8 <
        p ^ 9 := by
    calc
      (2 ^ 9 * B ^ 18 * explicitDivisorMomentConstant ^ 8) * p ^ 8 <
          p * p ^ 8 :=
        mul_lt_mul_of_pos_right hconstant (pow_pos (by omega) 8)
      _ = p ^ 9 := by ring
  exact (not_lt_of_ge hpPowLe) hstrict

/-- Assembly-facing alias for the divisor-sensitive cube certificate. -/
theorem explicit_lowOrder_divisorSensitive_cube
    {p d : ℕ} (hp : explicitStrongApproximationCutoff ≤ p)
    (hdPos : 0 < d)
    (hpLe : p ≤ 2 * (2 + d *
      ((p - 1).divisors.card + (p + 1).divisors.card)) ^ 2) :
    (corvajaZannierCorollaryTwoSafeCoefficient *
      ((p - 1).divisors.card + (p + 1).divisors.card)) ^ 3 < d :=
  explicit_lowOrder_forces_corvajaZannier_cube hp hdPos hpLe

end BGS.Markoff
