/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyScalarNearLocalInterpolation
import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyScaleSummation

/-!
# Finite nonstandard one-node closure

This file closes the numerical summation in the nonstandard half of the
Krause--Lacey one-node argument.  The analytic operators remain in the
source range: the gap is `s : ℕ`, the physical suffix starts at `k₀ + s`,
and applications of the physical estimate retain `3 ≤ k₀`.

The first theorem is the exact finite `p'` summation mechanism.  It is
separated from the operator-specific normalization so that no low-scale or
whole-good-part estimate is smuggled into the statement.
-/

open Function MeasureTheory Set
open scoped ENNReal BigOperators

namespace QuadraticCarleson
namespace KrauseLaceyNonstandardOneNodeClosure

open KrauseLaceyBadScale KrauseLaceyScalarNear


noncomputable section

/-- The dimensionless scale weight in the nonstandard interpolation. -/
def oneNodeNonstandardScaleWeight (s : ℕ) : ℝ :=
  ((s + 1 : ℕ) : ℝ) ^ 2 * (2 : ℝ) ^ (-(s : ℝ))

theorem oneNodeNonstandardScaleWeight_pos (s : ℕ) :
    0 < oneNodeNonstandardScaleWeight s := by
  unfold oneNodeNonstandardScaleWeight
  positivity

private theorem sq_succ_le_sixtyFour_mul_rpow_four_fifths (s : ℕ) :
    (((s + 1 : ℕ) : ℝ) ^ 2) ≤
      64 * (2 : ℝ) ^ ((4 : ℝ) * s / 5) := by
  induction s using Nat.strong_induction_on with
  | h s ih =>
      by_cases hs : s ≤ 5
      · have hsq : (((s + 1 : ℕ) : ℝ) ^ 2) ≤ 36 := by
          norm_num at hs ⊢
          interval_cases s <;> norm_num
        have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ ((4 : ℝ) * s / 5) :=
          Real.one_le_rpow (by norm_num) (by positivity)
        nlinarith
      · have hs6 : 6 ≤ s := by omega
        let t := s - 5
        have htlt : t < s := by dsimp [t]; omega
        have ht1 : 1 ≤ t := by dsimp [t]; omega
        have hi := ih t htlt
        have hnat : s = t + 5 := by dsimp [t]; omega
        have hlin : ((s + 1 : ℕ) : ℝ) ≤ 4 * (((t + 1 : ℕ) : ℝ)) := by
          exact_mod_cast (show s + 1 ≤ 4 * (t + 1) by omega)
        have hsq : (((s + 1 : ℕ) : ℝ) ^ 2) ≤
            16 * (((t + 1 : ℕ) : ℝ) ^ 2) := by nlinarith
        calc
          (((s + 1 : ℕ) : ℝ) ^ 2) ≤ 16 * (((t + 1 : ℕ) : ℝ) ^ 2) := hsq
          _ ≤ 16 * (64 * (2 : ℝ) ^ ((4 : ℝ) * t / 5)) := by gcongr
          _ = 64 * (2 : ℝ) ^ ((4 : ℝ) * s / 5) := by
            rw [hnat]
            rw [show (4 : ℝ) * (↑(t + 5) : ℝ) / 5 =
              (4 : ℝ) * t / 5 + 4 by push_cast; ring]
            rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
            norm_num
            ring

theorem oneNodeNonstandardScaleWeight_le (s : ℕ) :
    oneNodeNonstandardScaleWeight s ≤ 64 * (2 : ℝ) ^ (-(s : ℝ) / 5) := by
  have h := sq_succ_le_sixtyFour_mul_rpow_four_fifths s
  have hmul := mul_le_mul_of_nonneg_right h
    (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (-(s : ℝ)))
  unfold oneNodeNonstandardScaleWeight
  calc
    (((s + 1 : ℕ) : ℝ) ^ 2) * (2 : ℝ) ^ (-(s : ℝ)) ≤
        (64 * (2 : ℝ) ^ ((4 : ℝ) * s / 5)) *
          (2 : ℝ) ^ (-(s : ℝ)) := hmul
    _ = 64 * (2 : ℝ) ^ (-(s : ℝ) / 5) := by
      rw [mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring

theorem oneNodeNonstandardScaleWeight_rpow_le_scaleDecayRatio
    {q : ℝ} (hq : 2 ≤ q) (s : ℕ) :
    oneNodeNonstandardScaleWeight s ^ (1 / q) ≤
      8 * scaleDecayRatio q ^ s := by
  have hq0 : 0 < q := by linarith
  have hpow := Real.rpow_le_rpow
    (oneNodeNonstandardScaleWeight_pos s).le (oneNodeNonstandardScaleWeight_le s)
      (by positivity : 0 ≤ (1 : ℝ) / q)
  have hexp : (1 : ℝ) / q ≤ 1 / 2 :=
    (div_le_div_iff_of_pos_left one_pos hq0 (by norm_num)).mpr hq
  have h64 : (64 : ℝ) ^ (1 / q) ≤ 8 := by
    calc
      (64 : ℝ) ^ (1 / q) ≤ (64 : ℝ) ^ (1 / 2) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
      _ = 8 := by norm_num [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num]
  calc
    oneNodeNonstandardScaleWeight s ^ (1 / q) ≤
        (64 * (2 : ℝ) ^ (-(s : ℝ) / 5)) ^ (1 / q) := hpow
    _ = (64 : ℝ) ^ (1 / q) *
        (2 : ℝ) ^ ((-(s : ℝ) / 5) * (1 / q)) := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 64)
        (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _),
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    _ ≤ 8 * (2 : ℝ) ^ ((-(s : ℝ) / 5) * (1 / q)) := by gcongr
    _ = 8 * scaleDecayRatio q ^ s := by
      unfold scaleDecayRatio
      rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]
      congr 2
      field_simp

theorem finite_sum_oneNodeNonstandardScaleWeight_rpow_le
    {q : ℝ} (hq : 2 ≤ q) (N : ℕ) :
    (∑ s ∈ Finset.range N, oneNodeNonstandardScaleWeight s ^ (1 / q)) ≤
      160 * q := by
  calc
    _ ≤ ∑ s ∈ Finset.range N, 8 * scaleDecayRatio q ^ s :=
      Finset.sum_le_sum fun s _ ↦
        oneNodeNonstandardScaleWeight_rpow_le_scaleDecayRatio hq s
    _ = 8 * ∑ s ∈ Finset.range N, scaleDecayRatio q ^ s := by
      rw [Finset.mul_sum]
    _ ≤ 8 * (20 * q) := by
      gcongr
      simpa only [Finset.sum_filter, Finset.mem_range, if_pos] using
        finite_scaleDecayRatio_sum_le_twenty_mul_q hq N
    _ = 160 * q := by ring

/-- Summing bounds with the source weight
`(((s+1)^2 2^{-s})^(1/q))` costs at most `160 q`.

This is the finite, extended-nonnegative-real form used for lintegrals.
Neither the functions `u` nor the common factors are assumed finite. -/
theorem finite_sum_le_of_nonstandardScaleWeight
    {q : ℝ} (hq : 2 ≤ q) (N : ℕ) (u : ℕ → ℝ≥0∞) (K atom : ℝ≥0∞)
    (hu : ∀ s ∈ Finset.range N,
      u s ≤ K * ENNReal.ofReal (oneNodeNonstandardScaleWeight s ^ (1 / q)) * atom) :
    (∑ s ∈ Finset.range N, u s) ≤
      K * ENNReal.ofReal (160 * q) * atom := by
  calc
    (∑ s ∈ Finset.range N, u s) ≤
        ∑ s ∈ Finset.range N,
          K * ENNReal.ofReal (oneNodeNonstandardScaleWeight s ^ (1 / q)) * atom :=
      Finset.sum_le_sum hu
    _ = K * ENNReal.ofReal
          (∑ s ∈ Finset.range N, oneNodeNonstandardScaleWeight s ^ (1 / q)) * atom := by
      rw [ENNReal.ofReal_sum_of_nonneg]
      · simp_rw [mul_assoc]
        rw [← Finset.mul_sum, Finset.sum_mul]
      · intro s hs
        exact Real.rpow_nonneg (oneNodeNonstandardScaleWeight_pos s).le _
    _ ≤ K * ENNReal.ofReal (160 * q) * atom := by
      gcongr
      exact finite_sum_oneNodeNonstandardScaleWeight_rpow_le hq N

/-- The same summation with the paper's exponent `q = p'`. -/
theorem finite_sum_le_of_nonstandardScaleWeight_holderConjugate
    {p : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) (N : ℕ)
    (u : ℕ → ℝ≥0∞) (K atom : ℝ≥0∞)
    (hu : ∀ s ∈ Finset.range N,
      u s ≤ K * ENNReal.ofReal
        (oneNodeNonstandardScaleWeight s ^ (1 / holderConjugate p)) * atom) :
    (∑ s ∈ Finset.range N, u s) ≤
      K * ENNReal.ofReal (160 * holderConjugate p) * atom := by
  exact finite_sum_le_of_nonstandardScaleWeight
    (holderConjugate_ge_two hp hp2) N u K atom hu


end

end KrauseLaceyNonstandardOneNodeClosure
end QuadraticCarleson
