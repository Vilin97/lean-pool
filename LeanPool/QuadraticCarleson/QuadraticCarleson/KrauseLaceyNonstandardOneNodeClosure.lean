/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/
module


public import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyScalarNearLocalInterpolation
public import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyNonstandardScaleWeight

/-!
# Finite nonstandard one-node closure

This file closes the numerical summation in the nonstandard half of the
Krause--Lacey one-node argument. The analytic operators remain in the
source range: the gap is `s : ℕ`, the physical suffix starts at `k₀ + s`,
and applications of the physical estimate retain `3 ≤ k₀`.

The first theorem is the exact finite `p'` summation mechanism. It is
separated from the operator-specific normalization so that no low-scale or
whole-good-part estimate is smuggled into the statement.
-/

@[expose] public section

open Function MeasureTheory Set
open scoped ENNReal BigOperators

namespace QuadraticCarleson
namespace KrauseLaceyNonstandardOneNodeClosure

open KrauseLaceyBadScale KrauseLaceyScalarNear


noncomputable
section

/-- The dimensionless scale weight in the nonstandard interpolation. -/
def oneNodeNonstandardScaleWeight (s : ℕ) : ℝ :=
  nonstandardScaleWeight s

theorem oneNodeNonstandardScaleWeight_pos (s : ℕ) :
    0 < oneNodeNonstandardScaleWeight s :=
  nonstandardScaleWeight_pos s

theorem oneNodeNonstandardScaleWeight_le (s : ℕ) :
    oneNodeNonstandardScaleWeight s ≤ 64 * (2 : ℝ) ^ (-(s : ℝ) / 5) :=
  nonstandardScaleWeight_le s

theorem oneNodeNonstandardScaleWeight_rpow_le_scaleDecayRatio
    {q : ℝ} (hq : 2 ≤ q) (s : ℕ) :
    oneNodeNonstandardScaleWeight s ^ (1 / q) ≤
      8 * scaleDecayRatio q ^ s :=
  nonstandardScaleWeight_rpow_le_scaleDecayRatio hq s

theorem finite_sum_oneNodeNonstandardScaleWeight_rpow_le
    {q : ℝ} (hq : 2 ≤ q) (N : ℕ) :
    (∑ s ∈ Finset.range N, oneNodeNonstandardScaleWeight s ^ (1 / q)) ≤
      160 * q :=
  finite_sum_nonstandardScaleWeight_rpow_le hq N

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
