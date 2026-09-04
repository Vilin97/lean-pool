/-
Copyright (c) 2026 Yuanhe Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuanhe Zhang, Jason D. Lee, Fanghui Liu
-/
import LeanPool.StatisticalLearningTheory.LeastSquares.Defs

/-!
# Empirical-Norm Scaling

## Main Results

* `empiricalNorm_smul_of_nonneg`: the empirical norm scales linearly by nonnegative scalars.

-/

noncomputable section

namespace LeanPool.StatisticalLearningTheory

open Finset BigOperators Real

namespace LeastSquares

variable {n : ℕ} {X : Type*}

/-!
## Empirical Norm Scaling

The empirical norm scales linearly for non-negative scalars.
-/

/-- For α ≥ 0, ‖α • h‖_n = α * ‖h‖_n -/
lemma empiricalNorm_smul_of_nonneg {f : Fin n → ℝ} {α : ℝ} (hα : 0 ≤ α) :
    empiricalNorm n (α • f) = α * empiricalNorm n f := by
  unfold empiricalNorm
  simp only [Pi.smul_apply, smul_eq_mul]
  have h1 : ∀ i, (α * f i) ^ 2 = α ^ 2 * f i ^ 2 := fun i => by ring
  simp only [h1]
  rw [← Finset.mul_sum]
  -- Goal: √(n⁻¹ * (α² * Σf²)) = α * √(n⁻¹ * Σf²)
  have h2 :
      (n : ℝ)⁻¹ * (α ^ 2 * ∑ i : Fin n, f i ^ 2) =
        α ^ 2 * ((n : ℝ)⁻¹ * ∑ i : Fin n, f i ^ 2) := by
    ring
  rw [h2]
  rw [Real.sqrt_mul (sq_nonneg α)]
  rw [Real.sqrt_sq hα]

end LeastSquares

end LeanPool.StatisticalLearningTheory
