/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Elementary bounds for Taylor remainders

These real inequalities choose a small radius and absorb a cubic error into a quadratic bound.

## Main results

* `le_one_and_mul_add_le_of_le_min`: Radius constraints used to absorb a cubic Taylor error into a
  quadratic budget `η t ^ 2`.
* `taylor_remainder_add_cubic_le`: Combine a second-order remainder of size `O(t ^ 2)` with a cubic
  error of size `O(t ^ 3)` into a single quadratic bound `η t ^ 2`.
-/

public section

namespace SeveralComplexVariables.TaylorBounds

/-- Radius constraints used to absorb a cubic Taylor error into a quadratic budget `η t ^ 2`. -/
theorem le_one_and_mul_add_le_of_le_min {η M₀ M₁ δ' r : ℝ} (hM₀ : 0 ≤ M₀)
    (hM₁ : 0 ≤ M₁) (hr : 0 < r)
    (hr₀ : r ≤ min 1 (min (η / (2 * (M₁ + 1))) (δ' / (2 * (M₀ + 1))))) :
    r ≤ 1 ∧ r * (M₁ + 1) ≤ η / 2 ∧ r * (M₀ + 1) < δ' := by
  have hr1 : r ≤ 1 := hr₀.trans (min_le_left _ _)
  have hrM₁ : r * (M₁ + 1) ≤ η / 2 := by
    have := hr₀.trans ((min_le_right _ _).trans (min_le_left _ _))
    rw [le_div_iff₀ (by positivity)] at this
    linarith
  have hrδ' : r * (M₀ + 1) < δ' := by
    have := hr₀.trans ((min_le_right _ _).trans (min_le_right _ _))
    rw [le_div_iff₀ (by positivity)] at this
    have : 0 < r * (M₀ + 1) := by positivity
    linarith
  exact ⟨hr1, hrM₁, hrδ'⟩

/-- Combine a second-order remainder of size `O(t ^ 2)` with a cubic error of size `O(t ^ 3)` into a
single quadratic bound `η t ^ 2`. -/
theorem taylor_remainder_add_cubic_le {η t M₀ M₁ rem cub : ℝ} (ht : 0 < t) (hη : 0 < η)
    (htM₁ : t * (M₁ + 1) ≤ η / 2)
    (hrem : |rem| ≤ η / (2 * (M₀ ^ 2 + 1)) * (t * M₀) ^ 2) (hcub : |cub| ≤ M₁ * t ^ 3) :
    |rem + cub| ≤ η * t ^ 2 := by
  have hR : |rem| ≤ η / 2 * t ^ 2 := by
    refine hrem.trans ?_
    rw [mul_pow, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    have : M₀ ^ 2 ≤ M₀ ^ 2 + 1 := by linarith
    calc η * (t ^ 2 * M₀ ^ 2) ≤ η * (t ^ 2 * (M₀ ^ 2 + 1)) := by gcongr
      _ = η / 2 * t ^ 2 * (2 * (M₀ ^ 2 + 1)) := by ring
  have hC : |cub| ≤ η / 2 * t ^ 2 := by
    refine hcub.trans ?_
    calc M₁ * t ^ 3 = t * M₁ * t ^ 2 := by ring
      _ ≤ η / 2 * t ^ 2 := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          have : t * M₁ ≤ t * (M₁ + 1) :=
            mul_le_mul_of_nonneg_left (by linarith) ht.le
          linarith
  calc |rem + cub| ≤ |rem| + |cub| := abs_add_le _ _
    _ ≤ η / 2 * t ^ 2 + η / 2 * t ^ 2 := add_le_add hR hC
    _ = η * t ^ 2 := by ring

end SeveralComplexVariables.TaylorBounds

end

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
