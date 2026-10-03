/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-!
# Young's inequality for the bounded drift term

This is the pointwise absorption used after the weak energy estimate. The norm conversion from
the product norm on `Vec 2` to its Euclidean gradient norm is provided by the Galerkin
drift estimates.
-/

@[expose] public section

namespace AVenhance.Infra.Parabolic.WeakUniqueness

/-- Young's inequality in the normalization used for a drift pairing. -/
theorem drift_product_le_young {B κ a c : ℝ} (hκ : 0 < κ) :
    B * a * c ≤ κ / 2 * a ^ 2 + B ^ 2 / (2 * κ) * c ^ 2 := by
  have hsq : 0 ≤ (κ * a - B * c) ^ 2 := sq_nonneg _
  have hmul : 0 < 2 * κ := by positivity
  have hscaled :
      (2 * κ) * (B * a * c) ≤ (2 * κ) *
        (κ / 2 * a ^ 2 + B ^ 2 / (2 * κ) * c ^ 2) := by
    field_simp [ne_of_gt hκ]
    nlinarith [hsq]
  exact (le_of_mul_le_mul_left hscaled hmul)

end AVenhance.Infra.Parabolic.WeakUniqueness
