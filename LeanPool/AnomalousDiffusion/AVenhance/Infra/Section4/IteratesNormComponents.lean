/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesDiffusiveMaterialScale

/-! # Iterates Norm Components

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
namespace AVenhance.Infra.Section4

/-- A squared sum norm bounds each energy separately. -/
theorem iterate_norm_sq_components {e g κ H : ℝ}
    (he : 0 ≤ e) (hg : 0 ≤ g) (hκ : 0 ≤ κ)
    (hbound : (Real.sqrt e + Real.sqrt κ * Real.sqrt g) ^ 2 ≤ H) :
    e ≤ H ∧ κ * g ≤ H := by
  have hse := Real.sq_sqrt he
  have hsg := Real.sq_sqrt hg
  have hsk := Real.sq_sqrt hκ
  have hp : 0 ≤ Real.sqrt e * (Real.sqrt κ * Real.sqrt g) := by positivity
  have hprod : (Real.sqrt κ * Real.sqrt g) ^ 2 = κ * g := by
    rw [mul_pow, hsk, hsg]
  constructor <;> nlinarith only [hbound, hse, hprod, hp, he, mul_nonneg hκ hg]

/-- The gradient component has the reciprocal diffusive amplitude, also when
 the initial-data norm vanishes. -/
theorem iterate_norm_sq_gradient_bound {e g κ N A W : ℝ}
    (he : 0 ≤ e) (hg : 0 ≤ g) (hκ : 0 < κ)
    (hbound : (Real.sqrt e + Real.sqrt κ * Real.sqrt g) ^ 2 ≤ N ^ 2 * A ^ 2 * W ^ 2) :
    g ≤ (N * A / Real.sqrt κ) ^ 2 * W ^ 2 := by
  have hb := (iterate_norm_sq_components he hg hκ.le hbound).2
  apply le_of_mul_le_mul_left (a := κ) _ hκ
  calc
    _ ≤ N ^ 2 * A ^ 2 * W ^ 2 := hb
    _ = κ * ((N * A / Real.sqrt κ) ^ 2 * W ^ 2) := by
      rw [← mul_assoc, iterate_diffusive_gradient_normalization hκ]
      ring

end AVenhance.Infra.Section4
