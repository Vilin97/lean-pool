/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesHomogeneousAnalyticMaterial

/-! # Iterates Diffusive Material Scale

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
namespace AVenhance.Infra.Section4

/-- Diffusive normalization cancels the square-root diffusivity exactly. -/
theorem iterate_diffusive_material_normalization {κ N : ℝ} (hκ : 0 < κ) :
    κ ^ 2 * (N / Real.sqrt κ) ^ 2 = κ * N ^ 2 := by
  rw [div_pow, Real.sq_sqrt hκ.le]
  field_simp

/-- The two material factors have reciprocal diffusive scales. -/
theorem iterate_diffusive_material_product {κ N R : ℝ} (hκ : 0 < κ) :
    (R * Real.sqrt κ * N) * (N / Real.sqrt κ) = R * N ^ 2 := by
  have hs : Real.sqrt κ ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hκ)
  field_simp

/-- The preceding scalar gradient has the reciprocal diffusive normalization. -/
theorem iterate_diffusive_gradient_normalization {κ N : ℝ} (hκ : 0 < κ) :
    κ * (N / Real.sqrt κ) ^ 2 = N ^ 2 := by
  rw [div_pow, Real.sq_sqrt hκ.le]
  field_simp

end AVenhance.Infra.Section4
