/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesFactorialHessian

/-! # Iterates Half Square Scale

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
namespace AVenhance.Infra.Section4

/-- The retained terminal term and material product both have the first-step
q-squared scale. No factorial gain or initial-data division is used. -/
theorem iterate_half_square_scale_bound (n : ℕ) {D L C q N R : ℝ}
    (hD : 0 ≤ D) (hL : 0 < L) (hC : 0 ≤ C) (hq : 0 ≤ q) (hR : 0 ≤ R)
    (hscale : D * L ^ 2 ≤ C * q) :
    8 * D ^ 2 * (N * ((n + 2).factorial : ℝ) * L ^ (n + 2)) ^ 2 +
      16 * D ^ 2 * R * N ^ 2 * ((n + 1).factorial : ℝ) *
        ((n + 3).factorial : ℝ) * L ^ (n + 1) * L ^ (n + 3) ≤
      (8 + 32 * R) * C ^ 2 * q ^ 2 *
        (N * ((n + 2).factorial : ℝ) * L ^ n) ^ 2 := by
  have hs := (sq_le_sq₀ (by positivity : 0 ≤ D * L ^ 2)
    (mul_nonneg hC hq)).mpr hscale
  have hf := iterate_hessian_factorial_product_le n
  have hm := mul_le_mul_of_nonneg_left hf
    (by positivity : 0 ≤ 16 * D ^ 2 * R * N ^ 2 * L ^ (n + 1) * L ^ (n + 3))
  have ht := mul_le_mul_of_nonneg_left hs
    (by positivity : 0 ≤ (8 + 32 * R) * (N * ((n + 2).factorial : ℝ) * L ^ n) ^ 2)
  simp only [pow_succ] at hm ht ⊢
  nlinarith only [hm, ht]

end AVenhance.Infra.Section4
