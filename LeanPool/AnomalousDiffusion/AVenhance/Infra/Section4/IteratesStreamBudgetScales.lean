/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesHigherEnergyBudget
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-! # Iterates Stream Budget Scales

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
namespace AVenhance.Infra.Section4

/-- Cancellation of the microscopic radius in the quadratic stream term.
This identifies the fourth-power gain without estimating either factor alone. -/
theorem iterate_quadratic_stream_scale_identity {κ a e L : ℝ}
    (he : e ≠ 0) (hL : L ≠ 0) (hκ : κ ≠ 0) :
    (16 / κ * (32 * a * e ^ 2) ^ 2 *
      (2 * ((256 * e⁻¹) / L) ^ 2) ^ 2) / κ =
      (16 * 32 ^ 2 * 4 * 256 ^ 4) * (a / (κ * L ^ 2)) ^ 2 := by
  field_simp
  ring

/-- The microscopic cancellation gives the F-to-the-minus-four gain. -/
theorem iterate_quadratic_stream_scale_bound {κ a e L C F : ℝ}
    (hκ : 0 < κ) (ha : 0 ≤ a) (he : e ≠ 0) (hL : 0 < L)
    (hC : 0 ≤ C) (hscale : a / (κ * L ^ 2) ≤ C / F ^ 2) :
    (16 / κ * (32 * a * e ^ 2) ^ 2 *
      (2 * ((256 * e⁻¹) / L) ^ 2) ^ 2) / κ ≤
      (16 * 32 ^ 2 * 4 * 256 ^ 4) * C ^ 2 / F ^ 4 := by
  rw [iterate_quadratic_stream_scale_identity he hL.ne' hκ.ne']
  have hs := (sq_le_sq₀ (by positivity : 0 ≤ a / (κ * L ^ 2))
    (by positivity : 0 ≤ C / F ^ 2)).mpr hscale
  have hm := mul_le_mul_of_nonneg_left hs
    (show (0 : ℝ) ≤ 16 * 32 ^ 2 * 4 * 256 ^ 4 by norm_num)
  convert hm using 1
  ring

end AVenhance.Infra.Section4
