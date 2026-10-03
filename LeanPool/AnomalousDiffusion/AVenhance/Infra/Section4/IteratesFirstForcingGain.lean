/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesCurrentCorrectedBudget

/-! # Iterates First Forcing Gain

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
namespace AVenhance.Infra.Section4

/-- The small first-step forcing remainder uses the q-squared Young budget;
 the centered forcing is treated separately by its half-square cancellation. -/
theorem iterate_first_remainder_forcing_gain {κ D L C Ccoef ρ q E g gF : ℝ}
    (hκ : 0 < κ) (hD : 0 ≤ D) (hC : 0 ≤ C) (hρ : 0 ≤ ρ) (hq : 0 < q)
    (hE : 0 ≤ E) (hscale : D * L ^ 2 ≤ C * q) (hρq : ρ ≤ q)
    (hprevious : κ * g ≤ E)
    (hforcing : gF ≤ 128 * κ * Ccoef ^ 2 * ρ ^ 2 * L ^ 4 * E) :
    (κ * q ^ 2) * g + D ^ 2 / (κ * q ^ 2) * gF ≤
      (1 + 128 * C ^ 2 * Ccoef ^ 2) * q ^ 2 * E := by
  have hs := (sq_le_sq₀ (mul_nonneg hD (sq_nonneg L)) (mul_nonneg hC hq.le)).mpr hscale
  have hρs := (sq_le_sq₀ hρ hq.le).mpr hρq
  have h1 : (κ * q ^ 2) * g ≤ q ^ 2 * E := by
    calc
      _ = q ^ 2 * (κ * g) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hprevious (sq_nonneg q)
  have h2 : D ^ 2 / (κ * q ^ 2) * gF ≤ 128 * C ^ 2 * Ccoef ^ 2 * q ^ 2 * E := by
    calc
      _ ≤ D ^ 2 / (κ * q ^ 2) * (128 * κ * Ccoef ^ 2 * ρ ^ 2 * L ^ 4 * E) :=
        mul_le_mul_of_nonneg_left hforcing (by positivity)
      _ = 128 * Ccoef ^ 2 * ρ ^ 2 * E * ((D * L ^ 2) ^ 2 / q ^ 2) := by field_simp
      _ ≤ 128 * Ccoef ^ 2 * ρ ^ 2 * E * ((C * q) ^ 2 / q ^ 2) :=
        mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right hs (sq_nonneg q)) (by positivity)
      _ = 128 * C ^ 2 * Ccoef ^ 2 * E * ρ ^ 2 := by field_simp
      _ ≤ 128 * C ^ 2 * Ccoef ^ 2 * E * q ^ 2 :=
        mul_le_mul_of_nonneg_left hρs (by positivity)
      _ = _ := by ring
  nlinarith only [h1, h2]

end AVenhance.Infra.Section4
