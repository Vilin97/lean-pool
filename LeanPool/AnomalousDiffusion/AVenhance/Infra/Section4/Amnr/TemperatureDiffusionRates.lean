/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.TemperatureCoefficientBounds

/-! Abstract scalar rate algebra used by the temperature energy cascade. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4

/-- The source spatial radius cancels the extra diffusivity power exactly. -/
theorem amnr_diffusivity_radius_identity {E : ℝ} (hE : 0 < E) (A γ : ℝ) :
    (A * E ^ (2 + γ)) * (E ^ (-(1 + γ / 2))) ^ 2 = A := by
  have hpow : (E ^ (-(1 + γ / 2))) ^ 2 = E ^ (-(2 + γ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hE.le]
    congr 1
    norm_num
    ring
  rw [hpow, mul_assoc, ← Real.rpow_add hE]
  simp

/-- The upper diffusivity-recursion estimate supplies the material diffusion rate. -/
theorem amnr_diffusion_rate_le {E A κ C H γ : ℝ} (hE : 0 < E)
    (hκ : κ ≤ C * (A * E ^ (2 + γ))) (hA : A ≤ H) (hC : 0 ≤ C) :
    κ * (E ^ (-(1 + γ / 2))) ^ 2 ≤ C * H := by
  have hh := mul_le_mul_of_nonneg_right hκ (sq_nonneg (E ^ (-(1 + γ / 2))))
  rw [mul_assoc, amnr_diffusivity_radius_identity hE] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left hA hC)

end AVenhance.Infra.Section4
