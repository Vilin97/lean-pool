/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.TemperatureMaterialStepL2

/-! Abstract real normalization of the material gradient PDE estimate. -/

@[expose] public section

namespace AVenhance.Infra.Section4

theorem amnr_material_gradient_rate_le {κ S H G K Cb Ccoeff Cd D W : ℝ}
    (hK : 0 ≤ K) (hG : 0 ≤ G) (hC : 0 ≤ Ccoeff) (_hCd : 0 ≤ Cd)
    (hD : 0 ≤ D) (hW : 0 ≤ W) (hH : 0 ≤ H)
    (hRate : κ * S ^ 2 ≤ Cd * H) :
    (((2 * κ * K * G + 2 * K * (D * (Ccoeff * κ) * G)) * S ^ 2 +
      D * Cb * H * G) * W) ≤
      (1 + 2 * Cd * K * (1 + D * Ccoeff) + D * Cb) * G * (W * H) := by
  have hh := mul_le_mul_of_nonneg_right hRate
    (show 0 ≤ 2 * K * G * (1 + D * Ccoeff) by positivity)
  have hhW := mul_le_mul_of_nonneg_right hh hW
  have hExtra : 0 ≤ G * W * H := by positivity
  nlinarith only [hhW, hExtra]

end AVenhance.Infra.Section4
