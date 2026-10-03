/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesDiffusion

/-! Corrected quantitative current-material allocation. -/

@[expose] public section

namespace AVenhance.Infra.Section4

/-- Allocate the current forcing with κq. The forcing and preceding-gradient
 contributions retain q, while transferred diffusion contributes q squared.
 This is scalar budget algebra; the actual forcing bound is proved separately. -/
theorem iterate_current_material_corrected_remainder_gain
    {κ D C H q L E g gLap gF : ℝ}
    (hκ : 0 < κ) (hD : 0 ≤ D) (hC : 0 ≤ C) (hH : 0 ≤ H)
    (hq : 0 < q) (hE : 0 ≤ E) (hscale : D * L ^ 2 ≤ C * q)
    (hprevious : κ * g ≤ E) (hLap : κ * gLap ≤ L ^ 4 * E)
    (hforcing : gF ≤ κ * H * L ^ 4 * E) :
    24 * κ * D ^ 2 * gLap + (κ * q) * g + D ^ 2 / (κ * q) * gF ≤
      (24 * C ^ 2 * q ^ 2 + (1 + C ^ 2 * H) * q) * E := by
  have hs : (D * L ^ 2) ^ 2 ≤ (C * q) ^ 2 :=
    (sq_le_sq₀ (mul_nonneg hD (sq_nonneg L)) (mul_nonneg hC hq.le)).mpr hscale
  have h₁ : 24 * κ * D ^ 2 * gLap ≤ 24 * C ^ 2 * q ^ 2 * E := by
    calc
      _ = (24 * D ^ 2) * (κ * gLap) := by ring
      _ ≤ (24 * D ^ 2) * (L ^ 4 * E) := mul_le_mul_of_nonneg_left hLap (by positivity)
      _ = 24 * (D * L ^ 2) ^ 2 * E := by ring
      _ ≤ 24 * (C * q) ^ 2 * E :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs (by norm_num)) hE
      _ = _ := by ring
  have h₂ : (κ * q) * g ≤ q * E := by
    simpa only [mul_assoc, mul_comm κ q] using mul_le_mul_of_nonneg_left hprevious hq.le
  have h₃ : D ^ 2 / (κ * q) * gF ≤ C ^ 2 * H * q * E := by
    calc
      _ ≤ D ^ 2 / (κ * q) * (κ * H * L ^ 4 * E) :=
        mul_le_mul_of_nonneg_left hforcing (by positivity)
      _ = (D * L ^ 2) ^ 2 / q * H * E := by field_simp
      _ ≤ (C * q) ^ 2 / q * H * E :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hs hq.le) hH) hE
      _ = _ := by field_simp
  nlinarith only [h₁, h₂, h₃]

end AVenhance.Infra.Section4
