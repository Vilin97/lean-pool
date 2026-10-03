/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesDiffusiveMaterialScale

/-! # Iterates Homogeneous Previous Scale

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
namespace AVenhance.Infra.Section4

/-- Normalize the homogeneous previous-material contribution at q squared. -/
theorem iterate_homogeneous_previous_material_scale_bound (n : ℕ)
    {κ D L Cs q H N : ℝ} (hκ : 0 < κ) (hD : 0 ≤ D) (hL : 0 < L)
    (hCs : 0 ≤ Cs) (hq : 0 ≤ q) (hH : 0 ≤ H)
    (hscale : D * L ^ 2 ≤ Cs * q) :
    24 * D ^ 2 / κ * (H * κ ^ 2 * (N / Real.sqrt κ) ^ 2 *
      (((n + 2).factorial : ℝ) * L ^ (n + 2)) ^ 2) ≤
      24 * Cs ^ 2 * H * q ^ 2 * N ^ 2 * (((n + 2).factorial : ℝ) * L ^ n) ^ 2 := by
  have hs := (sq_le_sq₀ (by positivity) (by positivity)).mpr hscale
  have hn := iterate_diffusive_material_normalization (N := N) hκ
  calc
    _ = 24 * H * (D * L ^ 2) ^ 2 * N ^ 2 *
        (((n + 2).factorial : ℝ) * L ^ n) ^ 2 := by
      rw [show H * κ ^ 2 * (N / Real.sqrt κ) ^ 2 = H * (κ ^ 2 * (N / Real.sqrt κ) ^ 2) by ring, hn]
      simp only [pow_add]
      field_simp
    _ ≤ _ := by
      have ht := mul_le_mul_of_nonneg_right hs
        (by positivity : 0 ≤ 24 * H * N ^ 2 * (((n + 2).factorial : ℝ) * L ^ n) ^ 2)
      nlinarith only [ht]

end AVenhance.Infra.Section4
