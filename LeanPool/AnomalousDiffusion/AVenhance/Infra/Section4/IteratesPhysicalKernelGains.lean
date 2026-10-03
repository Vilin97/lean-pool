/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesPhysicalBudgetScales

/-! # Iterates Physical Kernel Gains

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
namespace AVenhance.Infra.Section4

/-- Literal diffusivity scaling supplies both stream kernels, including all
absolute losses from the actual terminal norm estimate. -/
theorem iterate_physical_stream_kernel_gains {a e γ κ c L F : ℝ}
    (ha : 0 ≤ a) (he : 0 < e) (hκ : 0 < κ) (hc : 0 < c)
    (hL : 0 < L) (hFp : 0 < F)
    (hlower : c * (a * e ^ (2 + γ)) ≤ κ)
    (hF : F = e ^ (1 + γ / 2) * L) :
    ((24 * (2 * ((2 : ℝ) ^ 19 * a) / L ^ 2)) / κ ≤
      (48 * (2 : ℝ) ^ 19 / c) / F ^ 2) ∧
    ((24 * (16 / κ * (32 * a * e ^ 2) ^ 2 * (2 * ((256 * e⁻¹) / L) ^ 2) ^ 2)) / κ ≤
      (24 * (16 * 32 ^ 2 * 4 * 256 ^ 4) / c ^ 2) / F ^ 4) := by
  have hr := iterate_stream_ratio_of_literal_lower he hκ hc hL hFp hlower hF
  have hu := mul_le_mul_of_nonneg_left hr (show (0 : ℝ) ≤ 48 * 2 ^ 19 by norm_num)
  have hv := iterate_quadratic_stream_scale_bound hκ ha he.ne' hL
    (show 0 ≤ (1 : ℝ) / c by positivity) hr
  have hv24 := mul_le_mul_of_nonneg_left hv (show (0 : ℝ) ≤ 24 by norm_num)
  constructor
  · convert hu using 1 <;> ring
  · convert hv24 using 1 <;> ring

/-- The linear material kernel keeps the primitive gain, after using the
proved amplitude-times-period estimate. -/
theorem iterate_physical_linear_kernel_gain {κ τ K a e H ρ : ℝ}
    (hκ : 0 < κ) (hK : 0 ≤ K) (he : e ≠ 0) (htime : τ * a ≤ H * ρ) :
    (24 * (8 * (2 * τ * K * κ) * (8192 * a * e) * (256 * e⁻¹))) / κ ≤
      (24 * 8 * 2 * K * (2 : ℝ) ^ 21 * H) * ρ := by
  have hb := iterate_primitive_amplitude_scale hκ hK htime
  have hm := mul_le_mul_of_nonneg_left hb
    (show (0 : ℝ) ≤ 24 * 8 * (2 : ℝ) ^ 21 by norm_num)
  have heq : (24 * (8 * (2 * τ * K * κ) * (8192 * a * e) * (256 * e⁻¹))) / κ =
      (24 * 8 * (2 : ℝ) ^ 21) * ((2 * τ * K * κ) * a / κ) := by
    have hv := iterate_velocity_first_jet_scale (a := a) he
    calc
      _ = 24 * 8 * (2 * τ * K * κ) * ((8192 * a * e) * (256 * e⁻¹)) / κ := by ring
      _ = _ := by rw [hv]; ring
  rw [heq]
  convert hm using 1
  ring

end AVenhance.Infra.Section4
