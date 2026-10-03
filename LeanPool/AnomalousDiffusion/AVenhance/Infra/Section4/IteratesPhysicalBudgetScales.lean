/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesStreamPhysical
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesStreamBudgetScales

/-! # Iterates Physical Budget Scales

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
namespace AVenhance.Infra.Section4

/-- The analytic radius converts the literal diffusivity power to F squared. -/
theorem iterate_diffusive_radius_square {e γ L F : ℝ}
    (he : 0 < e) (hF : F = e ^ (1 + γ / 2) * L) :
    e ^ (2 + γ) * L ^ 2 = F ^ 2 := by
  rw [hF, mul_pow, ← Real.rpow_mul_natCast he.le]
  congr 1
  congr 1
  push_cast
  ring

/-- Literal lower diffusivity scaling gives the reciprocal analytic gain. -/
theorem iterate_stream_ratio_of_literal_lower {a e γ κ c L F : ℝ}
    (he : 0 < e) (hκ : 0 < κ) (hc : 0 < c) (hL : 0 < L) (hFpos : 0 < F)
    (hlower : c * (a * e ^ (2 + γ)) ≤ κ)
    (hF : F = e ^ (1 + γ / 2) * L) :
    a / (κ * L ^ 2) ≤ 1 / c / F ^ 2 := by
  have hb := mul_le_mul_of_nonneg_right hlower (sq_nonneg L)
  have hr := iterate_diffusive_radius_square he hF
  have hb' : a * (c * F ^ 2) ≤ κ * L ^ 2 := by
    calc
      _ = c * a * (e ^ (2 + γ) * L ^ 2) := by rw [hr]; ring
      _ ≤ _ := by
        convert hb using 1
        ring
  calc
    _ ≤ 1 / (c * F ^ 2) := (div_le_div_iff₀ (by positivity) (by positivity)).mpr (by simpa using
        hb')
    _ = _ := by ring

/-- The explicit primitive has the q gain from upper diffusivity scaling
and the proved amplitude-times-period bound. -/
theorem iterate_primitive_radius_scale {a e γ κ τ K Ck H ρ L F : ℝ}
    (he : 0 < e) (hτ : 0 ≤ τ) (hK : 0 ≤ K) (hCk : 0 ≤ Ck)
    (hupper : κ ≤ Ck * (a * e ^ (2 + γ))) (htime : τ * a ≤ H * ρ)
    (hF : F = e ^ (1 + γ / 2) * L) :
    (2 * τ * K * κ) * L ^ 2 ≤ (2 * K * Ck * H) * (ρ * F ^ 2) := by
  have hb := mul_le_mul_of_nonneg_right hupper (sq_nonneg L)
  have hr := iterate_diffusive_radius_square he hF
  have hb' : κ * L ^ 2 ≤ Ck * a * F ^ 2 := by
    calc
      _ ≤ Ck * a * (e ^ (2 + γ) * L ^ 2) := by
        convert hb using 1
        ring
      _ = _ := by rw [hr]
  have h1 := mul_le_mul_of_nonneg_left hb' (show 0 ≤ 2 * τ * K by positivity)
  have h2 := mul_le_mul_of_nonneg_left htime (show 0 ≤ 2 * K * Ck * F ^ 2 by positivity)
  nlinarith only [h1, h2]

/-- The material primitive factor cancels the diffusivity exactly. -/
theorem iterate_primitive_amplitude_scale {κ τ K a H ρ : ℝ}
    (hκ : 0 < κ) (hK : 0 ≤ K) (htime : τ * a ≤ H * ρ) :
    (2 * τ * K * κ) * a / κ ≤ 2 * K * H * ρ := by
  have hb := mul_le_mul_of_nonneg_left htime (show 0 ≤ 2 * K by positivity)
  have heq : (2 * τ * K * κ) * a / κ = 2 * K * (τ * a) := by field_simp
  rw [heq]
  simpa only [mul_assoc] using hb

/-- Exact positive first-velocity-jet scale supplied by stream-regularity. -/
theorem iterate_velocity_first_jet_scale {a e : ℝ} (he : e ≠ 0) :
    (8192 * a * e) * (256 * e⁻¹) = (2 : ℝ) ^ 21 * a := by
  field_simp
  ring

end AVenhance.Infra.Section4
