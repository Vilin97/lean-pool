/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesSourceRadius

/-! # Iterates TSource Scale

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
namespace AVenhance.Infra.Section4

/-- The original T radius condition collapses both maxima to the coarse scale. -/
theorem iterate_T_source_scale {e γ R C₀ ρ : ℝ}
    (he : 0 < e) (hR : 0 < R) (hC : 1 ≤ C₀)
    (hscale : e ^ (1 + γ / 2) ≤ R)
    (hsmall : ρ ≤ (4 * C₀ ^ 3)⁻¹) :
    max 1 (e ^ (2 + γ) * R ^ (-2 : ℤ)) = 1 ∧
    max (C₀ * e ^ (-1 - γ / 2)) (C₀ / R) = C₀ * e ^ (-1 - γ / 2) ∧
    C₀ ^ 3 * ρ ≤ 1 / 4 := by
  have hCp : 0 < C₀ := by linarith only [hC]
  have hrp : 0 < e ^ (1 + γ / 2) := Real.rpow_pos_of_pos he _
  have hid : e ^ (2 + γ) = (e ^ (1 + γ / 2)) ^ 2 := by
    rw [← Real.rpow_mul_natCast he.le]
    congr 1
    push_cast
    ring
  have hs := pow_le_pow_left₀ hrp.le hscale 2
  have hmax : e ^ (2 + γ) * R ^ (-2 : ℤ) ≤ 1 := by
    rw [hid, zpow_neg, zpow_two, ← pow_two]
    rw [mul_inv_le_iff₀ (sq_pos_of_pos hR)]
    simpa only [one_mul] using hs
  have hneg : e ^ (-1 - γ / 2) = (e ^ (1 + γ / 2))⁻¹ := by
    rw [← Real.rpow_neg he.le]
    congr 1
    ring
  have hinv := (inv_le_inv₀ hR hrp).mpr hscale
  have hrad : C₀ / R ≤ C₀ * e ^ (-1 - γ / 2) := by
    rw [hneg, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hinv hCp.le
  refine ⟨max_eq_left hmax, max_eq_left hrad, ?_⟩
  have hm := mul_le_mul_of_nonneg_left hsmall (show 0 ≤ C₀ ^ 3 by positivity)
  have heq : C₀ ^ 3 * (4 * C₀ ^ 3)⁻¹ = (1 : ℝ) / 4 := by field_simp
  exact hm.trans_eq heq

/-- The printed enlarged T frequency dominates the finite-sum frequency. -/
theorem iterate_T_frequency_bound {C₀ E : ℝ} (hC : 1 ≤ C₀) (hE : 0 ≤ E) :
    4 * (C₀ * E) ≤ (4 * C₀ ^ 3) * E := by
  have hp : C₀ ≤ C₀ ^ 3 := by
    have h := pow_le_pow_right₀ hC (by norm_num : 1 ≤ (3 : ℕ))
    simpa only [pow_one] using h
  have hm := mul_le_mul_of_nonneg_right hp (by positivity : 0 ≤ 4 * E)
  nlinarith only [hm]

end AVenhance.Infra.Section4
