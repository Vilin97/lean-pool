/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.MaterialCalculus

/-! Physical spatial and material rates used by the mixed AMNR estimates. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4

/-- Ordered radius products are monotone in both nonnegative rates. -/
theorem amnrWeight_mono {S₁ H₁ S₂ H₂ : ℝ} (hS₁ : 0 ≤ S₁) (hH₁ : 0 ≤ H₁)
    (hS : S₁ ≤ S₂) (hH : H₁ ≤ H₂) (w : List (Option (Fin 2))) :
    amnrWeight S₁ H₁ w ≤ amnrWeight S₂ H₂ w := by
  induction w with
  | nil => exact le_rfl
  | cons d w ih =>
    change (match d with | none => H₁ | some _ => S₁) * amnrWeight S₁ H₁ w ≤
      (match d with | none => H₂ | some _ => S₂) * amnrWeight S₂ H₂ w
    cases d
    · exact mul_le_mul hH ih (amnrWeight_nonneg hS₁ hH₁ w) (hH₁.trans hH)
    · exact mul_le_mul hS ih (amnrWeight_nonneg hS₁ hH₁ w) (hS₁.trans hS)

/-- Abstract rpow comparison for the source's enlarged spatial radius. -/
theorem amnr_spatial_rate_le {E γ : ℝ} (hE : 0 < E) (hE1 : E ≤ 1) (hγ : 0 ≤ γ) :
    E⁻¹ ≤ E ^ (-(1 + γ / 2)) := by
  rw [← Real.rpow_neg_one]
  exact Real.rpow_le_rpow_of_exponent_ge hE hE1 (by linarith)

/-- The original flow rates are dominated by the actual AMNR radii. -/
theorem amnr_physical_rates {β : ℝ} (I : AVenhance.Ingredients β)
    {m : ℕ} (hm : 1 ≤ m) :
    (AVenhance.epsilon β I.Λ (m - 1))⁻¹ ≤
      AVenhance.epsilon β I.Λ (m - 1) ^ (-(1 + AVenhance.gamma β / 2)) ∧
    AVenhance.a β I.Λ (m - 1) ≤ (AVenhance.tauP β I.Λ m)⁻¹ := by
  constructor
  · exact amnr_spatial_rate_le
      (AVenhance.Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le)
      (AVenhance.Infra.Construction.epsilon_le_one I.one_lt_beta I.beta_lt I.two_pow_seven_le)
      (AVenhance.Infra.Ingredients.gamma_pos I.one_lt_beta I.beta_lt).le
  · exact amplitude_le_inverse_tauP I.one_lt_beta I.beta_lt I.two_pow_seven_le hm

/-- The whole closed large-cutoff support window lies inside the short-flow
interval required by the source flow derivative estimates. -/
theorem amnr_cutoff_window_fits_flow {β : ℝ} (I : AVenhance.Ingredients β)
    {m : ℕ} (hm : 1 ≤ m) :
    AVenhance.tauPP β I.Λ m / 2 + AVenhance.tauP β I.Λ m ≤
      (2 : ℝ) ^ (-25 : ℤ) * (AVenhance.a β I.Λ (m - 1))⁻¹ := by
  have hfit := AVenhance.Infra.Cutoff.four_tauP_le_tauPP
    I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m)
  have hτ := I.tauPP_pos' m
  have ha := AVenhance.Infra.Cutoff.a_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
    (m := m - 1)
  have he := AVenhance.Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
    (m := m - 1)
  have he1 := AVenhance.Infra.Construction.epsilon_le_one I.one_lt_beta I.beta_lt I.two_pow_seven_le
    (m := m - 1)
  have hd := AVenhance.Infra.Ingredients.delta_pos I.one_lt_beta I.beta_lt
  have hp := Real.rpow_le_one he.le he1 (show 0 ≤ 2 * AVenhance.delta β from by positivity)
  have hscale := (amplitude_tauPP_bounds I.one_lt_beta I.beta_lt I.two_pow_seven_le hm).2
  have hupper : AVenhance.a β I.Λ (m - 1) * AVenhance.tauPP β I.Λ m ≤
      (2 : ℝ) ^ (-25 : ℤ) := hscale.trans (by
        simpa only [mul_one] using
          (mul_le_mul_of_nonneg_left hp (show 0 ≤ (2 : ℝ) ^ (-25 : ℤ) from by positivity)))
  have hτupper : AVenhance.tauPP β I.Λ m ≤
      (2 : ℝ) ^ (-25 : ℤ) * (AVenhance.a β I.Λ (m - 1))⁻¹ := by
    rw [← div_eq_mul_inv]
    exact (le_div_iff₀ ha).mpr (by simpa only [mul_comm] using hupper)
  exact (show AVenhance.tauPP β I.Λ m / 2 + AVenhance.tauP β I.Λ m ≤
    AVenhance.tauPP β I.Λ m by linarith).trans hτupper

/-- The material cascade retains its source smallness factor. This stronger
comparison is needed before absorbing constants in the temperature estimate. -/
theorem amnr_material_rate_small {β : ℝ} (I : AVenhance.Ingredients β)
    {m : ℕ} (hm : 1 ≤ m) :
    AVenhance.a β I.Λ (m - 1) ≤
      (2 : ℝ) ^ (-27 : ℤ) *
        AVenhance.epsilon β I.Λ (m - 1) ^ (3 * AVenhance.delta β) *
          (AVenhance.tauP β I.Λ m)⁻¹ := by
  have hτ := AVenhance.Infra.Cutoff.tauP_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
    (m := m)
  rw [← div_eq_mul_inv]
  exact (le_div_iff₀ hτ).mpr
    (amplitude_tauP_bounds I.one_lt_beta I.beta_lt I.two_pow_seven_le hm).2

end AVenhance.Infra.Section4
