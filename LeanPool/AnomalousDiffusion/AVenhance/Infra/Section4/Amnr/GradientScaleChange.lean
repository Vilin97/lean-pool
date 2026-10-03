/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.SourceJetLevels

/-! Coarse-to-fine rate conversion for actual lower gradient levels. -/

@[expose] public section

noncomputable section
namespace AVenhance.Infra.Section4

theorem amnr_gradient_material_spatial_scale {E β : ℝ} (hE : 0 < E) (k r : ℕ) :
    E ^ (β - 2) * E⁻¹ ^ k * (E ^ (β - 2)) ^ r =
      E ^ ((β - 2) * ((r : ℝ) + 1) - (k : ℝ)) := by
  rw [← Real.rpow_natCast (E ^ (β - 2)) r, ← Real.rpow_mul hE.le,
    ← Real.rpow_natCast E⁻¹ k, ← Real.rpow_neg_one,
    ← Real.rpow_mul hE.le, ← Real.rpow_add hE, ← Real.rpow_add hE]
  congr 1
  ring

theorem amnr_gradient_material_scale_antitone {E F β : ℝ} (hE : 0 < E)
    (hF : 0 < F) (hEF : E ≤ F) (hβ : β < 4 / 3) (k r : ℕ) :
    F ^ (β - 2) * F⁻¹ ^ k * (F ^ (β - 2)) ^ r ≤
      E ^ (β - 2) * E⁻¹ ^ k * (E ^ (β - 2)) ^ r := by
  rw [amnr_gradient_material_spatial_scale hF, amnr_gradient_material_spatial_scale hE]
  apply Real.rpow_le_rpow_of_nonpos hE hEF
  have hβ2 : β - 2 ≤ 0 := by linarith
  have hprod := mul_nonpos_of_nonpos_of_nonneg hβ2
    (show (0 : ℝ) ≤ (r : ℝ) + 1 by positivity)
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  linarith

theorem amnr_epsilon_current_le_prev {β : ℝ} (I : AVenhance.Ingredients β)
    {m : ℕ} (hm : 1 ≤ m) :
    AVenhance.epsilon β I.Λ m ≤ AVenhance.epsilon β I.Λ (m - 1) := by
  have hE := AVenhance.Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m)
  have hF := AVenhance.Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m
      - 1)
  exact (inv_le_inv₀ hF hE).mp (amnr_epsilon_inverse_prev_le_current I hm)

end AVenhance.Infra.Section4
