/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.MStar
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.LaterStart
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.TUpgradeConsumersPackaging

/-! # TUpgrade Consumers Scales

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4
open AVenhance

/-- A threshold chosen before ingredients enforces the T-upgrade smallness;
the starting index supplies its radius premise. -/
theorem iterate_contract_scales (β D : ℝ) (hD : 1 ≤ D) :
    ∃ C₁ : ℝ, ∀ I : Ingredients β, C₁ ≤ (I.Λ : ℝ) →
      ∀ R : ℝ, 0 < R → ∀ m : ℕ, mTheta0 β I.Λ R ≤ m →
        2 ≤ m ∧ epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2) ≤ R ∧
        epsilon β I.Λ (m - 1) ^ (2 * delta β) ≤ (4 * D ^ 3)⁻¹ := by
  by_cases hb : 1 < β ∧ β < 4 / 3
  · have hδ : 0 < 2 * delta β := mul_pos (by norm_num) (Infra.Ingredients.delta_pos hb.1 hb.2)
    refine ⟨(4 * D ^ 3) ^ (2 * delta β)⁻¹, ?_⟩
    intro I hΛ R hR m hm
    have hspec := Infra.Section5.mTheta0_spec I.one_lt_beta I.beta_lt I.two_pow_seven_le hR
    have hm2 := hspec.1.trans hm
    have he : 0 < epsilon β I.Λ (m - 1) :=
      Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
    have hΛpos : 0 < (I.Λ : ℝ) := by
      have hΛ := I.two_pow_seven_le
      exact_mod_cast (by omega : 0 < I.Λ)
    have hΛone : 1 ≤ (I.Λ : ℝ) := by
      have hΛ := I.two_pow_seven_le
      exact_mod_cast (by omega : 1 ≤ I.Λ)
    have hp : 0 < 1 + gamma β / 2 := by
      have hg := Infra.Ingredients.gamma_pos hb.1 hb.2
      linarith only [hg]
    have hradius := (Real.rpow_le_rpow he.le
      (Infra.Section5.RelativeError.epsilon_antitone I.one_lt_beta I.beta_lt I.two_pow_seven_le
        (show mTheta0 β I.Λ R - 1 ≤ m - 1 by omega)) hp.le).trans hspec.2
    have helambda : epsilon β I.Λ (m - 1) ≤ (I.Λ : ℝ)⁻¹ := by
      calc
        _ ≤ (I.Λ : ℝ) ^ (-((m - 1 : ℕ) : ℝ)) :=
          Infra.Ingredients.epsilon_le_lambda_pow I.one_lt_beta I.beta_lt I.two_pow_seven_le
        _ ≤ (I.Λ : ℝ) ^ (-1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hΛone (by
            have hi : (1 : ℝ) ≤ ((m - 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ m - 1 by omega)
            linarith only [hi])
        _ = _ := Real.rpow_neg_one _
    have hbase : 0 < 4 * D ^ 3 := by positivity
    have hpow : 4 * D ^ 3 ≤ (I.Λ : ℝ) ^ (2 * delta β) :=
      (Real.rpow_inv_le_iff_of_pos hbase.le hΛpos.le hδ).mp hΛ
    have hsmall : epsilon β I.Λ (m - 1) ^ (2 * delta β) ≤ (4 * D ^ 3)⁻¹ := by
      calc
        _ ≤ ((I.Λ : ℝ)⁻¹) ^ (2 * delta β) := Real.rpow_le_rpow he.le helambda hδ.le
        _ = ((I.Λ : ℝ) ^ (2 * delta β))⁻¹ := Real.inv_rpow hΛpos.le _
        _ ≤ _ := (inv_le_inv₀ (Real.rpow_pos_of_pos hΛpos _) hbase).mpr hpow
    exact ⟨hm2, hradius, hsmall⟩
  · exact ⟨0, fun I => False.elim (hb ⟨I.one_lt_beta, I.beta_lt⟩)⟩

end AVenhance.Infra.Section4
