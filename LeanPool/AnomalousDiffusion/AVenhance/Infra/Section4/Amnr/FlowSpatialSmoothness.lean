/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.FlowCurve

/-! All spatial orders of the actual flows on source cutoff windows. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory Set
namespace AVenhance.Infra.Section4
open AVenhance.Infra.Flow

/-- The actual previous flow is spatially smooth on every interval of the
source cutoff length. Invertibility is proved from the actual Jacobian rate given by the
    stream-regularity estimates. -/
theorem amnr_previous_flow_spatial_contDiff_infty_of_A3 {β C : ℝ}
    (I : AVenhance.Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : AVenhance.IsStreamSeq I Φ) (hreg : AVenhance.StreamRegularityBounds C I Φ)
    {m : ℕ} (hm : 1 ≤ m) (s t : ℝ)
    (ht : |t - s| ≤ AVenhance.tauPP β I.Λ m / 2 + AVenhance.tauP β I.Λ m) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => AVenhance.flow (AVenhance.streamVel (Φ (m - 1)))
      (hΦ.adm_pred m).vel_continuous (hΦ.adm_pred m).vel_lipschitz t x s) := by
  let A := AVenhance.a β I.Λ (m - 1)
  let M := (2 : ℝ) ^ 20 * A
  have hA : 0 < A := AVenhance.Infra.Cutoff.a_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have htime : |t - s| ≤ (2 : ℝ) ^ (-25 : ℤ) * A⁻¹ :=
    ht.trans (amnr_cutoff_window_fits_flow I hm)
  have hAd : A * |t - s| ≤ (2 : ℝ) ^ (-25 : ℤ) := by
    have hh := mul_le_mul_of_nonneg_left htime hA.le
    have heq : A * ((2 : ℝ) ^ (-25 : ℤ) * A⁻¹) = (2 : ℝ) ^ (-25 : ℤ) := by field_simp
    rwa [heq] at hh
  have hsmall : (max s t - min s t) * M < 1 := by
    rw [max_sub_min_eq_abs]
    have hh := mul_le_mul_of_nonneg_left hAd (show (0 : ℝ) ≤ 2 ^ 20 by positivity)
    have heq : (2 : ℝ) ^ 20 * (2 : ℝ) ^ (-25 : ℤ) = 1 / 32 := by norm_num
    rw [heq] at hh
    have hmid : |t - s| * M ≤ 1 / 32 := by convert hh using 1; dsimp [M]; ring
    exact hmid.trans_lt (by norm_num)
  exact amnr_flow_spatial_contDiff_infty_of_short
    (AVenhance.Infra.Construction.smoothPeriodic_streamVel (hΦ.adm_pred m))
    (AVenhance.flow_isFlow (AVenhance.streamVel (Φ (m - 1)))
      (hΦ.adm_pred m).vel_continuous (hΦ.adm_pred m).vel_lipschitz)
    hM (amnr_previous_velocityJacobian_norm_le_of_A3 I hΦ hreg hm)
    (min_le_max) ⟨min_le_left _ _, le_max_left _ _⟩ ⟨min_le_right _ _, le_max_right _ _⟩ hsmall

/-- Every spatial order of the forward flow is now proved on the
whole actual cutoff window, instead of supplied as a smoothness hypothesis. -/
theorem amnr_xFlow_spatial_contDiff_infty_of_A3 {β C : ℝ}
    (I : AVenhance.Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : AVenhance.IsStreamSeq I Φ) (hreg : AVenhance.StreamRegularityBounds C I Φ)
    {m : ℕ} (hm : 1 ≤ m) (l : ℤ) (t : ℝ)
    (ht : |t - (l : ℝ) * AVenhance.tauPP β I.Λ m| ≤
      AVenhance.tauPP β I.Λ m / 2 + AVenhance.tauP β I.Λ m) :
    ContDiff ℝ (⊤ : ℕ∞) (I.xFlow hΦ m l t) :=
  amnr_previous_flow_spatial_contDiff_infty_of_A3 I hΦ hreg hm
    ((l : ℝ) * AVenhance.tauPP β I.Λ m) t ht

/-- Every spatial order of the inverse flow follows by exchanging
its actual initial and target times in the same short-interval argument. -/
theorem amnr_xFlowInv_spatial_contDiff_infty_of_A3 {β C : ℝ}
    (I : AVenhance.Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : AVenhance.IsStreamSeq I Φ) (hreg : AVenhance.StreamRegularityBounds C I Φ)
    {m : ℕ} (hm : 1 ≤ m) (l : ℤ) (t : ℝ)
    (ht : |t - (l : ℝ) * AVenhance.tauPP β I.Λ m| ≤
      AVenhance.tauPP β I.Λ m / 2 + AVenhance.tauP β I.Λ m) :
    ContDiff ℝ (⊤ : ℕ∞) (I.xFlowInv hΦ m l t) :=
  amnr_previous_flow_spatial_contDiff_infty_of_A3 I hΦ hreg hm t
    ((l : ℝ) * AVenhance.tauPP β I.Λ m) (by simpa only [abs_sub_comm] using ht)

end AVenhance.Infra.Section4
