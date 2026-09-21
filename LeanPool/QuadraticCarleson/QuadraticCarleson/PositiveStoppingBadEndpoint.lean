/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.PositiveStoppingBadAction

/-! # Full-real oscillatory endpoint bound for the canonical bad part -/

open MeasureTheory Set
open scoped ENNReal NNReal Function

namespace QuadraticCarleson
namespace PositiveStoppingBadEstimate

open CalderonZygmundDyadicStopping CalderonZygmundStoppingIntervals
open PositiveEndpointOptimization PositiveLevelIntegration
open PositiveHighHeightEstimate PositiveLowFullEstimate OscillatoryReduction

theorem fullHighMajorant_sq_lintegral_le_orlicz
    {ι : Type*} [Countable ι] {f : ℝ → ℂ} (hf : Measurable f) (hfi : Integrable f)
    (z R : ι → ℝ) (hR : ∀ i, 0 < R i)
    (hdisj : Pairwise (Disjoint on fun i ↦ centeredInterval (z i) (R i))) :
    (∫⁻ x, highContributionMajorant fullHighCutoff
      (fun k ↦ disjointLevelAtomSum fullAmplitude f k z R) x ^ 2) ≤
      fullHighEndpointConstant * ∫⁻ x, ENNReal.ofReal (‖f x‖ * paperLog 1 ‖f x‖) := by
  have he := highContributionMajorant_eLpNorm_le fullHighCutoff
    (fun k ↦ memLp_disjointLevelAtomSum hf hfi (fullAmplitude_pos k).le z R hR hdisj)
  have hb : eLpNorm (highContributionMajorant fullHighCutoff
      (fun k ↦ disjointLevelAtomSum fullAmplitude f k z R)) 2 ≤
      highHeightTailConstant * ∑' k : ℕ,
        ENNReal.ofReal ((2 : ℝ) ^ (-((fullHighCutoff k : ℕ) : ℝ) / 10)) *
          (ENNReal.ofReal (4 * fullAmplitude k) * magnitudeLevelL1Mass volume fullAmplitude f k) ^
            (1 / 2 : ℝ) := by
    apply he.trans
    apply mul_le_mul' le_rfl
    exact ENNReal.tsum_le_tsum (fun k ↦ mul_le_mul' le_rfl
      (disjointLevelAtomSum_eLpNorm_le hf (fullAmplitude_pos k).le z R hR hdisj))
  have hs := pow_le_pow_left₀ bot_le hb 2
  have hm := measurable_highContributionMajorant fullHighCutoff
    (fun k ↦ memLp_disjointLevelAtomSum hf hfi (fullAmplitude_pos k).le z R hR hdisj)
  rw [eLpNorm_two_sq_lintegral _ hm.aestronglyMeasurable] at hs
  simp only [enorm_eq_self, mul_pow] at hs
  have hw := weighted_level_sum_sq_le fullAmplitude
    (fun k ↦ (2 : ℝ) ^ (-((fullHighCutoff k : ℕ) : ℝ) / 10)) (fullCutoff 20)
    (magnitudeLevelL1Mass volume fullAmplitude f) (fun k ↦ (fullAmplitude_pos k).le)
    (fun _ ↦ by positivity)
    (fun k ↦ by unfold fullCutoff; exact mul_pos (by norm_num) (dyadicScale_pos k))
  have hp (k : ℕ) : ((2 : ℝ) ^ (-((fullHighCutoff k : ℕ) : ℝ) / 10)) ^ 2 =
      (2 : ℝ) ^ (-((fullHighCutoff k : ℕ) : ℝ) / 5) := by
    rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  simp only [hp] at hw
  rw [tsum_fullHighPrefactor] at hw
  have hm : (∑' k : ℕ, ENNReal.ofReal (fullCutoff 20 k) *
      magnitudeLevelL1Mass volume fullAmplitude f k) ≤
      80 * ∫⁻ x, ENNReal.ofReal (‖f x‖ * paperLog 1 ‖f x‖) := by
    have h := tsum_full_weight_mul_levelMass_le_orlicz volume (C := 20) (by norm_num) hf
    norm_num only [show (4 : ℝ) * 20 = 80 by norm_num] at h
    simp_rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 80)] at h
    rw [lintegral_const_mul' _ _ (by finiteness)] at h
    simpa only [ENNReal.ofReal_ofNat] using h
  apply hs.trans
  apply (mul_le_mul' le_rfl hw).trans
  apply (mul_le_mul' le_rfl (mul_le_mul' le_rfl hm)).trans_eq
  unfold fullHighEndpointConstant
  ring

theorem tsum_stoppingLength_le_lintegral_norm {f : ℝ → ℂ} (hfi : Integrable f) :
    (∑' c : stoppingCell f, ENNReal.ofReal (stoppingLength c)) ≤ ∫⁻ x, ‖f x‖ₑ := by
  have h := tsum_volume_stoppingCell_le_lintegral_norm hfi
  simp_rw [← centeredInterval_eq_stoppingInterval, volume_centeredStoppingInterval] at h
  simpa only [ofReal_norm] using h

theorem lintegral_norm_le_full_orlicz (f : ℝ → ℂ) :
    (∫⁻ x, ‖f x‖ₑ) ≤ ∫⁻ x, ENNReal.ofReal (‖f x‖ * paperLog 1 ‖f x‖) := by
  apply lintegral_mono
  intro x
  dsimp only
  rw [← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal
    (le_mul_of_one_le_right (norm_nonneg _)
      (PositiveEndpointOptimization.one_le_paperLog_one (norm_nonneg _)))

noncomputable def stoppingBadOscillatoryConstant : ℝ≥0∞ :=
  5 + 2 * fullLowEndpointConstant + 4 * fullHighEndpointConstant

theorem stoppingBadOscillatoryConstant_lt_top : stoppingBadOscillatoryConstant < ∞ := by
  unfold stoppingBadOscillatoryConstant
  exact ENNReal.add_lt_top.mpr ⟨ENNReal.add_lt_top.mpr ⟨by finiteness,
    ENNReal.mul_lt_top (by finiteness) fullLowEndpointConstant_lt_top⟩,
    ENNReal.mul_lt_top (by finiteness) fullHighEndpointConstant_lt_top⟩

theorem half_levelSet_measure_le_two_lintegral {F : ℝ → ℝ≥0∞} (hF : Measurable F) :
    volume {x | (1/2 : ℝ≥0∞) < F x} ≤ 2 * ∫⁻ x, F x := by
  have hm := mul_meas_ge_le_lintegral (μ := volume) hF (1/2)
  calc
    _ ≤ volume {x | (1/2 : ℝ≥0∞) ≤ F x} :=
      measure_mono (fun x (hx : (1/2 : ℝ≥0∞) < F x) ↦ hx.le)
    _ = 2 * ((1/2 : ℝ≥0∞) * volume {x | (1/2 : ℝ≥0∞) ≤ F x}) := by
      rw [← mul_assoc, one_div, ENNReal.mul_inv_cancel (by norm_num) (by finiteness), one_mul]
    _ ≤ _ := mul_le_mul' le_rfl hm

theorem half_levelSet_measure_le_four_sq_lintegral {F : ℝ → ℝ≥0∞} (hF : Measurable F) :
    volume {x | (1/2 : ℝ≥0∞) < F x} ≤ 4 * ∫⁻ x, F x ^ 2 := by
  have hm := mul_meas_ge_le_lintegral (μ := volume) (hF.pow_const 2) ((1/2 : ℝ≥0∞)^2)
  calc
    _ ≤ volume {x | (1/2 : ℝ≥0∞)^2 ≤ F x ^ 2} :=
      measure_mono (fun x hx ↦ pow_le_pow_left₀ bot_le hx.le 2)
    _ = 4 * (((1/2 : ℝ≥0∞)^2) * volume {x | (1/2 : ℝ≥0∞)^2 ≤ F x ^ 2}) := by
      rw [← mul_assoc, show (4 : ℝ≥0∞) = 2 ^ 2 by norm_num, ← mul_pow, one_div,
        ENNReal.mul_inv_cancel (by norm_num) (by finiteness), one_pow, one_mul]
    _ ≤ _ := mul_le_mul' le_rfl hm

/-- The normalized full-real oscillatory endpoint bound for the actual
canonical bad part. No decomposition or operator identity is assumed. -/
theorem stoppingBadPart_oscillatory_levelSet_le_orlicz
    {f : ℝ → ℂ} (hf : Measurable f) (hfi : Integrable f) :
    volume {x | 1 < paperOscillatoryMaximal (stoppingBadPart f) x} ≤
      stoppingBadOscillatoryConstant *
        ∫⁻ x, ENNReal.ofReal (‖f x‖ * paperLog 1 ‖f x‖) := by
  let z := stoppingCenter (f := f)
  let R := stoppingLength (f := f)
  let E := fivefoldExceptionalSet z R
  let L := fullLowMajorant f z R
  let H := highContributionMajorant fullHighCutoff (stoppingLevelBadPart f)
  have hR : ∀ c, 0 < R c := stoppingLength_pos
  have hd : Pairwise (Disjoint on fun c ↦ centeredInterval (z c) (R c)) :=
    centeredStoppingIntervals_pairwiseDisjoint
  have hp (x : ℝ) (hx : x ∉ E) :
      paperOscillatoryMaximal (stoppingBadPart f) x ≤ L x + H x := by
    apply (paperOscillatoryMaximal_stoppingBadPart_le_low_add_high hf hfi x).trans
    apply add_le_add
    · rw [← paperFullLowContribution_eq_heightContribution hf hfi z R hR hd]
      exact paperFullLowContribution_le_majorant hf hfi z R hR hd hx
    · exact paperHighContribution_le_majorant _ _ x
  have hset : {x | 1 < paperOscillatoryMaximal (stoppingBadPart f) x} ⊆
      E ∪ ({x | (1/2 : ℝ≥0∞) < L x} ∪ {x | (1/2 : ℝ≥0∞) < H x}) := by
    intro x hx
    by_cases he : x ∈ E
    · exact Or.inl he
    apply Or.inr
    by_cases hl : (1/2 : ℝ≥0∞) < L x
    · exact Or.inl hl
    apply Or.inr
    by_contra hh
    have hle := add_le_add (le_of_not_gt hl) (le_of_not_gt hh)
    simp only [one_div, ENNReal.inv_two_add_inv_two] at hle
    exact (not_lt_of_ge ((hp x he).trans hle)) hx
  have hL := (half_levelSet_measure_le_two_lintegral (measurable_fullLowMajorant f z R)).trans
    (mul_le_mul' le_rfl (lintegral_fullLowMajorant_le_orlicz hf z R hR hd))
  have hHm : Measurable H := measurable_highContributionMajorant fullHighCutoff
    (fun k ↦ memLp_disjointLevelAtomSum hf hfi (fullAmplitude_pos k).le z R hR hd)
  have hH := (half_levelSet_measure_le_four_sq_lintegral hHm).trans
    (mul_le_mul' le_rfl (fullHighMajorant_sq_lintegral_le_orlicz hf hfi z R hR hd))
  have hE : volume E ≤ 5 * ∫⁻ x, ENNReal.ofReal (‖f x‖ * paperLog 1 ‖f x‖) :=
    (volume_fivefoldExceptionalSet_le z R).trans
      (mul_le_mul' le_rfl ((tsum_stoppingLength_le_lintegral_norm hfi).trans
        (lintegral_norm_le_full_orlicz f)))
  apply (measure_mono hset).trans
  apply (measure_union_le _ _).trans
  apply (add_le_add le_rfl (measure_union_le _ _)).trans
  apply (add_le_add hE (add_le_add hL hH)).trans_eq
  unfold stoppingBadOscillatoryConstant
  ring

end PositiveStoppingBadEstimate
end QuadraticCarleson
