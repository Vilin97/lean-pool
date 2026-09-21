/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.LacunaryLowAssembly
import LeanPool.QuadraticCarleson.QuadraticCarleson.PositiveFullOscillatoryEndpoint

/-!
# Canonical lacunary oscillatory endpoint assembly

The source's low and high terms are connected to the actual all-height
oscillatory action of the canonical bad part. Combining this with the genuine
good-part estimate gives a universal-threshold endpoint for the original
input. The individual frozen-block weak bound is the sole conditional
analytic input; no operator decomposition is assumed.
-/

open MeasureTheory Set
open scoped ENNReal

namespace QuadraticCarleson
namespace LacunaryOscillatoryAssembly

open CalderonZygmundDyadicStopping CalderonZygmundStoppingIntervals
open CanonicalScaleAtoms PositiveStoppingBadEstimate PositiveGoodOscillatory
open PositiveFullOscillatoryEndpoint OscillatoryReduction
open PositiveEndpointOptimization PositiveLevelIntegration PositiveHighHeightEstimate
open PositiveLowFullEstimate LacunaryMiddleKalton LacunaryLowAssembly
open LacunaryMiddleFinalSummation


theorem tsum_lintegral_enorm_lacunaryStoppingLevels_le
    {f : ℝ → ℂ} (hf : Measurable f) :
    (∑' k : ℕ, ∫⁻ x, ‖lacunaryStoppingLevelBadPart f k x‖ₑ) ≤
      2 * ∫⁻ x, ‖f x‖ₑ := by
  simpa only [tsum_lintegral_enorm_stoppingScaleLevelBadPart hf,
    lacunaryStoppingLevelBadPart] using tsum_lacunary_scale_level_L1Mass_le hf

theorem tsum_lintegral_enorm_highPass_lacunaryStoppingLevels_lt_top
    {f : ℝ → ℂ} (hf : Measurable f) (hfi : Integrable f)
    (lam : ℝ) (hlam : lam ≠ 0) (x : ℝ) :
    (∑' k : ℕ, ∫⁻ y,
      ‖highPassKernel lam hlam (x-y) * lacunaryStoppingLevelBadPart f k y‖ₑ) < ∞ := by
  have hp (k : ℕ) :
      (∫⁻ y, ‖highPassKernel lam hlam (x-y) * lacunaryStoppingLevelBadPart f k y‖ₑ) ≤
        ENNReal.ofReal (2 / innerRadius lam hlam) *
          ∫⁻ y, ‖lacunaryStoppingLevelBadPart f k y‖ₑ := by
    calc
      _ ≤ ∫⁻ y, ENNReal.ofReal (2 / innerRadius lam hlam) *
          ‖lacunaryStoppingLevelBadPart f k y‖ₑ := by
        apply lintegral_mono
        intro y
        dsimp only
        rw [enorm_mul]
        exact mul_le_mul' (by
          simpa only [← ofReal_norm] using ENNReal.ofReal_le_ofReal
            (highPassKernel_norm_le lam hlam (x-y))) le_rfl
      _ = _ := lintegral_const_mul' _ _ (by finiteness)
  have hs := ENNReal.tsum_le_tsum hp
  rw [ENNReal.tsum_mul_left] at hs
  exact hs.trans_lt (ENNReal.mul_lt_top (by finiteness)
    ((tsum_lintegral_enorm_lacunaryStoppingLevels_le hf).trans_lt
      (ENNReal.mul_lt_top (by finiteness) hfi.hasFiniteIntegral)))

/-- Actual Bochner interchange for the canonical lacunary magnitude atoms,
at every point and every nonzero modulation. -/
theorem paperOscillatoryAction_stoppingBadPart_eq_tsum_lacunaryLevels
    {f : ℝ → ℂ} (hf : Measurable f) (hfi : Integrable f)
    (lam : ℝ) (hlam : lam ≠ 0) (x : ℝ) :
    paperOscillatoryAction lam hlam (stoppingBadPart f) x =
      ∑' k : ℕ, paperOscillatoryAction lam hlam (lacunaryStoppingLevelBadPart f k) x := by
  have hi (k : ℕ) : Integrable (lacunaryStoppingLevelBadPart f k) :=
    integrable_canonicalLevelBadPart hf hfi (lacunaryAmplitude_pos k).le
  rw [paperOscillatoryAction_eq_integral_of_integrable lam hlam
    (integrable_stoppingBadPart hf hfi)]
  simp_rw [paperOscillatoryAction_eq_integral_of_integrable lam hlam (hi _)]
  have hp (y : ℝ) : highPassKernel lam hlam (x-y) * stoppingBadPart f y =
      ∑' k : ℕ, highPassKernel lam hlam (x-y) * lacunaryStoppingLevelBadPart f k y := by
    rw [tsum_mul_left, (hasSum_lacunaryStoppingLevelBadPart hf hfi y).tsum_eq]
  simp_rw [hp]
  exact integral_tsum
    (fun k ↦ (integrable_highPassKernel_mul lam hlam (hi k) x).1)
    (tsum_lintegral_enorm_highPass_lacunaryStoppingLevels_lt_top hf hfi lam hlam x).ne

/-- The exact complete low contribution and strict high tail dominate the
actual lacunary oscillatory maximal action of the canonical bad part. -/
theorem paperLacunaryOscillatoryMaximal_stoppingBadPart_le_low_add_high
    {f : ℝ → ℂ} (hf : Measurable f) (hfi : Integrable f)
    (B : ℕ → ℕ) (x : ℝ) :
    paperLacunaryOscillatoryMaximal (stoppingBadPart f) x ≤
      lacunaryLowContribution f B x +
        paperLacunaryHighContribution B (lacunaryStoppingLevelBadPart f) x := by
  apply iSup_le
  intro m
  rw [paperOscillatoryAction_stoppingBadPart_eq_tsum_lacunaryLevels hf hfi
    (dyadicModulation m) (dyadicModulation_pos m).ne' x]
  apply enorm_tsum_le_tsum_enorm.trans
  unfold lacunaryLowContribution paperLacunaryHighContribution
  rw [← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro k
  simp only [lacunaryStoppingLevelBadPart]
  rw [paperOscillatoryAction_eq_low_add_high
    (integrable_canonicalLevelBadPart hf hfi (lacunaryAmplitude_pos k).le)
    (B k) (dyadicModulation m) (dyadicModulation_pos m).ne' x]
  apply (enorm_add_le _ _).trans
  apply add_le_add
  · rw [← lacunaryLowActionAtLevel_eq_sum_fixedHeights hf hfi (lacunaryAmplitude_pos k).le]
    exact le_iSup (fun m : ℤ ↦
      ‖lacunaryLowActionAtLevel lacunaryAmplitude f k (B k) m x‖ₑ) m
  · exact le_iSup (fun m : ℤ ↦ ‖∑' n : ℕ,
      ∫ t, lacunaryStoppingLevelBadPart f k (x-t) *
        (dyadicPsi (oscillatoryScaleIndex ((2 : ℝ) ^ m) (B k+n+1)
          (zpow_pos (by norm_num) m).ne') t : ℂ) * phase ((2 : ℝ) ^ m*t^2)‖ₑ) m

theorem lintegral_lacunaryHighOrlicz_le_lowOrlicz (f : ℝ → ℂ) :
    (∫⁻ x, ENNReal.ofReal (‖f x‖ * paperLog 2 ‖f x‖ ^ 2)) ≤
      ∫⁻ x, ENNReal.ofReal (‖f x‖ * paperLog 2 ‖f x‖ ^ 2 * paperLog 4 ‖f x‖) := by
  apply lintegral_mono
  intro x
  exact ENNReal.ofReal_le_ofReal (le_mul_of_one_le_right
    (mul_nonneg (norm_nonneg _) (sq_nonneg _))
      (one_le_paperLog_succ 3 (norm_nonneg (f x))))

/-- The combined endpoint constant for the low and high stopping bad parts. -/
noncomputable def lacunaryBadEndpointConstant (C : ℝ) : ℝ≥0∞ :=
  lacunaryLowEndpointConstant C + lacunaryHighEndpointConstant

theorem lacunaryBadEndpointConstant_lt_top (C : ℝ) : lacunaryBadEndpointConstant C < ∞ :=
  ENNReal.add_lt_top.mpr ⟨lacunaryLowEndpointConstant_lt_top C,
    lacunaryHighEndpointConstant_lt_top⟩

/-- Both estimated bad-part contributions are combined at the universal
threshold two, exactly reflecting the source's `≳ 1` formulation. -/
theorem stoppingBadPart_lacunaryOscillatory_levelSet_two_le_orlicz
    {f : ℝ → ℂ} (hf : Measurable f) (hfi : Integrable f)
    {c : ℕ} {C : ℝ} (hc : ∀ k, 2 * c ≤ 5 * lacunaryHighCutoff k)
    (hblock : HasLogSquaredFrozenBlockWeakBounds f lacunaryHighCutoff c C) :
    volume {x | 2 < paperLacunaryOscillatoryMaximal (stoppingBadPart f) x} ≤
      lacunaryBadEndpointConstant C *
        ∫⁻ x, ENNReal.ofReal (‖f x‖ * paperLog 2 ‖f x‖ ^ 2 * paperLog 4 ‖f x‖) := by
  let L := lacunaryLowContribution f lacunaryHighCutoff
  let H := paperLacunaryHighContribution lacunaryHighCutoff (lacunaryStoppingLevelBadPart f)
  have hsub : {x | 2 < paperLacunaryOscillatoryMaximal (stoppingBadPart f) x} ⊆
      {x | 1 < L x} ∪ {x | 1 < H x} := by
    intro x hx
    by_cases hL : 1 < L x
    · exact Or.inl hL
    apply Or.inr
    by_contra hH
    have hp := paperLacunaryOscillatoryMaximal_stoppingBadPart_le_low_add_high
      hf hfi lacunaryHighCutoff x
    have hh := add_le_add (le_of_not_gt hL) (le_of_not_gt hH)
    norm_num only [one_add_one_eq_two] at hh
    exact hx.not_ge (hp.trans hh)
  apply ((measure_mono hsub).trans (measure_union_le _ _)).trans
  rw [lacunaryBadEndpointConstant, add_mul]
  apply add_le_add
  · exact lacunaryLowContribution_paperCutoff_levelSet_one_le_orlicz hf hfi hc hblock
  · exact (lacunaryHighContribution_levelSet_le_orlicz hf hfi
      (stoppingCenter (f := f)) stoppingLength stoppingLength_pos
      centeredStoppingIntervals_pairwiseDisjoint).trans
        (mul_le_mul' le_rfl (lintegral_lacunaryHighOrlicz_le_lowOrlicz f))

theorem paperLacunaryOscillatoryMaximal_add_le
    {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (x : ℝ) :
    paperLacunaryOscillatoryMaximal (f + g) x ≤
      paperLacunaryOscillatoryMaximal f x + paperLacunaryOscillatoryMaximal g x := by
  apply iSup_le
  intro m
  rw [paperOscillatoryAction_add_of_integrable (dyadicModulation m)
    (dyadicModulation_pos m).ne' hf hg]
  apply (enorm_add_le _ _).trans
  exact add_le_add
    (le_iSup (fun m : ℤ ↦
      ‖paperOscillatoryAction (dyadicModulation m) (dyadicModulation_pos m).ne' f x‖ₑ) m)
    (le_iSup (fun m : ℤ ↦
      ‖paperOscillatoryAction (dyadicModulation m) (dyadicModulation_pos m).ne' g x‖ₑ) m)

theorem paperLacunaryOscillatoryMaximal_le_good_add_bad
    {f : ℝ → ℂ} (hf : Measurable f) (hfi : Integrable f) (x : ℝ) :
    paperLacunaryOscillatoryMaximal f x ≤
      paperLacunaryOscillatoryMaximal (stoppingGoodPart f) x +
        paperLacunaryOscillatoryMaximal (stoppingBadPart f) x := by
  calc
    _ = paperLacunaryOscillatoryMaximal (stoppingGoodPart f + stoppingBadPart f) x := by
      rw [stoppingGoodPart_add_stoppingBadPart]
    _ ≤ _ := paperLacunaryOscillatoryMaximal_add_le
      (integrable_stoppingGoodPart hf hfi) (integrable_stoppingBadPart hf hfi) x

/-- The endpoint constant combining the stopping good and bad oscillatory estimates. -/
noncomputable def lacunaryOscillatoryEndpointConstant (C : ℝ) : ℝ≥0∞ :=
  stoppingGoodOscillatoryConstant + lacunaryBadEndpointConstant C

theorem lacunaryOscillatoryEndpointConstant_lt_top (C : ℝ) :
    lacunaryOscillatoryEndpointConstant C < ∞ :=
  ENNReal.add_lt_top.mpr ⟨stoppingGoodOscillatoryConstant_lt_top,
    lacunaryBadEndpointConstant_lt_top C⟩

/-- The original input, its actual all-height lacunary oscillatory operator,
and the paper's exact Orlicz modular. Threshold three combines the separately
normalized good, low and high estimates without altering the stopping atoms. -/
theorem paperLacunaryOscillatoryMaximal_levelSet_three_le_orlicz
    {f : ℝ → ℂ} (hf : Measurable f) (hfi : Integrable f)
    {c : ℕ} {C : ℝ} (hc : ∀ k, 2 * c ≤ 5 * lacunaryHighCutoff k)
    (hblock : HasLogSquaredFrozenBlockWeakBounds f lacunaryHighCutoff c C) :
    volume {x | 3 < paperLacunaryOscillatoryMaximal f x} ≤
      lacunaryOscillatoryEndpointConstant C *
        ∫⁻ x, ENNReal.ofReal (‖f x‖ * paperLog 2 ‖f x‖ ^ 2 * paperLog 4 ‖f x‖) := by
  have hsub : {x | 3 < paperLacunaryOscillatoryMaximal f x} ⊆
      {x | 1 < paperLacunaryOscillatoryMaximal (stoppingGoodPart f) x} ∪
        {x | 2 < paperLacunaryOscillatoryMaximal (stoppingBadPart f) x} := by
    intro x hx
    by_cases hg : 1 < paperLacunaryOscillatoryMaximal (stoppingGoodPart f) x
    · exact Or.inl hg
    apply Or.inr
    by_contra hb
    have h := (paperLacunaryOscillatoryMaximal_le_good_add_bad hf hfi x).trans
      (add_le_add (le_of_not_gt hg) (le_of_not_gt hb))
    norm_num only [show (1 : ℝ≥0∞) + 2 = 3 by norm_num] at h
    exact hx.not_ge h
  apply ((measure_mono hsub).trans (measure_union_le _ _)).trans
  rw [lacunaryOscillatoryEndpointConstant, add_mul]
  exact add_le_add
    ((stoppingGoodPart_lacunaryOscillatory_levelSet_le hfi).trans
      (mul_le_mul' le_rfl (lintegral_enorm_le_lacunaryOrlicz f)))
    (stoppingBadPart_lacunaryOscillatory_levelSet_two_le_orlicz hf hfi hc hblock)

theorem paperLacunaryOscillatoryMaximal_L0Infinity_levelSet_three_le_orlicz
    (f : L0Infinity) {C : ℝ}
    (hblock : HasLogSquaredFrozenBlockWeakBounds f lacunaryHighCutoff 0 C) :
    volume {x | 3 < paperLacunaryOscillatoryMaximal f x} ≤
      lacunaryOscillatoryEndpointConstant C *
        ∫⁻ x, ENNReal.ofReal (‖f x‖ * paperLog 2 ‖f x‖ ^ 2 * paperLog 4 ‖f x‖) :=
  paperLacunaryOscillatoryMaximal_levelSet_three_le_orlicz f.measurable_toFun f.integrable
    (by intro k; omega) hblock


end LacunaryOscillatoryAssembly
end QuadraticCarleson
