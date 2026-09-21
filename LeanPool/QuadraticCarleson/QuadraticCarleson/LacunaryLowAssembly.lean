/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.LacunaryMiddleFinalSummation
import LeanPool.QuadraticCarleson.QuadraticCarleson.CanonicalScaleAtomIntegrals

/-!
# Genuine middle-range and complete lacunary low assembly

The actual canonical low-kernel action is split into its finite middle scale
range and the very-small remainder. The frozen-range error is bounded by the
same already-estimated very-small triangle majorant.
-/

open MeasureTheory Set
open scoped ENNReal

namespace QuadraticCarleson
namespace LacunaryLowAssembly

open CalderonZygmundStoppingIntervals CanonicalScaleAtoms
open LacunaryMiddleRange LacunaryMiddleOperator LacunaryMiddleKalton
open LacunaryMiddleFinalSummation LacunaryVerySmallOperator LacunaryVerySmallEndpoint
open PositiveEndpointOptimization PositiveHighHeightEstimate PositiveLowFullEstimate
open LowKernelLevelSummation


/-- The supremum over dyadic modulations of the middle-range low action at one magnitude level. -/
noncomputable def middleLowContributionAtLevel
    (A : ℕ → ℝ) (f : ℝ → ℂ) (k B c : ℕ) (x : ℝ) : ℝ≥0∞ :=
  ⨆ m : ℤ, ‖middleRangeLowAction A f k B c m x‖ₑ

/-- The sum of the middle-range low contributions over all lacunary magnitude levels. -/
noncomputable def lacunaryMiddleLowContribution
    (f : ℝ → ℂ) (B : ℕ → ℕ) (c : ℕ) (x : ℝ) : ℝ≥0∞ :=
  ∑' k : ℕ, middleLowContributionAtLevel lacunaryAmplitude f k (B k) c x

theorem measurable_middleRangeLowAction
    {A : ℕ → ℝ} {f : ℝ → ℂ} (hf : Measurable f) (k B c : ℕ) (m : ℤ) :
    Measurable (middleRangeLowAction A f k B c m) := by
  have hK : Measurable (fun p : ℝ × ℝ ↦
      paperLowCZKernel (dyadicModulation m) (dyadicModulation_pos m).ne' B p.1 p.2) :=
    (continuous_paperLowOscillatoryKernel (dyadicModulation_pos m).ne' B).measurable.comp
      (measurable_fst.sub measurable_snd)
  have hjoint := hK.mul ((measurable_middleRangeInput (A := A) hf k B c m).comp measurable_snd)
  exact hjoint.stronglyMeasurable.integral_prod_right.measurable

theorem measurable_lacunaryMiddleLowContribution
    {f : ℝ → ℂ} (hf : Measurable f) (B : ℕ → ℕ) (c : ℕ) :
    Measurable (lacunaryMiddleLowContribution f B c) :=
  Measurable.tsum fun k ↦ Measurable.iSup fun m ↦
    (measurable_middleRangeLowAction hf k (B k) c m).enorm

/-- The actual middle action is bounded by the frozen main term plus the
genuine very-small error majorant, uniformly over all modulation blocks. -/
theorem middleLowContributionAtLevel_le_frozen_add_verySmall
    {A : ℕ → ℝ} {f : ℝ → ℂ} (hf : Measurable f) (hfi : Integrable f)
    {k B c : ℕ} (hAk : 0 ≤ A k) (hB : 0 < B) {x : ℝ}
    (hx : x ∉ fivefoldExceptionalSet (stoppingCenter (f := f)) stoppingLength) :
    middleLowContributionAtLevel A f k B c x ≤
      (⨆ τ : ℤ, frozenBlockMaxEnorm A f k B c τ x) +
        verySmallLowContributionAtLevel A f k B c x := by
  apply iSup_le
  intro m
  obtain ⟨τ, hm, _⟩ := exists_unique_mem_Q B m hB
  rw [middleRangeLowAction_eq_frozenBlockLowAction_add_error A hf hfi hAk B c hm x]
  apply (enorm_add_le _ _).trans
  apply add_le_add
  · exact (frozenBlockLowAction_enorm_le_max A f k B c hm x).trans
      (le_iSup (fun τ : ℤ ↦ frozenBlockMaxEnorm A f k B c τ x) τ)
  · exact enorm_frozenBlockErrorLowAction_le_verySmall hf hfi hAk hx

theorem lacunaryMiddleLowContribution_le_frozen_add_verySmall
    {f : ℝ → ℂ} (hf : Measurable f) (hfi : Integrable f)
    {B : ℕ → ℕ} (hB : ∀ k, 0 < B k) (c : ℕ) {x : ℝ}
    (hx : x ∉ fivefoldExceptionalSet (stoppingCenter (f := f)) stoppingLength) :
    lacunaryMiddleLowContribution f B c x ≤
      lacunaryFrozenMainOutput f B c x + lacunaryVerySmallLowContribution f B c x := by
  unfold lacunaryMiddleLowContribution lacunaryFrozenMainOutput lacunaryVerySmallLowContribution
  rw [← ENNReal.tsum_add]
  exact ENNReal.tsum_le_tsum fun k ↦
    middleLowContributionAtLevel_le_frozen_add_verySmall hf hfi
      (lacunaryAmplitude_pos k).le (hB k) hx

/-- The genuine complete lacunary low action at one magnitude level. -/
noncomputable def lacunaryLowActionAtLevel
    (A : ℕ → ℝ) (f : ℝ → ℂ) (k B : ℕ) (m : ℤ) (x : ℝ) : ℂ :=
  ∫ y, paperLowCZKernel (dyadicModulation m) (dyadicModulation_pos m).ne' B x y *
    canonicalLevelBadPart A f k y

/-- The sum over magnitude levels of the maximal lacunary low actions. -/
noncomputable def lacunaryLowContribution
    (f : ℝ → ℂ) (B : ℕ → ℕ) (x : ℝ) : ℝ≥0∞ :=
  ∑' k : ℕ, ⨆ m : ℤ, ‖lacunaryLowActionAtLevel lacunaryAmplitude f k (B k) m x‖ₑ

theorem measurable_lacunaryLowActionAtLevel
    {A : ℕ → ℝ} {f : ℝ → ℂ} (hf : Measurable f) (k B : ℕ) (m : ℤ) :
    Measurable (lacunaryLowActionAtLevel A f k B m) := by
  have hK : Measurable (fun p : ℝ × ℝ ↦
      paperLowCZKernel (dyadicModulation m) (dyadicModulation_pos m).ne' B p.1 p.2) :=
    (continuous_paperLowOscillatoryKernel (dyadicModulation_pos m).ne' B).measurable.comp
      (measurable_fst.sub measurable_snd)
  have hjoint := hK.mul ((measurable_canonicalLevelBadPart (A := A) hf k).comp measurable_snd)
  exact hjoint.stronglyMeasurable.integral_prod_right.measurable

theorem measurable_lacunaryLowContribution
    {f : ℝ → ℂ} (hf : Measurable f) (B : ℕ → ℕ) :
    Measurable (lacunaryLowContribution f B) :=
  Measurable.tsum fun k ↦ Measurable.iSup fun m ↦
    (measurable_lacunaryLowActionAtLevel hf k (B k) m).enorm

theorem summable_canonicalScaleLowActions
    {A : ℕ → ℝ} {f : ℝ → ℂ} (hf : Measurable f) (hfi : Integrable f)
    {k : ℕ} (hAk : 0 ≤ A k) (B : ℕ) (m : ℤ) (x : ℝ) :
    Summable (fun j : ℤ ↦ ∫ y,
      paperLowCZKernel (dyadicModulation m) (dyadicModulation_pos m).ne' B x y *
        stoppingScaleLevelBadPart A f j k y) := by
  let K : ℝ → ℂ := fun y ↦
    paperLowCZKernel (dyadicModulation m) (dyadicModulation_pos m).ne' B x y
  have hK : Measurable K :=
    (continuous_paperLowOscillatoryKernel (dyadicModulation_pos m).ne' B).measurable.comp
      (measurable_const.sub measurable_id)
  have hKi := (integrable_canonicalLevelBadPart hf hfi hAk).bdd_mul hK.aestronglyMeasurable
    (Filter.Eventually.of_forall fun y ↦
      paperLowOscillatoryKernel_norm_le_global (dyadicModulation_pos m).ne' B (x-y))
  have hsum : (∑' j : ℤ, ‖∫ y, K y * stoppingScaleLevelBadPart A f j k y‖ₑ) < ∞ := by
    apply (ENNReal.tsum_le_tsum (fun j ↦ enorm_integral_le_lintegral_enorm
      (fun y ↦ K y * stoppingScaleLevelBadPart A f j k y))).trans_lt
    rw [tsum_lintegral_enorm_kernel_mul_scale hf hK k]
    exact hKi.hasFiniteIntegral
  exact (tsum_enorm_ne_top_iff_summable_norm.mp hsum.ne).of_norm

theorem middleRangeLowAction_eq_sum_scaleActions
    {A : ℕ → ℝ} {f : ℝ → ℂ} (hf : Measurable f) (hfi : Integrable f)
    {k : ℕ} (hAk : 0 ≤ A k) (B c : ℕ) (m : ℤ) (x : ℝ) :
    middleRangeLowAction A f k B c m x =
      ∑ j ∈ S B c m, ∫ y,
        paperLowCZKernel (dyadicModulation m) (dyadicModulation_pos m).ne' B x y *
          stoppingScaleLevelBadPart A f j k y := by
  have hK : Measurable (fun y ↦
      paperLowCZKernel (dyadicModulation m) (dyadicModulation_pos m).ne' B x y) :=
    (continuous_paperLowOscillatoryKernel (dyadicModulation_pos m).ne' B).measurable.comp
      (measurable_const.sub measurable_id)
  unfold middleRangeLowAction middleRangeInput
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum]
  intro j _
  exact (integrable_stoppingScaleLevelBadPart hf hfi j hAk).bdd_mul
    hK.aestronglyMeasurable (Filter.Eventually.of_forall fun y ↦
      paperLowOscillatoryKernel_norm_le_global (dyadicModulation_pos m).ne' B (x-y))

/-- The part outside `S` consists exactly of the very-small scales and
scales whose action vanishes by the proved support theorem. -/
theorem lacunaryLowActionAtLevel_enorm_le_middle_add_verySmall
    {A : ℕ → ℝ} {f : ℝ → ℂ} (hf : Measurable f) (hfi : Integrable f)
    {k : ℕ} (hAk : 0 ≤ A k) (B c : ℕ) (m : ℤ) {x : ℝ}
    (hx : x ∉ fivefoldExceptionalSet (stoppingCenter (f := f)) stoppingLength) :
    ‖lacunaryLowActionAtLevel A f k B m x‖ₑ ≤
      ‖middleRangeLowAction A f k B c m x‖ₑ +
        verySmallLowContributionAtLevel A f k B c x := by
  let u : ℤ → ℂ := fun j ↦ ∫ y,
    paperLowCZKernel (dyadicModulation m) (dyadicModulation_pos m).ne' B x y *
      stoppingScaleLevelBadPart A f j k y
  have hs : Summable u := summable_canonicalScaleLowActions hf hfi hAk B m x
  have heq : lacunaryLowActionAtLevel A f k B m x =
      middleRangeLowAction A f k B c m x + ∑' j : ↑(S B c m : Set ℤ)ᶜ, u j := by
    rw [middleRangeLowAction_eq_sum_scaleActions hf hfi hAk]
    change (∫ y, _ * canonicalLevelBadPart A f k y) =
      (∑ j ∈ S B c m, u j) + ∑' j : ↑(S B c m : Set ℤ)ᶜ, u j
    rw [integral_paperLowCZKernel_canonicalLevelBadPart_eq_tsum_scale hf hfi hAk]
    exact hs.sum_add_tsum_compl.symm
  rw [heq]
  apply (enorm_add_le _ _).trans
  apply add_le_add le_rfl
  apply enorm_tsum_le_tsum_enorm.trans
  have hterm (j : ↑(S B c m : Set ℤ)ᶜ) :
      ‖u j‖ₑ ≤ restrictedCanonicalScaleLowActionEnorm A f k B c m j x := by
    have hj : (j : ℤ) ∉ S B c m := j.2
    rcases not_mem_S_iff_mem_L_or_tooLarge.mp hj with hjL | hjlarge
    · simp only [restrictedCanonicalScaleLowActionEnorm, indicator_of_mem hjL,
        canonicalScaleLowActionEnorm, u, le_refl]
    · have hz : u j = 0 := canonicalScaleLowAction_eq_zero_of_tooLarge
        hf hfi hAk hjlarge hx
      rw [hz, enorm_zero]
      exact bot_le
  calc
    _ ≤ ∑' j : ↑(S B c m : Set ℤ)ᶜ,
        restrictedCanonicalScaleLowActionEnorm A f k B c m j x :=
      ENNReal.tsum_le_tsum hterm
    _ ≤ ∑' j : ℤ, restrictedCanonicalScaleLowActionEnorm A f k B c m j x :=
      ENNReal.summable.tsum_le_tsum_of_inj (↑) Subtype.val_injective
        (fun _ _ ↦ bot_le) (fun _ ↦ le_rfl) ENNReal.summable
    _ ≤ verySmallLowContributionAtLevel A f k B c x :=
      ENNReal.le_tsum (f := fun m' ↦ ∑' j : ℤ,
        restrictedCanonicalScaleLowActionEnorm A f k B c m' j x) m

theorem lacunaryLowContribution_le_middle_add_verySmall
    {f : ℝ → ℂ} (hf : Measurable f) (hfi : Integrable f)
    (B : ℕ → ℕ) (c : ℕ) {x : ℝ}
    (hx : x ∉ fivefoldExceptionalSet (stoppingCenter (f := f)) stoppingLength) :
    lacunaryLowContribution f B x ≤
      lacunaryMiddleLowContribution f B c x + lacunaryVerySmallLowContribution f B c x := by
  unfold lacunaryLowContribution lacunaryMiddleLowContribution lacunaryVerySmallLowContribution
  rw [← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro k
  apply iSup_le
  intro m
  apply (lacunaryLowActionAtLevel_enorm_le_middle_add_verySmall hf hfi
    (lacunaryAmplitude_pos k).le (B k) c m hx).trans
  exact add_le_add (le_iSup (fun m : ℤ ↦
    ‖middleRangeLowAction lacunaryAmplitude f k (B k) c m x‖ₑ) m) le_rfl

/-- All genuine low scales, all integer modulations and all magnitude levels;
the coefficient two records the original very-small term and frozen error. -/
theorem lacunaryLowContribution_le_frozen_add_two_verySmall
    {f : ℝ → ℂ} (hf : Measurable f) (hfi : Integrable f)
    {B : ℕ → ℕ} (hB : ∀ k, 0 < B k) (c : ℕ) {x : ℝ}
    (hx : x ∉ fivefoldExceptionalSet (stoppingCenter (f := f)) stoppingLength) :
    lacunaryLowContribution f B x ≤
      lacunaryFrozenMainOutput f B c x + 2 * lacunaryVerySmallLowContribution f B c x := by
  apply (lacunaryLowContribution_le_middle_add_verySmall hf hfi B c hx).trans
  simpa only [two_mul, add_assoc] using add_le_add
    (lacunaryMiddleLowContribution_le_frozen_add_verySmall hf hfi hB c hx)
    (le_refl (lacunaryVerySmallLowContribution f B c x))

/-- The endpoint constant combining the middle-range and very-small low contributions. -/
noncomputable def lacunaryLowEndpointConstant (C : ℝ) : ℝ≥0∞ :=
  5 + 48 * ENNReal.ofReal C * frozenMiddleOrliczConstant + 4 * verySmallL1Constant

theorem lacunaryLowEndpointConstant_lt_top (C : ℝ) : lacunaryLowEndpointConstant C < ∞ := by
  unfold lacunaryLowEndpointConstant
  exact ENNReal.add_lt_top.mpr ⟨ENNReal.add_lt_top.mpr ⟨by finiteness,
    ENNReal.mul_lt_top (by finiteness) frozenMiddleOrliczConstant_lt_top⟩,
    ENNReal.mul_lt_top (by finiteness) verySmallL1Constant_lt_top⟩

/-- The complete, genuine low-height contribution satisfies the paper's
normalized lacunary Orlicz estimate. Only the individual finite frozen-block
weak estimate remains as an analytic input. -/
theorem lacunaryLowContribution_paperCutoff_levelSet_one_le_orlicz
    {f : ℝ → ℂ} (hf : Measurable f) (hfi : Integrable f)
    {c : ℕ} {C : ℝ} (hc : ∀ k, 2 * c ≤ 5 * lacunaryHighCutoff k)
    (hblock : HasLogSquaredFrozenBlockWeakBounds f lacunaryHighCutoff c C) :
    volume {x | 1 < lacunaryLowContribution f lacunaryHighCutoff x} ≤
      lacunaryLowEndpointConstant C *
        ∫⁻ x, ENNReal.ofReal (‖f x‖ * paperLog 2 ‖f x‖ ^ 2 * paperLog 4 ‖f x‖) := by
  let E := fivefoldExceptionalSet (stoppingCenter (f := f)) stoppingLength
  let M := lacunaryFrozenMainOutput f lacunaryHighCutoff c
  let V := lacunaryVerySmallLowContribution f lacunaryHighCutoff c
  let J := ∫⁻ x, ENNReal.ofReal (‖f x‖ * paperLog 2 ‖f x‖ ^ 2 * paperLog 4 ‖f x‖)
  have h2quarter : (2 : ℝ≥0∞) * ENNReal.ofReal (1 / 4 : ℝ) =
      ENNReal.ofReal (1 / 2 : ℝ) := by
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) by norm_num,
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hhalf : ENNReal.ofReal (1 / 2 : ℝ) + 2 * ENNReal.ofReal (1 / 4 : ℝ) = 1 := by
    rw [h2quarter, ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    norm_num
  have htwo : (2 : ℝ≥0∞) * ENNReal.ofReal (1 / 2 : ℝ) = 1 := by
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) by norm_num,
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hfour : (4 : ℝ≥0∞) * ENNReal.ofReal (1 / 4 : ℝ) = 1 := by
    rw [show (4 : ℝ≥0∞) = ENNReal.ofReal (4 : ℝ) by norm_num,
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num
  have hsub : {x | 1 < lacunaryLowContribution f lacunaryHighCutoff x} ⊆
      E ∪ (({x | ENNReal.ofReal (1 / 2 : ℝ) < M x} ∩ Eᶜ) ∪
        ({x | ENNReal.ofReal (1 / 4 : ℝ) < V x} ∩ Eᶜ)) := by
    intro x hx
    by_cases hxE : x ∈ E
    · exact Or.inl hxE
    apply Or.inr
    by_cases hm : ENNReal.ofReal (1 / 2 : ℝ) < M x
    · exact Or.inl ⟨hm, hxE⟩
    by_cases hv : ENNReal.ofReal (1 / 4 : ℝ) < V x
    · exact Or.inr ⟨hv, hxE⟩
    have hp := lacunaryLowContribution_le_frozen_add_two_verySmall
      hf hfi lacunaryHighCutoff_pos c hxE
    have hle : M x + 2 * V x ≤ 1 := by
      rw [← hhalf]
      exact add_le_add (le_of_not_gt hm) (mul_le_mul' le_rfl (le_of_not_gt hv))
    exact (hx.not_ge (hp.trans hle)).elim
  have hM : volume ({x | ENNReal.ofReal (1 / 2 : ℝ) < M x} ∩ Eᶜ) ≤
      (48 * ENNReal.ofReal C * frozenMiddleOrliczConstant) * J := by
    have h := lacunaryFrozenMainOutput_paperCutoff_compl_levelSet_mul_le_orlicz
      hf hfi hc hblock (by norm_num : (0 : ℝ) < 1 / 2)
    calc
      _ = 2 * (ENNReal.ofReal (1 / 2 : ℝ) *
          volume ({x | ENNReal.ofReal (1 / 2 : ℝ) < M x} ∩ Eᶜ)) := by
        rw [← mul_assoc, htwo, one_mul]
      _ ≤ 2 * ((24 * ENNReal.ofReal C * frozenMiddleOrliczConstant) * J) :=
        mul_le_mul' le_rfl h
      _ = _ := by ring
  have hV : volume ({x | ENNReal.ofReal (1 / 4 : ℝ) < V x} ∩ Eᶜ) ≤
      (4 * verySmallL1Constant) * J := by
    have h := lacunaryVerySmallLowContribution_compl_levelSet_mul_le hf hfi
      lacunaryHighCutoff_pos c (ENNReal.ofReal (1 / 4 : ℝ))
    have hh := mul_le_mul' (le_refl (4 : ℝ≥0∞)) h
    rw [← mul_assoc, hfour, one_mul] at hh
    apply hh.trans
    simpa only [J, mul_assoc] using mul_le_mul'
      (le_refl (4 * verySmallL1Constant)) (lintegral_enorm_le_lacunaryOrlicz f)
  calc
    _ ≤ volume E +
        (volume ({x | ENNReal.ofReal (1 / 2 : ℝ) < M x} ∩ Eᶜ) +
          volume ({x | ENNReal.ofReal (1 / 4 : ℝ) < V x} ∩ Eᶜ)) :=
      (measure_mono hsub).trans ((measure_union_le _ _).trans
        (add_le_add le_rfl (measure_union_le _ _)))
    _ ≤ 5 * J +
        ((48 * ENNReal.ofReal C * frozenMiddleOrliczConstant) * J +
          (4 * verySmallL1Constant) * J) := by
      apply add_le_add
      · exact (volume_canonicalFivefoldExceptionalSet_le hfi).trans
          (mul_le_mul' le_rfl (lintegral_enorm_le_lacunaryOrlicz f))
      · exact add_le_add hM hV
    _ = _ := by unfold lacunaryLowEndpointConstant; ring

theorem lacunaryLowContribution_paperCutoff_zero_levelSet_one_le_orlicz
    {f : ℝ → ℂ} (hf : Measurable f) (hfi : Integrable f) {C : ℝ}
    (hblock : HasLogSquaredFrozenBlockWeakBounds f lacunaryHighCutoff 0 C) :
    volume {x | 1 < lacunaryLowContribution f lacunaryHighCutoff x} ≤
      lacunaryLowEndpointConstant C *
        ∫⁻ x, ENNReal.ofReal (‖f x‖ * paperLog 2 ‖f x‖ ^ 2 * paperLog 4 ‖f x‖) :=
  lacunaryLowContribution_paperCutoff_levelSet_one_le_orlicz hf hfi
    (by intro k; omega) hblock

/-- Exact agreement with the source's finite height sum and convolution
convention, including height zero. -/
theorem lacunaryLowActionAtLevel_eq_sum_fixedHeights
    {A : ℕ → ℝ} {f : ℝ → ℂ} (hf : Measurable f) (hfi : Integrable f)
    {k : ℕ} (hAk : 0 ≤ A k) (B : ℕ) (m : ℤ) (x : ℝ) :
    lacunaryLowActionAtLevel A f k B m x =
      ∑ r ∈ Finset.range (B + 1), ∫ t, canonicalLevelBadPart A f k (x - t) *
        (dyadicPsi (oscillatoryScaleIndex (dyadicModulation m) r
          (dyadicModulation_pos m).ne') t : ℂ) * phase (dyadicModulation m * t ^ 2) :=
  integral_paperLowCZKernel_eq_sum_fixedHeights
    (integrable_canonicalLevelBadPart hf hfi hAk).locallyIntegrable B
      (dyadicModulation m) (dyadicModulation_pos m).ne' x


end LacunaryLowAssembly
end QuadraticCarleson
