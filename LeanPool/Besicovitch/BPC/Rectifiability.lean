/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import LeanPool.Besicovitch.Rectifiability.AttachmentLocalization
public import LeanPool.Besicovitch.Rectifiability.FiniteContinuum
public import LeanPool.Besicovitch.Rectifiability.ContinuumSurgery
public import LeanPool.Besicovitch.Rectifiability.StraightReduction
public import LeanPool.Besicovitch.Measure.UniformDensityCompact
public import LeanPool.Besicovitch.Sigma.Basic

/-!
# The pair condition forces rectifiability

The Besicovitch pair condition rules out a positive straight purely unrectifiable set whose lower
density is strictly above the pair-condition parameter.
-/

@[expose] public section

noncomputable section

open Bornology MeasureTheory Set
open scoped ENNReal MeasureTheory Topology

namespace LeanPool.Besicovitch

/-- The Besicovitch pair condition at `sigma < 1` forces rectifiability at every strictly larger
density threshold. -/
theorem BesicovitchPairCondition.forcesOneRectifiability
    {sigma gamma : ℝ} (hpairCondition : BesicovitchPairCondition sigma)
    (hsigma : 0 < sigma) (hsigma_one : sigma < 1) (hsigma_gamma : sigma < gamma) :
    ForcesOneRectifiability (EuclideanSpace ℝ (Fin 2)) (ENNReal.ofReal gamma) := by
  intro E hE hE_finite hE_density
  by_contra hE_not_rectifiable
  obtain ⟨A, hA, hAE, hA_pos, hA_finite, hA_pure, hA_straight, hA_density⟩ :=
    exists_pure_straight_subset_of_not_rectifiable hE hE_finite hE_not_rectifiable
      hsigma.le hsigma_gamma hE_density
  let mu := μH[1].restrict A
  letI : IsFiniteMeasure mu := isFiniteMeasure_restrict.mpr hA_finite.ne
  obtain ⟨tau, htau, hpair⟩ := hpairCondition mu hA_straight
  let alpha := min tau (sigma / 2)
  have halpha : 0 < alpha := by
    simpa only [alpha, lt_min_iff] using ⟨htau, half_pos hsigma⟩
  have halpha_tau : alpha ≤ tau := min_le_left _ _
  have halpha_28 : alpha < 28 := by
    calc
      alpha ≤ sigma / 2 := min_le_right _ _
      _ < 1 / 2 := (div_lt_div_iff_of_pos_right (by norm_num)).2 hsigma_one
      _ < 28 := by norm_num
  obtain ⟨density, m, F, hsigma_density, hF_compact, hF_uniform_A, houtside_A⟩ :=
    exists_compact_uniformDensitySet_above hA hA_pos hA_finite.ne hsigma.le
      (div_pos halpha (by norm_num : (0 : ℝ) < 15)) hA_density
  have hF_measurable : MeasurableSet F := hF_compact.isClosed.measurableSet
  have hFA : F ⊆ A := fun _ hx ↦ (hF_uniform_A hx).1
  have hF_uniform : F ⊆ uniformDensitySet mu F density m := by
    intro x hx
    exact ⟨hx, (hF_uniform_A hx).2⟩
  have hmu_F : mu F = μH[1] F := by
    rw [Measure.restrict_apply hF_measurable]
    congr 1
    exact inter_eq_left.mpr hFA
  have hmu_compl : mu Fᶜ = μH[1] (A \ F) := by
    rw [Measure.restrict_apply hF_measurable.compl]
    congr 1
    ext x
    simp only [mem_inter_iff, mem_compl_iff, mem_sdiff]
    tauto
  have houtside : mu Fᶜ < ENNReal.ofReal (alpha / 15) * mu F := by
    rwa [hmu_compl, hmu_F]
  obtain ⟨chosen, hchosen, hdisjoint, hcountable, hselect⟩ :=
    exists_countable_disjoint_badConvexSets (mu := mu) F halpha
  have hsum_lt :
      (∑' V : chosen, Metric.ediam (V : Set (EuclideanSpace ℝ (Fin 2)))) <
        ENNReal.ofReal (1 / 15 : ℝ) * mu F :=
    tsum_ediam_badConvexSets_lt hF_measurable halpha (by norm_num) hchosen
      hcountable hdisjoint houtside
  have hsum : (∑' V : chosen, Metric.ediam (V : Set (EuclideanSpace ℝ (Fin 2)))) ≠ ∞ :=
    ne_top_of_lt hsum_lt
  let lossRate := sigma * alpha / 28
  have hlossRate : 0 < lossRate := by
    dsimp only [lossRate]
    positivity
  obtain ⟨z, hzF, hzHoles, densityScale, hdensityScale, hloss⟩ :=
    exists_densityPoint_not_mem_sevenDiameterThickening hA_straight hF_measurable
      halpha hchosen hcountable hdisjoint houtside hlossRate
  have huniformScale : 0 < 1 / (m + 1 : ℝ) := by positivity
  obtain ⟨delta, hdelta, hpair⟩ := hpair (1 / (m + 1 : ℝ)) huniformScale
  let bound := min delta (min (1 / (m + 1 : ℝ)) (densityScale / 2))
  let rho := bound / 2
  have hbound : 0 < bound := by
    dsimp only [bound]
    simp only [lt_min_iff]
    exact ⟨hdelta, huniformScale, half_pos hdensityScale⟩
  have hrho : 0 < rho := half_pos hbound
  have hrho_bound : rho < bound := by
    dsimp only [rho]
    linarith
  have hrho_delta : rho < delta := hrho_bound.trans_le (min_le_left _ _)
  have hrho_uniform : rho < 1 / (m + 1 : ℝ) :=
    hrho_bound.trans_le <| (min_le_right _ _).trans (min_le_left _ _)
  have htwo_rho_densityScale : 2 * rho < densityScale := by
    have : rho < densityScale / 2 :=
      hrho_bound.trans_le <| (min_le_right _ _).trans (min_le_right _ _)
    linarith
  have hball : ENNReal.ofReal (2 * sigma * rho) < mu (Metric.ball z rho) :=
    uniformDensitySet_ball_measure_gt hsigma.le hsigma_density (hF_uniform hzF)
      hrho hrho_uniform
  have hloss_rho :
      mu (Metric.ball z rho \ F) < ENNReal.ofReal (sigma * alpha / 28 * rho) := by
    have hrho_densityScale : rho < densityScale := by
      have : rho < densityScale / 2 :=
        hrho_bound.trans_le <| (min_le_right _ _).trans (min_le_right _ _)
      linarith
    simpa only [lossRate] using hloss rho hrho hrho_densityScale
  have hannulus := annulus_inter_nonempty hA_straight hsigma halpha halpha_28 hrho
    hball hloss_rho
  let C := localAttachmentComponent F chosen z rho
  have hCdiam_real : sigma * rho / 2 ≤ Metric.diam C :=
    sigma_mul_radius_div_two_le_diam_localAttachmentComponent hF_compact halpha
      halpha_tau hsigma.le hsigma_one hsigma_density hF_uniform hchosen hselect hsum hzF
      hrho hrho_delta hannulus hpair
  let Q := compactAttachmentUnion F chosen
  have hQ_compact : IsCompact Q :=
    isCompact_compactAttachmentUnion hF_compact halpha hchosen hsum
  have hC_compact : IsCompact C := by
    exact isCompact_connectedComponentIn
      (hQ_compact.inter_right Metric.isClosed_closedBall) z
  have hC_subset_ball : C ⊆ Metric.closedBall z rho :=
    (connectedComponentIn_subset _ _).trans inter_subset_right
  have hCdiam : ENNReal.ofReal (sigma * rho / 2) ≤ Metric.ediam C := by
    calc
      ENNReal.ofReal (sigma * rho / 2) ≤ ENNReal.ofReal (Metric.diam C) :=
        ENNReal.ofReal_le_ofReal hCdiam_real
      _ = Metric.ediam C := by
        rw [Metric.diam, ENNReal.ofReal_toReal hC_compact.isBounded.ediam_ne_top]
  have hloss_two_rho :
      mu (Metric.ball z (2 * rho) \ F) <
        ENNReal.ofReal alpha * ENNReal.ofReal (sigma * rho / 14) := by
    have h := hloss (2 * rho) (by positivity) htwo_rho_densityScale
    calc
      mu (Metric.ball z (2 * rho) \ F) <
          ENNReal.ofReal (lossRate * (2 * rho)) := h
      _ = ENNReal.ofReal alpha * ENNReal.ofReal (sigma * rho / 14) := by
        rw [← ENNReal.ofReal_mul halpha.le]
        congr 1
        dsimp only [lossRate]
        ring
  have hlocalSum :
      ∑' V : touchingBadConvexSets 3 chosen C,
        Metric.ediam (diameterThickening 3 (V : Set (EuclideanSpace ℝ (Fin 2)))) <
          Metric.ediam C :=
    tsum_ediam_touchingBadConvexSets_lt_ediam hF_measurable halpha hsigma hchosen
      hcountable hdisjoint hrho hzHoles hC_subset_ball hloss_two_rho hCdiam
  have hzQ : z ∈ Q := Or.inl hzF
  have hzlocal : z ∈ Q ∩ Metric.closedBall z rho :=
    ⟨hzQ, Metric.mem_closedBall_self hrho.le⟩
  have hC_connected : IsConnected C := by
    simpa only [C, localAttachmentComponent, Q] using
      (isConnected_connectedComponentIn_iff.mpr hzlocal)
  obtain ⟨x, hxC, y, hyC, hxy⟩ :=
    hC_compact.exists_edist_eq_ediam hC_connected.nonempty
  have htouching_countable : (touchingBadConvexSets 3 chosen C).Countable :=
    hcountable.mono fun _ hV ↦ hV.1
  letI : Countable (touchingBadConvexSets 3 chosen C) :=
    htouching_countable.to_subtype
  obtain ⟨D, hD_compact, hD_connected, _, _, hD_ediam, _, hD_charged, _, hD_measure⟩ :=
    exists_continuum_surgery_open_holes hC_compact hC_connected hxC hyC hxy
      (fun V : touchingBadConvexSets 3 chosen C ↦
        diameterThickening 3 (V : Set (EuclideanSpace ℝ (Fin 2))))
      (fun V ↦ isOpen_diameterThickening 3 (V : Set (EuclideanSpace ℝ (Fin 2)))) hlocalSum
  have hC_subset_Q : C ⊆ Q := by
    simpa only [C, localAttachmentComponent, Q] using
      ((connectedComponentIn_subset
        (compactAttachmentUnion F chosen ∩ Metric.closedBall z rho) z).trans
          inter_subset_left)
  have hcore_subset_F :
      C \ ⋃ V : touchingBadConvexSets 3 chosen C,
        diameterThickening 3 (V : Set (EuclideanSpace ℝ (Fin 2))) ⊆ F :=
    sdiff_iUnion_touchingBadConvexSets_subset_core halpha hchosen hC_subset_Q
  have hF_finite : μH[1] F ≠ ∞ :=
    ne_top_of_le_ne_top hA_finite.ne (measure_mono hFA)
  have hcore_finite :
      μH[1] (C \ ⋃ V : touchingBadConvexSets 3 chosen C,
        diameterThickening 3 (V : Set (EuclideanSpace ℝ (Fin 2)))) ≠ ∞ :=
    ne_top_of_le_ne_top hF_finite (measure_mono hcore_subset_F)
  have hD_finite : μH[1] D ≠ ∞ := by
    apply ne_top_of_le_ne_top _ hD_measure
    exact ENNReal.add_ne_top.mpr
      ⟨hcore_finite, hC_compact.isBounded.ediam_ne_top⟩
  have hD_rectifiable : IsCountablyOneRectifiable D :=
    LeanPool.Besicovitch.IsConnected.isCountablyOneRectifiable_of_isCompact
      hD_connected hD_compact hD_finite
  have hcore_null :
      μH[1] (D ∩ (C \ ⋃ V : touchingBadConvexSets 3 chosen C,
        diameterThickening 3 (V : Set (EuclideanSpace ℝ (Fin 2))))) = 0 := by
    apply measure_mono_null _ (hA_pure D hD_rectifiable)
    rintro q ⟨hqD, hqcore⟩
    exact ⟨hFA (hcore_subset_F hqcore), hqD⟩
  have hD_measure_lt : μH[1] D < Metric.ediam C := by
    calc
      μH[1] D = μH[1]
          ((D ∩ (C \ ⋃ V : touchingBadConvexSets 3 chosen C,
            diameterThickening 3 (V : Set (EuclideanSpace ℝ (Fin 2))))) ∪
          (D \ (C \ ⋃ V : touchingBadConvexSets 3 chosen C,
            diameterThickening 3 (V : Set (EuclideanSpace ℝ (Fin 2)))))) := by
        rw [inter_union_sdiff]
      _ ≤ μH[1] (D ∩ (C \ ⋃ V : touchingBadConvexSets 3 chosen C,
            diameterThickening 3 (V : Set (EuclideanSpace ℝ (Fin 2))))) +
          μH[1] (D \ (C \ ⋃ V : touchingBadConvexSets 3 chosen C,
            diameterThickening 3 (V : Set (EuclideanSpace ℝ (Fin 2))))) := measure_union_le _ _
      _ = μH[1] (D \ (C \ ⋃ V : touchingBadConvexSets 3 chosen C,
            diameterThickening 3 (V : Set (EuclideanSpace ℝ (Fin 2))))) := by
        rw [hcore_null, zero_add]
      _ < Metric.ediam C := hD_charged
  have hD_lower : Metric.ediam C ≤ μH[1] D := by
    rw [← hD_ediam]
    exact ediam_le_hausdorffMeasure_one_of_isPreconnected hD_connected.isPreconnected
  exact (not_lt_of_ge hD_lower) hD_measure_lt

end LeanPool.Besicovitch
