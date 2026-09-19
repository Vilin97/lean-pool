/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import LeanPool.Besicovitch.SixPoint.RationalChord
public import LeanPool.Besicovitch.SixPoint.SiblingLens

/-!
# The `E1/S0` sibling incidence

This file closes the endpoint/balanced orbit `E1/S0`. A rational factorization of its cross-term
matrix preserves the correlation between the three positive distances. The resulting two
colorwise quadratics are bounded on the three radial vertices.
-/

@[expose] public section

noncomputable section

open scoped InnerProductSpace

namespace LeanPool.Besicovitch

private theorem norm_sub_sub_sq {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (e x y : E) :
    ‖e - x - y‖ ^ 2 = ‖e‖ ^ 2 + ‖x‖ ^ 2 + ‖y‖ ^ 2 -
      2 * ⟪e, x⟫_ℝ - 2 * ⟪e, y⟫_ℝ + 2 * ⟪x, y⟫_ℝ := by
  rw [norm_sub_sq_real, norm_sub_sq_real]
  simp only [inner_sub_left]
  ring

/-- A rational sum-of-squares factorization of the `E1/S0` cross matrix. -/
private theorem e1s0_cross_inner_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (p₁ p₂ w₁ w₂ : E) :
    2 * (31 / 80 : ℝ) * ⟪p₁, w₁⟫_ℝ +
        2 * (7 / 15 : ℝ) * ⟪p₁, w₂⟫_ℝ +
        2 * (4 / 15 : ℝ) * ⟪p₂, w₂⟫_ℝ ≤
      256 / 625 * ‖p₁‖ ^ 2 + 757 / 5000 * ‖p₂‖ ^ 2 +
        2 * (68 / 625) * ⟪p₁, p₂⟫_ℝ +
        727477 / 1605632 * ‖w₁‖ ^ 2 + 39397 / 56448 * ‖w₂‖ ^ 2 +
        2 * (32271 / 100352) * ⟪w₁, w₂⟫_ℝ := by
  have hfirst : 0 ≤
      ‖(16 / 25 : ℝ) • p₁ + (17 / 100 : ℝ) • p₂ -
        ((155 / 256 : ℝ) • w₁ + (35 / 48 : ℝ) • w₂)‖ ^ 2 :=
    sq_nonneg _
  have hsecond : 0 ≤
      ‖(7 / 20 : ℝ) • p₂ -
        ((137 / 336 : ℝ) • w₂ - (527 / 1792 : ℝ) • w₁)‖ ^ 2 :=
    sq_nonneg _
  rw [norm_sub_sq_real] at hfirst hsecond
  rw [norm_add_sq_real] at hfirst
  rw [norm_add_sq_real] at hfirst
  rw [norm_sub_sq_real] at hsecond
  simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 16 / 25),
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 17 / 100),
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 155 / 256),
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 35 / 48),
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 7 / 20),
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 137 / 336),
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 527 / 1792), inner_add_left,
    inner_add_right, inner_sub_right, real_inner_smul_right, real_inner_comm] at hfirst hsecond
  ring_nf at hfirst hsecond ⊢
  nlinarith

private theorem e1s0_red_pair_maximum :
    gramPairMaximum barC (41177 / 30000) (7903 / 15000) (41 / 48) (4 / 15)
      ((barC - 1) / 2) ((barC + 1) / 2) (68 / 625) (9 / 10) ≤ 53 / 25 := by
  simp only [gramPairMaximum, max_le_iff]
  rcases barC_mem_isolation_box with ⟨hlower, hupper⟩
  norm_num [gramPairValue] at hlower hupper ⊢
  constructor
  · nlinarith [sq_nonneg (barC - 1)]
  constructor <;> nlinarith [sq_nonneg (barC - 1)]

private theorem e1s0_blue_pair_maximum :
    gramPairMaximum barC (9329977 / 8028160) (7915571 / 4515840) (31 / 80) (11 / 15)
      (17 / 16 * (barC + 1)) (17 / 16 * (barC - 1)) (32271 / 100352)
      (13 / 20) ≤ 11 / 10 := by
  simp only [gramPairMaximum, max_le_iff]
  rcases barC_mem_isolation_box with ⟨hlower, hupper⟩
  norm_num [gramPairValue] at hlower hupper ⊢
  constructor
  · nlinarith [sq_nonneg (barC - 1)]
  constructor <;> nlinarith [sq_nonneg (barC - 1)]

private theorem e1s0_positive_distances_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (e p₁ p₂ w₁ w₂ : E) (he : ‖e‖ = 1) :
    37 / 20 * ‖e - p₁ - w₁‖ + 21 / 8 * ‖e - p₁ - w₂‖ +
        27 / 20 * ‖e - p₂ - w₂‖ ≤
      269 / 240 + 4717 / 620 +
        41 / 48 * ‖p₁‖ ^ 2 + 4 / 15 * ‖p₂‖ ^ 2 +
        31 / 80 * ‖w₁‖ ^ 2 + 11 / 15 * ‖w₂‖ ^ 2 -
        41 / 24 * ⟪e, p₁⟫_ℝ - 8 / 15 * ⟪e, p₂⟫_ℝ -
        31 / 40 * ⟪e, w₁⟫_ℝ - 22 / 15 * ⟪e, w₂⟫_ℝ +
        2 * (31 / 80 : ℝ) * ⟪p₁, w₁⟫_ℝ +
        2 * (7 / 15 : ℝ) * ⟪p₁, w₂⟫_ℝ +
        2 * (4 / 15 : ℝ) * ⟪p₂, w₂⟫_ℝ := by
  have h₁₁ := weightedNorm_le_quadratic (e - p₁ - w₁) (37 / 20) (31 / 80)
    (by norm_num)
  have h₁₂ := weightedNorm_le_quadratic (e - p₁ - w₂) (21 / 8) (7 / 15)
    (by norm_num)
  have h₂₂ := weightedNorm_le_quadratic (e - p₂ - w₂) (27 / 20) (4 / 15)
    (by norm_num)
  rw [norm_sub_sub_sq e p₁ w₁] at h₁₁
  rw [norm_sub_sub_sq e p₁ w₂] at h₁₂
  rw [norm_sub_sub_sq e p₂ w₂] at h₂₂
  simp only [he, one_pow] at h₁₁ h₁₂ h₂₂
  ring_nf at h₁₁ h₁₂ h₂₂ ⊢
  nlinarith

private theorem e1s0_cross_le_reduced {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (p₁ p₂ w₁ w₂ : E)
    (hpsep : barC ≤ ‖p₁ - p₂‖) (hwsep : barC ≤ ‖w₁ - w₂‖) :
    2 * (31 / 80 : ℝ) * ⟪p₁, w₁⟫_ℝ +
        2 * (7 / 15 : ℝ) * ⟪p₁, w₂⟫_ℝ +
        2 * (4 / 15 : ℝ) * ⟪p₂, w₂⟫_ℝ ≤
      256 / 625 * ‖p₁‖ ^ 2 + 757 / 5000 * ‖p₂‖ ^ 2 +
        68 / 625 * (‖p₁‖ ^ 2 + ‖p₂‖ ^ 2 - barC ^ 2) +
        727477 / 1605632 * ‖w₁‖ ^ 2 + 39397 / 56448 * ‖w₂‖ ^ 2 +
        32271 / 100352 * (‖w₁‖ ^ 2 + ‖w₂‖ ^ 2 - barC ^ 2) := by
  have hpsepSq : barC ^ 2 ≤ ‖p₁ - p₂‖ ^ 2 := by
    nlinarith [barC_pos, norm_nonneg (p₁ - p₂)]
  have hwsepSq : barC ^ 2 ≤ ‖w₁ - w₂‖ ^ 2 := by
    nlinarith [barC_pos, norm_nonneg (w₁ - w₂)]
  rw [norm_sub_sq_real] at hpsepSq hwsepSq
  have hpinnerScaled := mul_le_mul_of_nonneg_left hpsepSq
    (by norm_num : (0 : ℝ) ≤ 68 / 625)
  have hwinnerScaled := mul_le_mul_of_nonneg_left hwsepSq
    (by norm_num : (0 : ℝ) ≤ 32271 / 100352)
  have hcross := e1s0_cross_inner_le p₁ p₂ w₁ w₂
  nlinarith

private theorem e1s0_constant_neg :
    269 / 240 + 4717 / 620 - 17 / 8 + 551 / 80 * barC -
      807 / 80 * barC ^ 2 + 53 / 25 + 11 / 10 < 0 := by
  rcases barC_mem_isolation_box with ⟨hlower, hupper⟩
  norm_num at hlower hupper ⊢
  nlinarith [sq_nonneg (barC - 1)]

private theorem e1s0_decomposition {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (e p₁ p₂ w₁ w₂ : E) (he : ‖e‖ = 1)
    (hpsep : barC ≤ ‖p₁ - p₂‖) (hwsep : barC ≤ ‖w₁ - w₂‖) :
    37 / 20 * ‖e - p₁ - w₁‖ + 21 / 8 * ‖e - p₁ - w₂‖ +
        27 / 20 * ‖e - p₂ - w₂‖ -
        ((barC - 1) * ‖p₁‖ + (barC + 1) * ‖p₂‖) / 2 -
        17 / 16 * ((barC + 1) * ‖w₁‖ + (barC - 1) * ‖w₂‖) ≤
      269 / 240 + 4717 / 620 +
        (41177 / 30000 * ‖p₁‖ ^ 2 + 7903 / 15000 * ‖p₂‖ ^ 2 -
          41 / 24 * ⟪e, p₁⟫_ℝ - 8 / 15 * ⟪e, p₂⟫_ℝ -
          (barC - 1) / 2 * ‖p₁‖ - (barC + 1) / 2 * ‖p₂‖ -
          68 / 625 * barC ^ 2) +
        (9329977 / 8028160 * ‖w₁‖ ^ 2 + 7915571 / 4515840 * ‖w₂‖ ^ 2 -
          31 / 40 * ⟪e, w₁⟫_ℝ - 22 / 15 * ⟪e, w₂⟫_ℝ -
          17 / 16 * (barC + 1) * ‖w₁‖ -
          17 / 16 * (barC - 1) * ‖w₂‖ - 32271 / 100352 * barC ^ 2) := by
  have htangent := e1s0_positive_distances_le e p₁ p₂ w₁ w₂ he
  have hcross := e1s0_cross_le_reduced p₁ p₂ w₁ w₂ hpsep hwsep
  nlinarith

private theorem e1s0_red_pair_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (e p₁ p₂ : E) (he : ‖e‖ = 1)
    (hp₁ : ‖p₁‖ ≤ 1) (hp₂ : ‖p₂‖ ≤ 1) (hpsep : barC ≤ ‖p₁ - p₂‖) :
    41177 / 30000 * ‖p₁‖ ^ 2 + 7903 / 15000 * ‖p₂‖ ^ 2 -
        41 / 24 * ⟪e, p₁⟫_ℝ - 8 / 15 * ⟪e, p₂⟫_ℝ -
        (barC - 1) / 2 * ‖p₁‖ - (barC + 1) / 2 * ‖p₂‖ -
        68 / 625 * barC ^ 2 ≤ 53 / 25 := by
  have hp := gramPairCore_le_vertices e p₁ p₂ barC (41177 / 30000) (7903 / 15000)
    (41 / 48) (4 / 15) ((barC - 1) / 2) ((barC + 1) / 2) (68 / 625) (9 / 10)
    he hp₁ hp₂ hpsep barC_pos.le (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
  have hpBound := hp.trans e1s0_red_pair_maximum
  simp only [inner_add_right, real_inner_smul_right] at hpBound
  nlinarith

private theorem e1s0_blue_pair_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (e w₁ w₂ : E) (he : ‖e‖ = 1)
    (hw₁ : ‖w₁‖ ≤ 1) (hw₂ : ‖w₂‖ ≤ 1) (hwsep : barC ≤ ‖w₁ - w₂‖) :
    9329977 / 8028160 * ‖w₁‖ ^ 2 + 7915571 / 4515840 * ‖w₂‖ ^ 2 -
        31 / 40 * ⟪e, w₁⟫_ℝ - 22 / 15 * ⟪e, w₂⟫_ℝ -
        17 / 16 * (barC + 1) * ‖w₁‖ -
        17 / 16 * (barC - 1) * ‖w₂‖ - 32271 / 100352 * barC ^ 2 ≤ 11 / 10 := by
  have hw := gramPairCore_le_vertices e w₁ w₂ barC
    (9329977 / 8028160) (7915571 / 4515840) (31 / 80) (11 / 15)
    (17 / 16 * (barC + 1)) (17 / 16 * (barC - 1)) (32271 / 100352) (13 / 20)
    he hw₁ hw₂ hwsep barC_pos.le (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
  have hwBound := hw.trans e1s0_blue_pair_maximum
  simp only [inner_add_right, real_inner_smul_right] at hwBound
  nlinarith

/-- A rational Gram separator for the `E1/S0` incidence representative. -/
theorem gramCertificate_e1s0 {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (e p₁ p₂ w₁ w₂ : E) (he : ‖e‖ = 1)
    (hp₁ : ‖p₁‖ ≤ 1) (hp₂ : ‖p₂‖ ≤ 1) (hw₁ : ‖w₁‖ ≤ 1)
    (hw₂ : ‖w₂‖ ≤ 1) (hpsep : barC ≤ ‖p₁ - p₂‖)
    (hwsep : barC ≤ ‖w₁ - w₂‖) :
    37 / 20 * ‖e - p₁ - w₁‖ + 21 / 8 * ‖e - p₁ - w₂‖ +
        27 / 20 * ‖e - p₂ - w₂‖ -
        ((barC - 1) * ‖p₁‖ + (barC + 1) * ‖p₂‖) / 2 -
        17 / 16 * ((barC + 1) * ‖w₁‖ + (barC - 1) * ‖w₂‖) -
        17 / 8 + 551 / 80 * barC - 807 / 80 * barC ^ 2 < 0 := by
  have hdecompose := e1s0_decomposition e p₁ p₂ w₁ w₂ he hpsep hwsep
  have hpBound := e1s0_red_pair_le e p₁ p₂ he hp₁ hp₂ hpsep
  have hwBound := e1s0_blue_pair_le e w₁ w₂ he hw₁ hw₂ hwsep
  nlinarith [e1s0_constant_neg]

/-- The alternative positive separator is strictly negative for every admissible configuration. -/
theorem endpointBalancedE1S0GramBound_of_admissible
    {configuration : SixPointConfiguration} (h : configuration.IsAdmissibleAt barS) :
    27 / 20 * diagonalMatchingReducedSlack configuration +
        17 / 8 * redEndpointReducedSlack configuration 1 +
        blueBalancedReducedSlack configuration 0 < 0 := by
  let e := configuration.rootDisplacement
  let p₁ := configuration.redDisplacement .left
  let p₂ := configuration.redDisplacement .right
  let w₁ := configuration.bluePullback .left
  let w₂ := configuration.bluePullback .right
  have hpsep : barC ≤ ‖p₁ - p₂‖ := by
    have hred := configuration.two_mul_le_dist_redDisplacement h
    rw [barS, show 2 * (barC / 2) = barC by ring, dist_eq_norm] at hred
    exact hred
  have hwsep : barC ≤ ‖w₁ - w₂‖ := by
    have hblue := configuration.two_mul_le_dist_bluePullback h
    rw [barS, show 2 * (barC / 2) = barC by ring, dist_eq_norm] at hblue
    exact hblue
  have hcertificate := gramCertificate_e1s0 e p₁ p₂ w₁ w₂
    (configuration.norm_rootDisplacement h)
    (configuration.norm_redDisplacement_le_one h (by simp))
    (configuration.norm_redDisplacement_le_one h (by simp))
    (configuration.norm_bluePullback_le_one h (by simp))
    (configuration.norm_bluePullback_le_one h (by simp)) hpsep hwsep
  simp only [diagonalMatchingReducedSlack, redEndpointReducedSlack,
    blueBalancedReducedSlack, balancedIncidencePenalty, incidenceCrossDistance_eq_norm,
    incidenceChildRadius_red_eq_norm, incidenceChildRadius_blue_eq_norm]
  norm_num [incidenceFirst, incidenceSecond, incidenceChild, otherChild]
  dsimp only [e, p₁, p₂, w₁, w₂] at hcertificate
  nlinarith

/-- The `E1/S0` endpoint/balanced representative is impossible. -/
theorem not_redEndpoint_one_and_blueBalanced_zero
    {configuration : SixPointConfiguration} (h : configuration.IsAdmissibleAt barS)
    (hmatching : SelectedDiagonalMatchingFails configuration) :
    ¬ (redSiblingTriangleFailure configuration (.endpoint 1) ∧
      blueSiblingTriangleFailure configuration (.balanced 0)) := by
  rintro ⟨hred, hblue⟩
  have hmatchingSlack := diagonalMatchingReducedSlack_nonneg h hmatching
  have hredSlack := redEndpointReducedSlack_pos h 1 hred
  have hblueSlack := blueBalancedReducedSlack_pos h 0 hblue
  have hbound := endpointBalancedE1S0GramBound_of_admissible h
  nlinarith

end LeanPool.Besicovitch
