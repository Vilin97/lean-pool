/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import LeanPool.Besicovitch.SixPoint.RationalChord
public import LeanPool.Besicovitch.SixPoint.SiblingIncidenceLedger

/-!
# The `S0/S0` sibling incidence

This file closes the balanced/balanced orbit `S0/S0`. Four norm tangents retain their full
two-by-two incidence matrix. A rational positive-semidefinite factorization then separates the
two colors, leaving two copies of the three-vertex radial estimate.
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

/-- The rational positive-semidefinite factorization for the `S0/S0` cross matrix. -/
private theorem s0s0_cross_inner_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (p₁ p₂ w₁ w₂ : E) :
    2 * (1 / 4 : ℝ) * ⟪p₁, w₁⟫_ℝ +
        2 * (3 / 25 : ℝ) * ⟪p₁, w₂⟫_ℝ +
        2 * (3 / 25 : ℝ) * ⟪p₂, w₁⟫_ℝ +
        2 * (7 / 60 : ℝ) * ⟪p₂, w₂⟫_ℝ ≤
      1 / 4 * ‖p₁‖ ^ 2 + 7 / 60 * ‖p₂‖ ^ 2 +
        2 * (3 / 25) * ⟪p₁, p₂⟫_ℝ +
        1 / 4 * ‖w₁‖ ^ 2 + 7 / 60 * ‖w₂‖ ^ 2 +
        2 * (3 / 25) * ⟪w₁, w₂⟫_ℝ := by
  have hfirst : 0 ≤
      ‖(1 / 2 : ℝ) • (p₁ - w₁) + (6 / 25 : ℝ) • (p₂ - w₂)‖ ^ 2 :=
    sq_nonneg _
  have hsecond : 0 ≤ (443 / 7500 : ℝ) * ‖p₂ - w₂‖ ^ 2 :=
    mul_nonneg (by norm_num) (sq_nonneg _)
  rw [norm_add_sq_real] at hfirst
  simp only [norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2),
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 6 / 25),
    real_inner_smul_left, real_inner_smul_right] at hfirst
  ring_nf at hfirst
  rw [norm_sub_sq_real, norm_sub_sq_real] at hfirst
  rw [norm_sub_sq_real] at hsecond
  simp only [inner_sub_left, inner_sub_right, real_inner_comm] at hfirst hsecond
  ring_nf at hfirst hsecond ⊢
  nlinarith

private theorem s0s0_positive_distances_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (e p₁ p₂ w₁ w₂ : E) (he : ‖e‖ = 1) :
    22 / 15 * ‖e - p₁ - w₁‖ + 1 / 2 * ‖e - p₁ - w₂‖ +
        1 / 2 * ‖e - p₂ - w₁‖ + 7 / 15 * ‖e - p₂ - w₂‖ ≤
      7679 / 1800 +
        37 / 100 * ‖p₁‖ ^ 2 + 71 / 300 * ‖p₂‖ ^ 2 +
        37 / 100 * ‖w₁‖ ^ 2 + 71 / 300 * ‖w₂‖ ^ 2 -
        37 / 50 * ⟪e, p₁⟫_ℝ - 71 / 150 * ⟪e, p₂⟫_ℝ -
        37 / 50 * ⟪e, w₁⟫_ℝ - 71 / 150 * ⟪e, w₂⟫_ℝ +
        2 * (1 / 4 : ℝ) * ⟪p₁, w₁⟫_ℝ +
        2 * (3 / 25 : ℝ) * ⟪p₁, w₂⟫_ℝ +
        2 * (3 / 25 : ℝ) * ⟪p₂, w₁⟫_ℝ +
        2 * (7 / 60 : ℝ) * ⟪p₂, w₂⟫_ℝ := by
  have h₁₁ := weightedNorm_le_quadratic (e - p₁ - w₁) (22 / 15) (1 / 4)
    (by norm_num)
  have h₁₂ := weightedNorm_le_quadratic (e - p₁ - w₂) (1 / 2) (3 / 25)
    (by norm_num)
  have h₂₁ := weightedNorm_le_quadratic (e - p₂ - w₁) (1 / 2) (3 / 25)
    (by norm_num)
  have h₂₂ := weightedNorm_le_quadratic (e - p₂ - w₂) (7 / 15) (7 / 60)
    (by norm_num)
  rw [norm_sub_sub_sq e p₁ w₁] at h₁₁
  rw [norm_sub_sub_sq e p₁ w₂] at h₁₂
  rw [norm_sub_sub_sq e p₂ w₁] at h₂₁
  rw [norm_sub_sub_sq e p₂ w₂] at h₂₂
  simp only [he, one_pow] at h₁₁ h₁₂ h₂₁ h₂₂
  ring_nf at h₁₁ h₁₂ h₂₁ h₂₂ ⊢
  nlinarith

private theorem s0s0_cross_le_reduced {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (p₁ p₂ w₁ w₂ : E)
    (hpsep : barC ≤ ‖p₁ - p₂‖) (hwsep : barC ≤ ‖w₁ - w₂‖) :
    2 * (1 / 4 : ℝ) * ⟪p₁, w₁⟫_ℝ +
        2 * (3 / 25 : ℝ) * ⟪p₁, w₂⟫_ℝ +
        2 * (3 / 25 : ℝ) * ⟪p₂, w₁⟫_ℝ +
        2 * (7 / 60 : ℝ) * ⟪p₂, w₂⟫_ℝ ≤
      1 / 4 * ‖p₁‖ ^ 2 + 7 / 60 * ‖p₂‖ ^ 2 +
        3 / 25 * (‖p₁‖ ^ 2 + ‖p₂‖ ^ 2 - barC ^ 2) +
        1 / 4 * ‖w₁‖ ^ 2 + 7 / 60 * ‖w₂‖ ^ 2 +
        3 / 25 * (‖w₁‖ ^ 2 + ‖w₂‖ ^ 2 - barC ^ 2) := by
  have hpsepSq : barC ^ 2 ≤ ‖p₁ - p₂‖ ^ 2 := by
    nlinarith [barC_pos, norm_nonneg (p₁ - p₂)]
  have hwsepSq : barC ^ 2 ≤ ‖w₁ - w₂‖ ^ 2 := by
    nlinarith [barC_pos, norm_nonneg (w₁ - w₂)]
  rw [norm_sub_sq_real] at hpsepSq hwsepSq
  have hpinnerScaled := mul_le_mul_of_nonneg_left hpsepSq
    (by norm_num : (0 : ℝ) ≤ 3 / 25)
  have hwinnerScaled := mul_le_mul_of_nonneg_left hwsepSq
    (by norm_num : (0 : ℝ) ≤ 3 / 25)
  have hcross := s0s0_cross_inner_le p₁ p₂ w₁ w₂
  nlinarith

private theorem s0s0_pair_maximum :
    gramPairMaximum barC (37 / 50) (71 / 150) (37 / 100) (71 / 300)
      ((barC - 1) / 2) ((barC + 1) / 2) (3 / 25) (10 / 27) ≤ 51 / 100 := by
  simp only [gramPairMaximum, max_le_iff]
  rcases barC_mem_isolation_box with ⟨hlower, hupper⟩
  norm_num [gramPairValue] at hlower hupper ⊢
  constructor
  · nlinarith [sq_nonneg (barC - 1)]
  constructor <;> nlinarith [sq_nonneg (barC - 1)]

private theorem s0s0_constant_neg :
    7679 / 1800 + 2 * (51 / 100) -
        14 / 15 * barC * (2 * barC - 1) + 2 * barC - 3 * barC ^ 2 < 0 := by
  rcases barC_mem_isolation_box with ⟨hlower, hupper⟩
  norm_num at hlower hupper ⊢
  nlinarith [sq_nonneg (barC - 1)]

/-- A rational Gram separator for the `S0/S0` incidence representative. -/
theorem gramCertificate_s0s0 {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (e p₁ p₂ w₁ w₂ : E) (he : ‖e‖ = 1)
    (hp₁ : ‖p₁‖ ≤ 1) (hp₂ : ‖p₂‖ ≤ 1) (hw₁ : ‖w₁‖ ≤ 1)
    (hw₂ : ‖w₂‖ ≤ 1) (hpsep : barC ≤ ‖p₁ - p₂‖)
    (hwsep : barC ≤ ‖w₁ - w₂‖) :
    22 / 15 * ‖e - p₁ - w₁‖ + 1 / 2 * ‖e - p₁ - w₂‖ +
        1 / 2 * ‖e - p₂ - w₁‖ + 7 / 15 * ‖e - p₂ - w₂‖ -
        ((barC - 1) * (‖p₁‖ + ‖w₁‖) +
          (barC + 1) * (‖p₂‖ + ‖w₂‖)) / 2 -
        14 / 15 * barC * (2 * barC - 1) + 2 * barC - 3 * barC ^ 2 < 0 := by
  have htangent := s0s0_positive_distances_le e p₁ p₂ w₁ w₂ he
  have hcross := s0s0_cross_le_reduced p₁ p₂ w₁ w₂ hpsep hwsep
  have hp := gramPairCore_le_vertices e p₁ p₂ barC
    (37 / 50) (71 / 150) (37 / 100) (71 / 300)
    ((barC - 1) / 2) ((barC + 1) / 2) (3 / 25) (10 / 27)
    he hp₁ hp₂ hpsep barC_pos.le (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  have hw := gramPairCore_le_vertices e w₁ w₂ barC
    (37 / 50) (71 / 150) (37 / 100) (71 / 300)
    ((barC - 1) / 2) ((barC + 1) / 2) (3 / 25) (10 / 27)
    he hw₁ hw₂ hwsep barC_pos.le (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  have hpBound := hp.trans s0s0_pair_maximum
  have hwBound := hw.trans s0s0_pair_maximum
  simp only [inner_add_right, real_inner_smul_right] at hpBound hwBound
  nlinarith [s0s0_constant_neg]

/-- The alternative positive separator is strictly negative for every admissible configuration. -/
theorem balancedBalancedS0S0GramBound_of_admissible
    {configuration : SixPointConfiguration} (h : configuration.IsAdmissibleAt barS) :
    7 / 15 * diagonalMatchingReducedSlack configuration +
        redBalancedReducedSlack configuration 0 +
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
  have hcertificate := gramCertificate_s0s0 e p₁ p₂ w₁ w₂
    (configuration.norm_rootDisplacement h)
    (configuration.norm_redDisplacement_le_one h (by simp))
    (configuration.norm_redDisplacement_le_one h (by simp))
    (configuration.norm_bluePullback_le_one h (by simp))
    (configuration.norm_bluePullback_le_one h (by simp)) hpsep hwsep
  simp only [diagonalMatchingReducedSlack, redBalancedReducedSlack,
    blueBalancedReducedSlack, balancedIncidencePenalty, incidenceCrossDistance_eq_norm,
    incidenceChildRadius_red_eq_norm, incidenceChildRadius_blue_eq_norm]
  norm_num [incidenceFirst, incidenceSecond, incidenceChild, otherChild]
  dsimp only [e, p₁, p₂, w₁, w₂] at hcertificate
  nlinarith

/-- The `S0/S0` balanced/balanced representative is impossible. -/
theorem not_redBalanced_zero_and_blueBalanced_zero
    {configuration : SixPointConfiguration} (h : configuration.IsAdmissibleAt barS)
    (hmatching : SelectedDiagonalMatchingFails configuration) :
    ¬ (redSiblingTriangleFailure configuration (.balanced 0) ∧
      blueSiblingTriangleFailure configuration (.balanced 0)) := by
  rintro ⟨hred, hblue⟩
  have hmatchingSlack := diagonalMatchingReducedSlack_nonneg h hmatching
  have hredSlack := redBalancedReducedSlack_pos h 0 hred
  have hblueSlack := blueBalancedReducedSlack_pos h 0 hblue
  have hbound := balancedBalancedS0S0GramBound_of_admissible h
  nlinarith

end LeanPool.Besicovitch
