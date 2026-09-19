/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import LeanPool.Besicovitch.SixPoint.RationalChord
public import LeanPool.Besicovitch.SixPoint.SiblingIncidenceLedger

/-!
# Analytic separators for sibling lens cells

The off-matching coincident endpoint cell has a short global proof. Three norm tangents
preserve the correlation between its cross distances. A rational two-by-two Gram majorant then
separates the two colors, leaving a convex quadratic on the three radial vertices.
-/

@[expose] public section

noncomputable section

open scoped InnerProductSpace

namespace LeanPool.Besicovitch

private theorem norm_tangent {E : Type*} [SeminormedAddCommGroup E]
    (x : E) {radius : ℝ} (hradius : 0 < radius) :
    ‖x‖ ≤ (‖x‖ ^ 2 + radius ^ 2) / (2 * radius) := by
  rw [le_div_iff₀ (by positivity : 0 < 2 * radius)]
  nlinarith [sq_nonneg (‖x‖ - radius)]

private theorem weighted_norm_tangent {E : Type*} [SeminormedAddCommGroup E]
    (x : E) (weight radius : ℝ) (hradius : 0 < radius) (hweight : 0 ≤ weight) :
    weight * ‖x‖ ≤ weight / (2 * radius) * (‖x‖ ^ 2 + radius ^ 2) := by
  calc
    weight * ‖x‖ ≤ weight * ((‖x‖ ^ 2 + radius ^ 2) / (2 * radius)) :=
      mul_le_mul_of_nonneg_left (norm_tangent x hradius) hweight
    _ = _ := by ring

private theorem two_mul_norm_tangent {E : Type*} [SeminormedAddCommGroup E]
    (x : E) {radius : ℝ} (hradius : 0 < radius) :
    2 * ‖x‖ ≤ radius + ‖x‖ ^ 2 / radius := by
  have h := norm_tangent x hradius
  calc
    2 * ‖x‖ ≤ 2 * ((‖x‖ ^ 2 + radius ^ 2) / (2 * radius)) :=
      mul_le_mul_of_nonneg_left h (by norm_num)
    _ = radius + ‖x‖ ^ 2 / radius := by field_simp; ring

private theorem weighted_norm_sq {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (x y : E) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ‖a • x + b • y‖ ^ 2 =
      (a + b) * (a * ‖x‖ ^ 2 + b * ‖y‖ ^ 2) - a * b * ‖x - y‖ ^ 2 := by
  rw [norm_add_sq_real, norm_sub_sq_real]
  simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg hb,
    real_inner_smul_left, real_inner_smul_right]
  ring

private theorem norm_sub_sub_sq {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (e x y : E) :
    ‖e - x - y‖ ^ 2 = ‖e‖ ^ 2 + ‖x‖ ^ 2 + ‖y‖ ^ 2 -
      2 * ⟪e, x⟫_ℝ - 2 * ⟪e, y⟫_ℝ + 2 * ⟪x, y⟫_ℝ := by
  rw [norm_sub_sq_real, norm_sub_sq_real]
  simp only [inner_sub_left]
  ring

/-- The rational Gram majorant that retains the three-distance incidence pattern. -/
private theorem offMatching_cross_inner_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (p₁ p₂ w₁ w₂ : E) :
    2 * (12 / 5 : ℝ) * ⟪p₁, w₁⟫_ℝ +
        2 * (3 / 2 : ℝ) * ⟪p₁, w₂⟫_ℝ +
        2 * (3 / 2 : ℝ) * ⟪p₂, w₁⟫_ℝ ≤
      267 / 100 * (‖p₁‖ ^ 2 + ‖w₁‖ ^ 2) +
        75 / 64 * (‖p₂‖ ^ 2 + ‖w₂‖ ^ 2) +
        2 * (15 / 16) * (⟪p₁, p₂⟫_ℝ + ⟪w₁, w₂⟫_ℝ) := by
  have hplus : 0 ≤
      507 / 200 * ‖(p₁ - w₁) + (25 / 52 : ℝ) • (p₂ - w₂)‖ ^ 2 := by
    positivity
  have hminus : 0 ≤
      27 / 200 * ‖(p₁ + w₁) - (25 / 12 : ℝ) • (p₂ + w₂)‖ ^ 2 := by
    positivity
  rw [norm_add_sq_real] at hplus
  rw [norm_sub_sq_real] at hminus
  simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 25 / 52),
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 25 / 12), inner_sub_left,
    inner_sub_right, inner_add_left, inner_add_right, real_inner_smul_right,
    real_inner_comm] at hplus hminus
  ring_nf at hplus hminus
  rw [norm_sub_sq_real p₁ w₁, norm_sub_sq_real p₂ w₂] at hplus
  rw [norm_add_sq_real p₁ w₁, norm_add_sq_real p₂ w₂] at hminus
  ring_nf at hplus hminus ⊢
  nlinarith

private theorem offMatching_pair_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (e x₁ x₂ : E) (he : ‖e‖ = 1)
    (hx₁ : ‖x₁‖ ≤ 1) (hx₂ : ‖x₂‖ ≤ 1)
    (hseparation : barC ≤ ‖x₁ - x₂‖) :
    3003 / 400 * ‖x₁‖ ^ 2 + 231 / 64 * ‖x₂‖ ^ 2 -
        2 * ⟪e, (39 / 10 : ℝ) • x₁ + (3 / 2 : ℝ) • x₂⟫_ℝ -
        7 / 2 * (barC - 1) * ‖x₁‖ - 7 / 2 * (barC + 1) * ‖x₂‖ -
        15 / 16 * barC ^ 2 ≤ 831 / 100 := by
  let z := (39 / 10 : ℝ) • x₁ + (3 / 2 : ℝ) • x₂
  let Q := 1053 / 50 * ‖x₁‖ ^ 2 + 81 / 10 * ‖x₂‖ ^ 2 -
    117 / 20 * barC ^ 2
  have hseparationSq : barC ^ 2 ≤ ‖x₁ - x₂‖ ^ 2 := by
    nlinarith [barC_pos, norm_nonneg (x₁ - x₂)]
  have hzUpper : ‖z‖ ^ 2 ≤ Q := by
    rw [show ‖z‖ ^ 2 =
      ((39 / 10 : ℝ) + 3 / 2) *
          ((39 / 10 : ℝ) * ‖x₁‖ ^ 2 + 3 / 2 * ‖x₂‖ ^ 2) -
        (39 / 10 : ℝ) * (3 / 2) * ‖x₁ - x₂‖ ^ 2 by
      exact weighted_norm_sq x₁ x₂ (by norm_num) (by norm_num)]
    dsimp only [Q]
    nlinarith
  have hinner := real_inner_le_norm (-e) z
  simp only [inner_neg_left, norm_neg, he, one_mul] at hinner
  have hnorm : 2 * ‖z‖ ≤ 84 / 25 + ‖z‖ ^ 2 / (84 / 25) :=
    two_mul_norm_tangent z (by norm_num)
  have hscaled : ‖z‖ ^ 2 / (84 / 25) ≤ Q / (84 / 25) := by
    exact div_le_div_of_nonneg_right hzUpper (by norm_num)
  have horientation :
      -2 * ⟪e, z⟫_ℝ ≤ 84 / 25 + 351 / 56 * ‖x₁‖ ^ 2 +
        135 / 56 * ‖x₂‖ ^ 2 - 195 / 112 * barC ^ 2 := by
    dsimp only [Q] at hscaled
    nlinarith
  have hsum : barC ≤ ‖x₁‖ + ‖x₂‖ :=
    hseparation.trans (norm_sub_le x₁ x₂)
  have hvertices := separableQuadratic_le_radial_vertices
    (a₁ := 38571 / 2800) (a₂ := 2697 / 448)
    (b₁ := -7 / 2 * (barC - 1)) (b₂ := -7 / 2 * (barC + 1))
    (d := 84 / 25 - 75 / 28 * barC ^ 2) (c := barC)
    (t₁ := ‖x₁‖) (t₂ := ‖x₂‖) (by norm_num) (by norm_num) hx₁ hx₂ hsum
  have hvertexBound :
      max (38571 / 2800 + (-7 / 2 * (barC - 1)) + 2697 / 448 +
          (-7 / 2 * (barC + 1)) + (84 / 25 - 75 / 28 * barC ^ 2))
        (max (38571 / 2800 + (-7 / 2 * (barC - 1)) +
            2697 / 448 * (barC - 1) ^ 2 +
            (-7 / 2 * (barC + 1)) * (barC - 1) +
            (84 / 25 - 75 / 28 * barC ^ 2))
          (38571 / 2800 * (barC - 1) ^ 2 +
            (-7 / 2 * (barC - 1)) * (barC - 1) + 2697 / 448 +
            (-7 / 2 * (barC + 1)) +
            (84 / 25 - 75 / 28 * barC ^ 2))) ≤ 831 / 100 := by
    simp only [max_le_iff]
    rcases barC_mem_isolation_box with ⟨hlower, hupper⟩
    norm_num at hlower hupper ⊢
    constructor
    · nlinarith [sq_nonneg (barC - 1)]
    constructor <;> nlinarith [sq_nonneg (barC - 1)]
  dsimp only [z] at horientation
  nlinarith [hvertices.trans hvertexBound]

/-- A global rational tangent separator for the off-matching coincident endpoint cell. -/
theorem offMatchingCoincidentTangentCertificate {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (e p₁ p₂ w₁ w₂ : E) (he : ‖e‖ = 1)
    (hp₁ : ‖p₁‖ ≤ 1) (hp₂ : ‖p₂‖ ≤ 1) (hw₁ : ‖w₁‖ ≤ 1)
    (hw₂ : ‖w₂‖ ≤ 1) (hpsep : barC ≤ ‖p₁ - p₂‖)
    (hwsep : barC ≤ ‖w₁ - w₂‖) :
    14 * ‖e - p₁ - w₁‖ + 6 * ‖e - p₁ - w₂‖ + 6 * ‖e - p₂ - w₁‖ -
        7 / 2 * ((barC - 1) * (‖p₁‖ + ‖w₁‖) +
          (barC + 1) * (‖p₂‖ + ‖w₂‖)) -
        14 + 33 * barC - 45 * barC ^ 2 < 0 := by
  have h₁₁ := weighted_norm_tangent (e - p₁ - w₁) 14 (35 / 12) (by norm_num) (by norm_num)
  have h₁₂ := weighted_norm_tangent (e - p₁ - w₂) 6 2 (by norm_num) (by norm_num)
  have h₂₁ := weighted_norm_tangent (e - p₂ - w₁) 6 2 (by norm_num) (by norm_num)
  rw [norm_sub_sub_sq e p₁ w₁] at h₁₁
  rw [norm_sub_sub_sq e p₁ w₂] at h₁₂
  rw [norm_sub_sub_sq e p₂ w₁] at h₂₁
  simp only [he, one_pow] at h₁₁ h₁₂ h₂₁
  have hcross := offMatching_cross_inner_le p₁ p₂ w₁ w₂
  have hpsepSq : barC ^ 2 ≤ ‖p₁ - p₂‖ ^ 2 := by
    nlinarith [barC_pos, norm_nonneg (p₁ - p₂)]
  have hwsepSq : barC ^ 2 ≤ ‖w₁ - w₂‖ ^ 2 := by
    nlinarith [barC_pos, norm_nonneg (w₁ - w₂)]
  have hpinner :
      2 * ⟪p₁, p₂⟫_ℝ ≤ ‖p₁‖ ^ 2 + ‖p₂‖ ^ 2 - barC ^ 2 := by
    rw [norm_sub_sq_real] at hpsepSq
    nlinarith
  have hwinner :
      2 * ⟪w₁, w₂⟫_ℝ ≤ ‖w₁‖ ^ 2 + ‖w₂‖ ^ 2 - barC ^ 2 := by
    rw [norm_sub_sq_real] at hwsepSq
    nlinarith
  have hp := offMatching_pair_le e p₁ p₂ he hp₁ hp₂ hpsep
  have hw := offMatching_pair_le e w₁ w₂ he hw₁ hw₂ hwsep
  have hconstant :
      27 / 5 + 7 * (35 / 12) + 12 - 14 + 33 * barC - 45 * barC ^ 2 +
        2 * (831 / 100) < 0 := by
    rcases barC_mem_isolation_box with ⟨hlower, hupper⟩
    norm_num at hlower hupper ⊢
    nlinarith [sq_nonneg (barC - 1)]
  simp only [inner_add_right, real_inner_smul_right] at hp hw
  ring_nf at h₁₁ h₁₂ h₂₁ hcross hpinner hwinner hp hw ⊢
  nlinarith

/-- The off-matching coincident lens bound holds for every admissible configuration. -/
theorem offMatchingCoincidentLensBound_of_admissible
    {configuration : SixPointConfiguration} (h : configuration.IsAdmissibleAt barS) :
    OffMatchingCoincidentLensBound configuration := by
  let e := configuration.rootDisplacement
  let p₁ := configuration.redDisplacement .left
  let p₂ := configuration.redDisplacement .right
  let w₁ := configuration.bluePullback .right
  let w₂ := configuration.bluePullback .left
  have hpsep : barC ≤ ‖p₁ - p₂‖ := by
    have hred := configuration.two_mul_le_dist_redDisplacement h
    rw [barS, show 2 * (barC / 2) = barC by ring, dist_eq_norm] at hred
    exact hred
  have hwsep : barC ≤ ‖w₁ - w₂‖ := by
    have hblue := configuration.two_mul_le_dist_bluePullback h
    rw [barS, show 2 * (barC / 2) = barC by ring, dist_eq_norm] at hblue
    exact hblue.trans_eq (norm_sub_rev _ _)
  have hcertificate := offMatchingCoincidentTangentCertificate e p₁ p₂ w₁ w₂
    (configuration.norm_rootDisplacement h)
    (configuration.norm_redDisplacement_le_one h (by simp))
    (configuration.norm_redDisplacement_le_one h (by simp))
    (configuration.norm_bluePullback_le_one h (by simp))
    (configuration.norm_bluePullback_le_one h (by simp))
    hpsep hwsep
  simp only [OffMatchingCoincidentLensBound, diagonalMatchingReducedSlack,
    redEndpointReducedSlack, blueEndpointReducedSlack, incidenceCrossDistance_eq_norm,
    incidenceChildRadius_red_eq_norm, incidenceChildRadius_blue_eq_norm]
  norm_num [incidenceFirst, incidenceSecond, incidenceChild, otherChild]
  dsimp only [e, p₁, p₂, w₁, w₂] at hcertificate
  nlinarith

/-- The off-matching coincident endpoint representative is impossible. -/
theorem not_redEndpoint_one_and_blueEndpoint_one
    {configuration : SixPointConfiguration} (h : configuration.IsAdmissibleAt barS)
    (hmatching : SelectedDiagonalMatchingFails configuration) :
    ¬ (redSiblingTriangleFailure configuration (.endpoint 1) ∧
      blueSiblingTriangleFailure configuration (.endpoint 1)) :=
  offMatchingCoincident_excluded_of_lensBound h hmatching
    (offMatchingCoincidentLensBound_of_admissible h)

end LeanPool.Besicovitch
