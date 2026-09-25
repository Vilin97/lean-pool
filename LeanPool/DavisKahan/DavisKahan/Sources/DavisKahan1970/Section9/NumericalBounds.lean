/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module


public import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section9.ExactData

/-!
# Davis--Kahan 1970, Section 9: certified numerical bounds

This file turns the exact radical expressions from the Section 9 finite model
into the printed decimal upper bounds.  The decimals are represented by exact
rationals.  The theorem-facing statements accept the corresponding exact
sine, tangent, or double-angle estimate as a hypothesis; the general
Davis--Kahan APIs can discharge those hypotheses in a separate integration
module.
-/

@[expose] public section

namespace TauCeti
namespace DavisKahan1970
namespace Section9

private lemma sqrt76_lt_4359_div_500 :
    Real.sqrt 76 < (4359 : ℝ) / 500 := by
  nlinarith [Real.sqrt_nonneg (76 : ℝ),
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 76)]

private lemma sqrt76_gt_87_div_10 :
    (87 : ℝ) / 10 < Real.sqrt 76 := by
  nlinarith [Real.sqrt_nonneg (76 : ℝ),
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 76)]

private lemma sqrt3_lt_8661_div_5000 :
    Real.sqrt 3 < (8661 : ℝ) / 5000 := by
  nlinarith [Real.sqrt_nonneg (3 : ℝ),
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]

private lemma sqrt3_gt_17319_div_10000 :
    (17319 : ℝ) / 10000 < Real.sqrt 3 := by
  nlinarith [Real.sqrt_nonneg (3 : ℝ),
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]

private lemma sqrt15_lt_3873_div_1000 :
    Real.sqrt 15 < (3873 : ℝ) / 1000 := by
  nlinarith [Real.sqrt_nonneg (15 : ℝ),
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 15)]

private lemma sqrt30_lt_2739_div_500 :
    Real.sqrt 30 < (2739 : ℝ) / 500 := by
  nlinarith [Real.sqrt_nonneg (30 : ℝ),
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 30)]

private lemma sqrt7_lt_53_div_20 :
    Real.sqrt 7 < (53 : ℝ) / 20 := by
  nlinarith [Real.sqrt_nonneg (7 : ℝ),
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 7)]

/-- The upper Ritz coefficient is below the printed `0.7887`. -/
lemma ritzHighCoefficient_lt_printed :
    ritzHighCoefficient < (7887 : ℝ) / 10000 := by
  unfold ritzHighCoefficient
  nlinarith [sqrt3_lt_8661_div_5000]

/-- The lower Ritz coefficient is below the printed `0.21135`. -/
lemma ritzLowCoefficient_lt_printed :
    ritzLowCoefficient < (4227 : ℝ) / 20000 := by
  unfold ritzLowCoefficient
  nlinarith [sqrt3_gt_17319_div_10000]

/-- The top residual root `√((11 + √76)/30)` is below the printed `0.811`. -/
lemma residualTopRoot_lt_printed :
    Real.sqrt ((11 + Real.sqrt 76) / 30) < (811 : ℝ) / 1000 := by
  have hq : 0 ≤ (11 + Real.sqrt 76) / 30 := by positivity
  have hs := Real.sq_sqrt hq
  nlinarith [sqrt76_lt_4359_div_500, Real.sqrt_nonneg ((11 + Real.sqrt 76) / 30)]

/-- The bottom residual root `√((11 - √76)/30)` is below the printed `0.279`. -/
lemma residualBottomRoot_lt_printed :
    Real.sqrt ((11 - Real.sqrt 76) / 30) < (279 : ℝ) / 1000 := by
  have h76 := sqrt76_le_eleven
  have hq : 0 ≤ (11 - Real.sqrt 76) / 30 := by positivity
  have hs := Real.sq_sqrt hq
  nlinarith [sqrt76_gt_87_div_10, Real.sqrt_nonneg ((11 - Real.sqrt 76) / 30)]

/-- The initial `sin Θ` estimate is below the printed decimal, for every `ε > 0`. -/
lemma initial_sin_exact_lt_printed (ε : ℝ) (hε : 0 < ε) :
    residualTopSingularValue ε / 500 < (811 : ℝ) / 500000 * ε := by
  rw [residualTopSingularValue, abs_of_pos hε]
  nlinarith [residualTopRoot_lt_printed]

/-- The initial Ky Fan 2-norm estimate is below the printed decimal, for every
`ε > 0`. -/
lemma initial_kyFanTwo_exact_lt_printed (ε : ℝ) (hε : 0 < ε) :
    residualKyFanTwo ε / 500 < (109 : ℝ) / 50000 * ε := by
  rw [residualKyFanTwo, residualTopSingularValue, residualBottomSingularValue,
    abs_of_pos hε]
  nlinarith [residualTopRoot_lt_printed, residualBottomRoot_lt_printed]

/-- Exact normalized tangent bound obtained from the recentered residual. -/
noncomputable def tangentThetaExactBound (ε : ℝ) : ℝ :=
  ((Real.sqrt 15 / 15) / 500 * ε) /
    (1 - (ritzHighCoefficient / 500) * ε)

/-- Exact normalized tangent-double-angle bound. -/
noncomputable def tangentTwoThetaExactBound (ε : ℝ) : ℝ :=
  (2 * ((Real.sqrt 15 / 15) / 500) * ε) /
    (1 - (ritzHighCoefficient / 500) * ε)

/-- Exact one-column tangent bound for the lower Ritz vector. -/
noncomputable def lowerIndividualTangentExactBound (ε : ℝ) : ℝ :=
  ((Real.sqrt 30 / 30) / 500 * ε) /
    (1 - (ritzLowCoefficient / 500) * ε)

/-- Exact one-column tangent bound for the upper Ritz vector. -/
noncomputable def upperIndividualTangentExactBound (ε : ℝ) : ℝ :=
  ((Real.sqrt 30 / 30) / 500 * ε) /
    (1 - (ritzHighCoefficient / 500) * ε)

/-- Exact scalar envelope obtained by combining the Schur-complement
`tan(2 psi)` estimate and the complementary-coordinate `tan eta` estimate. -/
noncomputable def lowerIndividualAngleExactBound (ε : ℝ) : ℝ :=
  ((Real.sqrt 7 / 10) / 500 * ε) /
    (1 - (ritzLowCoefficient / 500) * ε)

/-- Upper-Ritz-vector version of the combined individual-angle envelope. -/
noncomputable def upperIndividualAngleExactBound (ε : ℝ) : ℝ :=
  ((Real.sqrt 7 / 10) / 500 * ε) /
    (1 - (ritzHighCoefficient / 500) * ε)

private theorem ratio_strict_mono
    {ε a A c C : ℝ}
    (hε : 0 < ε) (ha0 : 0 ≤ a) (ha : a < A)
    (hc : c ≤ C) (hC : C * ε < 1) :
    (a * ε) / (1 - c * ε) < (A * ε) / (1 - C * ε) := by
  have hdC : 0 < 1 - C * ε := by linarith
  have hdc : 0 < 1 - c * ε := by nlinarith
  have hnum : a * ε < A * ε := mul_lt_mul_of_pos_right ha hε
  have hfirst : (a * ε) / (1 - c * ε) < (A * ε) / (1 - c * ε) :=
    div_lt_div_of_pos_right hnum hdc
  have hA0 : 0 ≤ A * ε := by
    have hA : 0 < A := lt_of_le_of_lt ha0 ha
    exact (mul_pos hA hε).le
  have hden : 1 - C * ε ≤ 1 - c * ε := by nlinarith
  have hsecond : (A * ε) / (1 - c * ε) ≤ (A * ε) / (1 - C * ε) := by
    apply (div_le_div_iff₀ hdc hdC).2
    exact mul_le_mul_of_nonneg_left hden hA0
  exact hfirst.trans_le hsecond

/-- The exact `tan Θ` bound is below the printed rational bound `(a·ε)/(1 - b·ε)`.
The hypothesis `ε < 100` is what keeps the denominator positive. -/
lemma tangentThetaExactBound_lt_printed (ε : ℝ)
    (hε : 0 < ε) (hε100 : ε < 100) :
    tangentThetaExactBound ε <
      ((1291 : ℝ) / 2500000 * ε) /
        (1 - (7887 : ℝ) / 5000000 * ε) := by
  unfold tangentThetaExactBound
  apply ratio_strict_mono hε (by positivity)
  · nlinarith [sqrt15_lt_3873_div_1000]
  · nlinarith [ritzHighCoefficient_lt_printed]
  · nlinarith

/-- The exact `tan 2Θ` bound is below the printed rational bound — twice the
`tan Θ` numerator over the same denominator, so it needs the same `ε < 100`. -/
lemma tangentTwoThetaExactBound_lt_printed (ε : ℝ)
    (hε : 0 < ε) (hε100 : ε < 100) :
    tangentTwoThetaExactBound ε <
      ((1291 : ℝ) / 1250000 * ε) /
        (1 - (7887 : ℝ) / 5000000 * ε) := by
  unfold tangentTwoThetaExactBound
  apply ratio_strict_mono hε (by positivity)
  · nlinarith [sqrt15_lt_3873_div_1000]
  · nlinarith [ritzHighCoefficient_lt_printed]
  · nlinarith

/-- The exact lower individual-angle tangent bound is below its printed rational
bound, on `0 < ε < 100`. -/
lemma lowerIndividualTangentExactBound_lt_printed (ε : ℝ)
    (hε : 0 < ε) (hε100 : ε < 100) :
    lowerIndividualTangentExactBound ε <
      ((913 : ℝ) / 2500000 * ε) /
        (1 - (4227 : ℝ) / 10000000 * ε) := by
  unfold lowerIndividualTangentExactBound
  apply ratio_strict_mono hε (by positivity)
  · nlinarith [sqrt30_lt_2739_div_500]
  · nlinarith [ritzLowCoefficient_lt_printed]
  · nlinarith

/-- The exact upper individual-angle tangent bound is below its printed rational
bound, on `0 < ε < 100`. -/
lemma upperIndividualTangentExactBound_lt_printed (ε : ℝ)
    (hε : 0 < ε) (hε100 : ε < 100) :
    upperIndividualTangentExactBound ε <
      ((913 : ℝ) / 2500000 * ε) /
        (1 - (7887 : ℝ) / 5000000 * ε) := by
  unfold upperIndividualTangentExactBound
  apply ratio_strict_mono hε (by positivity)
  · nlinarith [sqrt30_lt_2739_div_500]
  · nlinarith [ritzHighCoefficient_lt_printed]
  · nlinarith

/-- The exact lower individual-angle bound is below its printed rational bound, on
`0 < ε < 100`. -/
lemma lowerIndividualAngleExactBound_lt_printed (ε : ℝ)
    (hε : 0 < ε) (hε100 : ε < 100) :
    lowerIndividualAngleExactBound ε <
      ((53 : ℝ) / 100000 * ε) /
        (1 - (43 : ℝ) / 100000 * ε) := by
  unfold lowerIndividualAngleExactBound
  apply ratio_strict_mono hε (by positivity)
  · nlinarith [sqrt7_lt_53_div_20]
  · nlinarith [ritzLowCoefficient_lt_printed]
  · nlinarith

/-- The exact upper individual-angle bound is below its printed rational bound, on
`0 < ε < 100`. -/
lemma upperIndividualAngleExactBound_lt_printed (ε : ℝ)
    (hε : 0 < ε) (hε100 : ε < 100) :
    upperIndividualAngleExactBound ε <
      ((53 : ℝ) / 100000 * ε) /
        (1 - (1 : ℝ) / 625 * ε) := by
  unfold upperIndividualAngleExactBound
  apply ratio_strict_mono hε (by positivity)
  · nlinarith [sqrt7_lt_53_div_20]
  · nlinarith [ritzHighCoefficient_lt_printed]
  · nlinarith

/-! ## Printed equations as consequences of exact theorem outputs -/

/-- Equation (9.1). -/
theorem equation_9_1
    (ε sinTheta₁ : ℝ) (hε : 0 < ε)
    (h : sinTheta₁ ≤ residualTopSingularValue ε / 500) :
    sinTheta₁ < (811 : ℝ) / 500000 * ε :=
  h.trans_lt (initial_sin_exact_lt_printed ε hε)

/-- Equation (9.2).  The strict premise records that the spectral separation is
strictly larger than 500. -/
theorem equation_9_2
    (ε sinTwoTheta₁ : ℝ)
    (h : sinTwoTheta₁ < 2 * ε / 500) :
    sinTwoTheta₁ < (1 : ℝ) / 250 * ε := by
  (convert h using 1; ring)

/-- Equation (9.3). -/
theorem equation_9_3
    (ε sinThetaSum : ℝ) (hε : 0 < ε)
    (h : sinThetaSum ≤ residualKyFanTwo ε / 500) :
    sinThetaSum < (109 : ℝ) / 50000 * ε :=
  h.trans_lt (initial_kyFanTwo_exact_lt_printed ε hε)

/-- Equation (9.4). -/
theorem equation_9_4
    (ε sinTwoThetaSum : ℝ)
    (h : sinTwoThetaSum < 4 * ε / 500) :
    sinTwoThetaSum < (1 : ℝ) / 125 * ε := by
  (convert h using 1; ring)

/-- Equation (9.5), lower Ritz value. -/
theorem equation_9_5_low (ε : ℝ) :
    ritzLow ε = ε / 2 * (1 - (Real.sqrt 3)⁻¹) := by
  unfold ritzLow ritzLowCoefficient
  rw [inv_sqrt_three_eq]
  ring

/-- Equation (9.5), upper Ritz value. -/
theorem equation_9_5_high (ε : ℝ) :
    ritzHigh ε = ε / 2 * (1 + (Real.sqrt 3)⁻¹) := by
  unfold ritzHigh ritzHighCoefficient
  rw [inv_sqrt_three_eq]
  ring

/-- Equation (9.6). -/
theorem equation_9_6
    (ε tanTheta₁ : ℝ) (hε : 0 < ε) (hε100 : ε < 100)
    (h : tanTheta₁ ≤ tangentThetaExactBound ε) :
    tanTheta₁ <
      ((1291 : ℝ) / 2500000 * ε) /
        (1 - (7887 : ℝ) / 5000000 * ε) :=
  h.trans_lt (tangentThetaExactBound_lt_printed ε hε hε100)

/-- Equation (9.7). -/
theorem equation_9_7
    (ε tanTwoTheta₁ : ℝ) (hε : 0 < ε) (hε100 : ε < 100)
    (h : tanTwoTheta₁ ≤ tangentTwoThetaExactBound ε) :
    tanTwoTheta₁ <
      ((1291 : ℝ) / 1250000 * ε) /
        (1 - (7887 : ℝ) / 5000000 * ε) :=
  h.trans_lt (tangentTwoThetaExactBound_lt_printed ε hε hε100)

/-- The sharper one-vector lower-Ritz estimate following equation (9.8). -/
theorem direct_lower_individual_vector_bound
    (ε tanPhi₁ : ℝ) (hε : 0 < ε) (hε100 : ε < 100)
    (h : tanPhi₁ ≤ lowerIndividualTangentExactBound ε) :
    tanPhi₁ <
      ((913 : ℝ) / 2500000 * ε) /
        (1 - (4227 : ℝ) / 10000000 * ε) :=
  h.trans_lt (lowerIndividualTangentExactBound_lt_printed ε hε hε100)

/-- The sharper one-vector upper-Ritz estimate following equation (9.8). -/
theorem direct_upper_individual_vector_bound
    (ε tanPhi₂ : ℝ) (hε : 0 < ε) (hε100 : ε < 100)
    (h : tanPhi₂ ≤ upperIndividualTangentExactBound ε) :
    tanPhi₂ <
      ((913 : ℝ) / 2500000 * ε) /
        (1 - (7887 : ℝ) / 5000000 * ε) :=
  h.trans_lt (upperIndividualTangentExactBound_lt_printed ε hε hε100)

/-- Final lower-eigenvector angle bound in Section 9. -/
theorem final_lower_individual_angle_bound
    (ε omega₁ : ℝ) (hε : 0 < ε) (hε100 : ε < 100)
    (h : omega₁ ≤ lowerIndividualAngleExactBound ε) :
    omega₁ <
      ((53 : ℝ) / 100000 * ε) /
        (1 - (43 : ℝ) / 100000 * ε) :=
  h.trans_lt (lowerIndividualAngleExactBound_lt_printed ε hε hε100)

/-- Final upper-eigenvector angle bound in Section 9. -/
theorem final_upper_individual_angle_bound
    (ε omega₂ : ℝ) (hε : 0 < ε) (hε100 : ε < 100)
    (h : omega₂ ≤ upperIndividualAngleExactBound ε) :
    omega₂ <
      ((53 : ℝ) / 100000 * ε) /
        (1 - (1 : ℝ) / 625 * ε) :=
  h.trans_lt (upperIndividualAngleExactBound_lt_printed ε hε hε100)

end Section9
end DavisKahan1970
end TauCeti
