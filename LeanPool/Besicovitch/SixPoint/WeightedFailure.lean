/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import LeanPool.Besicovitch.SixPoint.RationalChord
public import LeanPool.Besicovitch.SixPoint.EndpointWeights
public import LeanPool.Besicovitch.SixPoint.RootEdgeFailureTree

/-!
# The three active six-point failure slacks

The surviving path through the packing failure tree produces three scalar inequalities. This file
names those natural slacks and identifies their positive weighted sum with the coordinate-free
weighted pair score.
-/

@[expose] public section

noncomputable section

namespace LeanPool.Besicovitch

/-- The weakened diagonal-matching slack `q1`. -/
def firstActiveFailureSlack (configuration : SixPointConfiguration) : ℝ :=
  dist (configuration .red .left) (configuration .blue .left) +
    dist (configuration .red .right) (configuration .blue .right) -
      2 * barC * (2 * barC - 1)

/-- The coincident sibling-endpoint slack `q2`. -/
def secondActiveFailureSlack (configuration : SixPointConfiguration) : ℝ :=
  dist (configuration .red .left) (configuration .blue .left) -
    ((barC - 1) * matchedChildAverage configuration 0 +
      (barC + 1) * matchedChildAverage configuration 1 +
      3 * barC ^ 2 - 3 * barC + 2) / 2

/-- The balanced root--edge slack `q3`. -/
def thirdActiveFailureSlack (configuration : SixPointConfiguration) : ℝ :=
  (dist (configuration .red .left) (configuration .blue .root) +
      dist (configuration .red .root) (configuration .blue .left) +
      dist (configuration .red .left) (configuration .blue .right) +
      dist (configuration .red .right) (configuration .blue .left)) / 2 -
    ((barC - 1) * matchedChildAverage configuration 0 +
      3 * barC * matchedChildAverage configuration 1 + barC ^ 2 - barC)

/-- The selected diagonal matching makes `q1` nonnegative. -/
theorem firstActiveFailureSlack_nonneg
    {configuration : SixPointConfiguration} (h : configuration.IsAdmissibleAt barS)
    (hmatching : SelectedDiagonalMatchingFails configuration) :
    0 ≤ firstActiveFailureSlack configuration := by
  have hL := (sibling_distance_mem_endpoint_interval h .red).1
  have hM := (sibling_distance_mem_endpoint_interval h .blue).1
  have hcoefficient : 0 ≤ 2 * barC - 1 := by
    nlinarith [one_lt_barC_and_barC_lt_two.1]
  have hscaled := mul_le_mul_of_nonneg_left (show 2 * barC ≤
      dist (configuration .red .left) (configuration .red .right) +
        dist (configuration .blue .left) (configuration .blue .right) by linarith)
    hcoefficient
  simp [firstActiveFailureSlack, SelectedDiagonalMatchingFails, incidenceCrossDistance,
    incidenceChild] at hmatching ⊢
  nlinarith

/-- Coincident endpoint failures at `B11` make `q2` strictly positive. -/
theorem secondActiveFailureSlack_pos
    {configuration : SixPointConfiguration} (h : configuration.IsAdmissibleAt barS)
    (hred : redSiblingTriangleFailure configuration (.endpoint 0))
    (hblue : blueSiblingTriangleFailure configuration (.endpoint 0)) :
    0 < secondActiveFailureSlack configuration := by
  exact sub_pos.mpr (q2_strict_of_matched_endpoint_zero h hred hblue)

/-- The two surviving `(1,1)` root--edge terms make `q3` strictly positive. -/
theorem thirdActiveFailureSlack_pos
    {configuration : SixPointConfiguration} (h : configuration.IsAdmissibleAt barS)
    (hred : 2 * redRootEdgeTarget configuration <
      dist (configuration .red .root) (configuration .red .right) +
        redRootBlueTriangleReach configuration .left +
        redChildBlueTriangleReach configuration .right .left)
    (hblue : 2 * blueRootEdgeTarget configuration <
      dist (configuration .blue .root) (configuration .blue .right) +
        blueRootRedTriangleReach configuration .left +
        blueChildRedTriangleReach configuration .right .left) :
    0 < thirdActiveFailureSlack configuration := by
  have hL := (sibling_distance_mem_endpoint_interval h .red).1
  have hM := (sibling_distance_mem_endpoint_interval h .blue).1
  have hcoefficient : 0 ≤ barC - 1 := by
    nlinarith [one_lt_barC_and_barC_lt_two.1]
  have hsiblingScaled := mul_le_mul_of_nonneg_left (show 2 * barC ≤
      dist (configuration .red .left) (configuration .red .right) +
        dist (configuration .blue .left) (configuration .blue .right) by linarith)
    hcoefficient
  simp [redRootEdgeTarget, blueRootEdgeTarget, rootedTriangleTotalRadius,
    redRootBlueTriangleReach, redChildBlueTriangleReach, blueRootRedTriangleReach,
    blueChildRedTriangleReach, canonicalTriangleRadius] at hred hblue
  simp only [thirdActiveFailureSlack, matchedChildAverage, incidenceChild]
  rw [dist_comm (configuration .blue .root) (configuration .red .left),
    dist_comm (configuration .blue .right) (configuration .red .left)] at hblue
  nlinarith

/-- The weighted score of the displacement pairs is exactly `q1 + lambda*q2 + mu*q3`. -/
theorem weightedPairScore_configuration_eq_activeFailureCombination
    (configuration : SixPointConfiguration) (lambda mu : ℝ) :
    weightedPairScore configuration.rootDisplacement barC lambda mu
        (configuration.redDisplacement .left) (configuration.redDisplacement .right)
        (configuration.bluePullback .left) (configuration.bluePullback .right) =
      firstActiveFailureSlack configuration +
        lambda * secondActiveFailureSlack configuration +
        mu * thirdActiveFailureSlack configuration := by
  have hB₁₁ := configuration.dist_red_blue_eq_norm .left .left
  have hB₂₂ := configuration.dist_red_blue_eq_norm .right .right
  have hB₁₂ := configuration.dist_red_blue_eq_norm .left .right
  have hB₂₁ := configuration.dist_red_blue_eq_norm .right .left
  have hAred :
      dist (configuration .red .left) (configuration .blue .root) =
        ‖configuration.rootDisplacement - configuration.redDisplacement .left‖ := by
    simpa [SixPointConfiguration.bluePullback] using
      configuration.dist_red_blue_eq_norm .left .root
  have hAblue :
      dist (configuration .red .root) (configuration .blue .left) =
        ‖configuration.rootDisplacement - configuration.bluePullback .left‖ := by
    simpa [SixPointConfiguration.redDisplacement] using
      configuration.dist_red_blue_eq_norm .root .left
  have hB₂₁' :
      ‖configuration.rootDisplacement - configuration.bluePullback .left -
          configuration.redDisplacement .right‖ =
        dist (configuration .red .right) (configuration .blue .left) := by
    rw [show configuration.rootDisplacement - configuration.bluePullback .left -
        configuration.redDisplacement .right =
      configuration.rootDisplacement - configuration.redDisplacement .right -
        configuration.bluePullback .left by abel]
    exact hB₂₁.symm
  have hr₁ : ‖configuration.redDisplacement .left‖ =
      dist (configuration .red .root) (configuration .red .left) := by
    simp [SixPointConfiguration.redDisplacement, dist_eq_norm, norm_sub_rev]
  have hr₂ : ‖configuration.redDisplacement .right‖ =
      dist (configuration .red .root) (configuration .red .right) := by
    simp [SixPointConfiguration.redDisplacement, dist_eq_norm, norm_sub_rev]
  have hb₁ : ‖configuration.bluePullback .left‖ =
      dist (configuration .blue .root) (configuration .blue .left) := by
    simp [SixPointConfiguration.bluePullback, dist_eq_norm]
  have hb₂ : ‖configuration.bluePullback .right‖ =
      dist (configuration .blue .root) (configuration .blue .right) := by
    simp [SixPointConfiguration.bluePullback, dist_eq_norm]
  simp only [weightedPairScore, firstActiveFailureSlack, secondActiveFailureSlack,
    thirdActiveFailureSlack, matchedChildAverage, incidenceChild, weightedFirstPenalty,
    weightedSecondPenalty, weightedConstantTerm]
  rw [← hB₁₁, ← hB₂₂, ← hB₁₂, hB₂₁', ← hAred, ← hAblue,
    ← hr₁, ← hr₂, ← hb₁, ← hb₂]
  ring

/-- Nonnegative active slacks make their exact weighted combination nonnegative. -/
theorem activeFailureCombination_nonneg {configuration : SixPointConfiguration}
    {lambda mu : ℝ} (hlambda : 0 ≤ lambda) (hmu : 0 ≤ mu)
    (hq₁ : 0 ≤ firstActiveFailureSlack configuration)
    (hq₂ : 0 ≤ secondActiveFailureSlack configuration)
    (hq₃ : 0 ≤ thirdActiveFailureSlack configuration) :
    0 ≤ firstActiveFailureSlack configuration +
      lambda * secondActiveFailureSlack configuration +
      mu * thirdActiveFailureSlack configuration := by
  have hsecond := mul_nonneg hlambda hq₂
  have hthird := mul_nonneg hmu hq₃
  linarith

/-- Strict second and third failure slacks make their weighted combination positive. -/
theorem activeFailureCombination_pos {configuration : SixPointConfiguration}
    {lambda mu : ℝ} (hlambda : 0 < lambda) (hmu : 0 < mu)
    (hq₁ : 0 ≤ firstActiveFailureSlack configuration)
    (hq₂ : 0 < secondActiveFailureSlack configuration)
    (hq₃ : 0 < thirdActiveFailureSlack configuration) :
    0 < firstActiveFailureSlack configuration +
      lambda * secondActiveFailureSlack configuration +
      mu * thirdActiveFailureSlack configuration := by
  have hsecond := mul_pos hlambda hq₂
  have hthird := mul_pos hmu hq₃
  linarith

end LeanPool.Besicovitch
