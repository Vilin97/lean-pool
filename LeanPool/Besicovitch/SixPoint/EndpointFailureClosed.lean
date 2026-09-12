/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import LeanPool.Besicovitch.SixPoint.RationalChord
public import LeanPool.Besicovitch.SixPoint.ChildSwapPacking
public import LeanPool.Besicovitch.SixPoint.RootEdgeClosed
public import LeanPool.Besicovitch.SixPoint.WeightedFailure

/-!
# Closing the matched-endpoint branch

At a matched sibling endpoint, failure of both root--edge packings makes the three active slacks
strictly incompatible with the weighted geometric bound.  The other matched endpoint follows by
simultaneously swapping both pairs of children.
-/

@[expose] public section

noncomputable section

namespace LeanPool.Besicovitch

/-- The weighted geometric bound closes the endpoint at the two left children. -/
theorem exists_nonnegative_score_of_matched_endpoint_zero
    (configuration : SixPointConfiguration) (h : configuration.IsAdmissibleAt barS)
    {lambda mu : ℝ} (hlambda : 0 < lambda) (hmu : 0 < mu)
    (hmatching : SelectedDiagonalMatchingFails configuration)
    (hred : redSiblingTriangleFailure configuration (.endpoint 0))
    (hblue : blueSiblingTriangleFailure configuration (.endpoint 0))
    (hweighted : weightedPairScore configuration.rootDisplacement barC lambda mu
      (configuration.redDisplacement .left) (configuration.redDisplacement .right)
      (configuration.bluePullback .left) (configuration.bluePullback .right) ≤ 0) :
    ∃ packing : SixPointPacking configuration, 0 ≤ packing.score barS := by
  rcases exists_nonnegative_score_or_rootEdge_type11_pair configuration h hmatching hred hblue with
    hpacking | htype11
  · exact hpacking
  · have hq₁ := firstActiveFailureSlack_nonneg h hmatching
    have hq₂ := secondActiveFailureSlack_pos h hred hblue
    have hq₃ := thirdActiveFailureSlack_pos h htype11.1 htype11.2
    have hpositive := activeFailureCombination_pos hlambda hmu hq₁ hq₂ hq₃
    rw [← weightedPairScore_configuration_eq_activeFailureCombination] at hpositive
    exact (not_lt_of_ge hweighted hpositive).elim

/-- The weighted geometric bound closes the endpoint at the two right children. -/
theorem exists_nonnegative_score_of_matched_endpoint_three
    (configuration : SixPointConfiguration) (h : configuration.IsAdmissibleAt barS)
    {lambda mu : ℝ} (hlambda : 0 < lambda) (hmu : 0 < mu)
    (hmatching : SelectedDiagonalMatchingFails configuration)
    (hred : redSiblingTriangleFailure configuration (.endpoint 3))
    (hblue : blueSiblingTriangleFailure configuration (.endpoint 3))
    (hweighted :
      weightedPairScore (swapConfigurationChildren configuration).rootDisplacement
        barC lambda mu
        ((swapConfigurationChildren configuration).redDisplacement .left)
        ((swapConfigurationChildren configuration).redDisplacement .right)
        ((swapConfigurationChildren configuration).bluePullback .left)
        ((swapConfigurationChildren configuration).bluePullback .right) ≤ 0) :
    ∃ packing : SixPointPacking configuration, 0 ≤ packing.score barS := by
  let swapped := swapConfigurationChildren configuration
  have hadmissible : swapped.IsAdmissibleAt barS := IsAdmissibleAt.swapChildren h
  have hmatching' : SelectedDiagonalMatchingFails swapped :=
    (selectedDiagonalMatchingFails_swapChildren configuration).2 hmatching
  have hred' : redSiblingTriangleFailure swapped (.endpoint 0) :=
    (redEndpointFailure_swapChildren configuration 3).2 hred
  have hblue' : blueSiblingTriangleFailure swapped (.endpoint 0) :=
    (blueEndpointFailure_swapChildren configuration 3).2 hblue
  obtain ⟨packing, hscore⟩ := exists_nonnegative_score_of_matched_endpoint_zero swapped
    hadmissible hlambda hmu hmatching' hred' hblue' hweighted
  exact ⟨packing.unswapChildren, by simpa only [packing.unswapChildren_score] using hscore⟩

end LeanPool.Besicovitch
