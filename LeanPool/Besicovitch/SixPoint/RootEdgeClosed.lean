/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import LeanPool.Besicovitch.SixPoint.RationalChord
public import LeanPool.Besicovitch.SixPoint.RootEdgeFailureTree
public import LeanPool.Besicovitch.SixPoint.RootEdgeType12

/-!
# Closing the root--edge failure stage

The crossed `(1,2)` separator removes the second branch of each root--edge minimax.  Thus the two
root--edge supports either provide a nonnegative packing or both select their `(1,1)` terms.
-/

@[expose] public section

noncomputable section

namespace LeanPool.Besicovitch

/-- The selected matching and endpoint force a failed red root--edge support onto `(1,1)`. -/
theorem redRootEdge_failure_forces_type11
    {configuration : SixPointConfiguration} (h : configuration.IsAdmissibleAt barS)
    (hmatching : SelectedDiagonalMatchingFails configuration)
    (hendpoint : redSiblingTriangleFailure configuration (.endpoint 0))
    (hfailure : RedRootEdgeFails configuration h) :
    2 * redRootEdgeTarget configuration <
      dist (configuration .red .root) (configuration .red .right) +
        redRootBlueTriangleReach configuration .left +
        redChildBlueTriangleReach configuration .right .left := by
  rcases redRootEdge_failure_routes_to_child_balanced h hmatching hendpoint hfailure with
    htype11 | htype12
  · exact htype11
  · have hnegative :=
      configuration.redRootEdgeType12Slack_neg_of_matching_endpoint h hmatching hendpoint
    simp only [redRootEdgeType12Slack] at hnegative
    simp only [redRootEdgeTarget, rootedTriangleTotalRadius, redRootBlueTriangleReach,
      redChildBlueTriangleReach, canonicalTriangleRadius] at htype12
    linarith

/-- The selected matching and endpoint force a failed blue root--edge support onto `(1,1)`. -/
theorem blueRootEdge_failure_forces_type11
    {configuration : SixPointConfiguration} (h : configuration.IsAdmissibleAt barS)
    (hmatching : SelectedDiagonalMatchingFails configuration)
    (hendpoint : blueSiblingTriangleFailure configuration (.endpoint 0))
    (hfailure : BlueRootEdgeFails configuration h) :
    2 * blueRootEdgeTarget configuration <
      dist (configuration .blue .root) (configuration .blue .right) +
        blueRootRedTriangleReach configuration .left +
        blueChildRedTriangleReach configuration .right .left := by
  rcases blueRootEdge_failure_routes_to_child_balanced h hmatching hendpoint hfailure with
    htype11 | htype12
  · exact htype11
  · let transposed := transposeConfigurationColors configuration
    have hnegative :=
      SixPointConfiguration.redRootEdgeType12Slack_neg_of_matching_endpoint transposed
        (IsAdmissibleAt.transposeColors h)
        ((selectedDiagonalMatchingFails_transposeColors configuration).2 hmatching)
        ((redEndpointFailure_transposeColors configuration 0).2 hendpoint)
    simp only [redRootEdgeType12Slack, transposed, transposeConfigurationColors] at hnegative
    simp only [blueRootEdgeTarget, rootedTriangleTotalRadius, blueRootRedTriangleReach,
      blueChildRedTriangleReach, canonicalTriangleRadius] at htype12
    rw [dist_comm (configuration .blue .right) (configuration .red .right)] at hnegative
    rw [dist_comm (configuration .blue .right) (configuration .red .right)] at htype12
    linarith

/-- The two root--edge supports either win or both leave the active `(1,1)` inequalities. -/
theorem exists_nonnegative_score_or_rootEdge_type11_pair
    (configuration : SixPointConfiguration) (h : configuration.IsAdmissibleAt barS)
    (hmatching : SelectedDiagonalMatchingFails configuration)
    (hredEndpoint : redSiblingTriangleFailure configuration (.endpoint 0))
    (hblueEndpoint : blueSiblingTriangleFailure configuration (.endpoint 0)) :
    (∃ packing : SixPointPacking configuration, 0 ≤ packing.score barS) ∨
      (2 * redRootEdgeTarget configuration <
          dist (configuration .red .root) (configuration .red .right) +
            redRootBlueTriangleReach configuration .left +
            redChildBlueTriangleReach configuration .right .left ∧
        2 * blueRootEdgeTarget configuration <
          dist (configuration .blue .root) (configuration .blue .right) +
            blueRootRedTriangleReach configuration .left +
            blueChildRedTriangleReach configuration .right .left) := by
  by_cases hred : RedRootEdgeFails configuration h
  · by_cases hblue : BlueRootEdgeFails configuration h
    · exact Or.inr ⟨redRootEdge_failure_forces_type11 h hmatching hredEndpoint hred,
        blueRootEdge_failure_forces_type11 h hmatching hblueEndpoint hblue⟩
    · simp only [BlueRootEdgeFails, not_forall, not_lt] at hblue
      obtain ⟨x, hxZero, hxEdge, hscore⟩ := hblue
      exact Or.inl ⟨blueRootEdgePackingAtEndpoint configuration h x hxZero hxEdge, hscore⟩
  · simp only [RedRootEdgeFails, not_forall, not_lt] at hred
    obtain ⟨x, hxZero, hxEdge, hscore⟩ := hred
    exact Or.inl ⟨redRootEdgePackingAtEndpoint configuration h x hxZero hxEdge, hscore⟩

end LeanPool.Besicovitch
