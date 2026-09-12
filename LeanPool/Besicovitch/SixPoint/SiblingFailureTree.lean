/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import LeanPool.Besicovitch.SixPoint.RationalChord
public import LeanPool.Besicovitch.SixPoint.FailureTree
public import LeanPool.Besicovitch.SixPoint.SiblingIncidenceLedger

/-!
# The sibling-triangle stage of the six-point failure tree

Once the diagonal matching obstruction is selected, supports `67` and `76` either provide a
nonnegative-score packing or route their simultaneous failures into the finite incidence ledger.
-/

@[expose] public section

noncomputable section

namespace LeanPool.Besicovitch

/-- Under the diagonal matching obstruction, the two sibling-triangle supports either win or
produce one of the residual incidence outcomes. -/
theorem exists_nonnegative_score_or_siblingIncidenceOutcome
    (configuration : SixPointConfiguration) (h : configuration.IsAdmissibleAt barS)
    (hmatching : SelectedDiagonalMatchingFails configuration) :
    (∃ packing : SixPointPacking configuration, 0 ≤ packing.score barS) ∨
      SiblingIncidenceOutcome configuration := by
  by_cases hred : RedSiblingTriangleFails configuration h
  · by_cases hblue : BlueSiblingTriangleFails configuration h
    · exact Or.inr (siblingTriangle_score_failure_route h hmatching hred hblue)
    · simp only [BlueSiblingTriangleFails, not_forall, not_lt] at hblue
      obtain ⟨y, hyLower, hyUpper, hscore⟩ := hblue
      exact Or.inl ⟨blueSiblingTrianglePackingAtEndpoint configuration h y hyLower hyUpper,
        hscore⟩
  · simp only [RedSiblingTriangleFails, not_forall, not_lt] at hred
    obtain ⟨x, hxLower, hxUpper, hscore⟩ := hred
    exact Or.inl ⟨redSiblingTrianglePackingAtEndpoint configuration h x hxLower hxUpper,
      hscore⟩

/-- The first two packing stages leave only a sibling incidence or the anti-diagonal matching. -/
theorem exists_nonnegative_score_or_siblingIncidence_or_antiDiagonal
    (configuration : SixPointConfiguration) (h : configuration.IsAdmissibleAt barS) :
    (∃ packing : SixPointPacking configuration, 0 ≤ packing.score barS) ∨
      SiblingIncidenceOutcome configuration ∨
      (2 * barC - 1) *
          (dist (configuration .red .left) (configuration .red .right) +
            dist (configuration .blue .left) (configuration .blue .right)) ≤
        dist (configuration .red .left) (configuration .blue .right) +
          dist (configuration .red .right) (configuration .blue .left) := by
  rcases exists_nonnegative_score_or_matching_obstruction configuration h with
    hpacking | hdiagonal | hantiDiagonal
  · exact Or.inl hpacking
  · rcases exists_nonnegative_score_or_siblingIncidenceOutcome configuration h hdiagonal with
      hpacking | houtcome
    · exact Or.inl hpacking
    · exact Or.inr (Or.inl houtcome)
  · exact Or.inr (Or.inr hantiDiagonal)

end LeanPool.Besicovitch
