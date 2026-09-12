/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import LeanPool.Besicovitch.SixPoint.RationalChord
public import LeanPool.Besicovitch.SixPoint.BlueChildSwap
public import LeanPool.Besicovitch.SixPoint.EndpointFailureClosed
public import LeanPool.Besicovitch.SixPoint.FiniteProperty
public import LeanPool.Besicovitch.SixPoint.SiblingIncidenceClosed

/-!
# The endpoint packing theorem

This file assembles the finite failure tree.  Its sole analytic input is the weighted geometric
bound for two ordered chords in the unit disk.
-/

@[expose] public section

noncomputable section

namespace LeanPool.Besicovitch

/-- The weighted geometric inequality for two ordered sibling pairs in the unit disk. -/
def WeightedGeometricBound (lambda mu : ℝ) : Prop :=
  ∀ e p₁ p₂ w₁ w₂ : (EuclideanSpace ℝ (Fin 2)),
    ‖e‖ = 1 →
    ‖p₁‖ ≤ 1 → ‖p₂‖ ≤ 1 → ‖w₁‖ ≤ 1 → ‖w₂‖ ≤ 1 →
    barC ≤ ‖p₁ - p₂‖ → barC ≤ ‖w₁ - w₂‖ →
    weightedPairScore e barC lambda mu p₁ p₂ w₁ w₂ ≤ 0

private theorem weightedGeometricBound_configuration {lambda mu : ℝ}
    (hweighted : WeightedGeometricBound lambda mu) {configuration : SixPointConfiguration}
    (h : configuration.IsAdmissibleAt barS) :
    weightedPairScore configuration.rootDisplacement barC lambda mu
      (configuration.redDisplacement .left) (configuration.redDisplacement .right)
      (configuration.bluePullback .left) (configuration.bluePullback .right) ≤ 0 := by
  apply hweighted
  · exact configuration.norm_rootDisplacement h
  · exact configuration.norm_redDisplacement_le_one h (by simp)
  · exact configuration.norm_redDisplacement_le_one h (by simp)
  · exact configuration.norm_bluePullback_le_one h (by simp)
  · exact configuration.norm_bluePullback_le_one h (by simp)
  · have hchord := configuration.two_mul_le_dist_redDisplacement h
    rw [barS, dist_eq_norm] at hchord
    convert hchord using 1
    ring
  · have hchord := configuration.two_mul_le_dist_bluePullback h
    rw [barS, dist_eq_norm] at hchord
    convert hchord using 1
    ring

private theorem exists_nonnegative_score_of_selected_diagonal {lambda mu : ℝ}
    (hlambda : 0 < lambda) (hmu : 0 < mu)
    (hweighted : WeightedGeometricBound lambda mu) (configuration : SixPointConfiguration)
    (h : configuration.IsAdmissibleAt barS)
    (hmatching : SelectedDiagonalMatchingFails configuration) :
    ∃ packing : SixPointPacking configuration, 0 ≤ packing.score barS := by
  rcases exists_nonnegative_score_or_matched_sibling_endpoint configuration h hmatching with
    hpacking | ⟨code, hcode, hred, hblue⟩
  · exact hpacking
  · rcases hcode with rfl | rfl
    · exact exists_nonnegative_score_of_matched_endpoint_zero configuration h hlambda hmu
        hmatching hred hblue (weightedGeometricBound_configuration hweighted h)
    · exact exists_nonnegative_score_of_matched_endpoint_three configuration h hlambda hmu
        hmatching hred hblue
        (weightedGeometricBound_configuration hweighted (IsAdmissibleAt.swapChildren h))

/-- The weighted geometric bound implies the finite six-point property at the exact endpoint. -/
theorem sixPointFiniteProperty_barS_of_weightedGeometricBound {lambda mu : ℝ}
    (hlambda : 0 < lambda) (hmu : 0 < mu)
    (hweighted : WeightedGeometricBound lambda mu) : SixPointFiniteProperty barS := by
  intro configuration h
  rcases exists_nonnegative_score_or_matching_obstruction configuration h with
    hpacking | hdiagonal | hantiDiagonal
  · exact hpacking
  · exact exists_nonnegative_score_of_selected_diagonal hlambda hmu hweighted configuration h
      hdiagonal
  · let swapped := swapBlueChildren configuration
    have hadmissible : swapped.IsAdmissibleAt barS := IsAdmissibleAt.swapBlueChildren h
    have hmatching : SelectedDiagonalMatchingFails swapped :=
      (selectedDiagonalMatchingFails_swapBlueChildren configuration).2 hantiDiagonal
    obtain ⟨packing, hscore⟩ :=
      exists_nonnegative_score_of_selected_diagonal hlambda hmu hweighted swapped hadmissible
        hmatching
    exact ⟨packing.unswapBlue, by simpa only [packing.unswapBlue_score] using hscore⟩

end LeanPool.Besicovitch
