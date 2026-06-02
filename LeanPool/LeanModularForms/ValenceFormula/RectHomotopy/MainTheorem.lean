/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import LeanPool.LeanModularForms.GeneralizedResidueTheory.Homotopy.CircleParam
import LeanPool.LeanModularForms.ValenceFormula.RectHomotopy.BoundaryHomotopyDiff
import LeanPool.LeanModularForms.ValenceFormula.RectHomotopy.MainTheoremBound
import LeanPool.LeanModularForms.ValenceFormula.RectHomotopy.MainTheoremDerivCont
import LeanPool.LeanModularForms.ValenceFormula.RectHomotopy.WindingProof

/-!
# Main winding number theorem for the fundamental domain boundary

The generalized winding number of `fdBoundary` around
interior points equals -1 (clockwise).
-/

open Complex Set Metric Filter Topology

namespace RectHomotopyProof

private lemma fdBoundaryToPolygonHomotopy_diffAt_off_partition
    (t : ℝ) (ht : t ∈ Ioo 0 5) (ht_not_P : t ∉ ({1, 2, 3, 4} : Finset ℝ))
    (s : ℝ) (_hs : s ∈ Icc (0 : ℝ) 1) :
    DifferentiableAt ℝ (fun t' => fdBoundaryToPolygonHomotopy (t', s)) t := by
  simp only [Finset.mem_insert,
    Finset.mem_singleton, not_or] at ht_not_P
  obtain ⟨hne1, hne2, hne3, hne4⟩ := ht_not_P
  by_cases h1 : t < 1
  · have heq : (fun t' : ℝ =>
          fdBoundaryToPolygonHomotopy (t', s)) =ᶠ[𝓝 t]
        (fun t' : ℝ => (1/2 : ℂ) +
            (HHeight - (↑t' : ℂ) * (HHeight -
                Real.sqrt 3 / 2)) * I) := by
      filter_upwards [eventually_lt_nhds h1]
        with t' ht'
      simp only [fdBoundaryToPolygonHomotopy,
        le_of_lt ht', ite_true]
    exact heq.differentiableAt_iff.mpr (fdBoundaryToPolygonHomotopy_seg1_differentiable
        t s)
  · push Not at h1
    by_cases h2 : t < 2
    · have ht1 : t > 1 :=
        lt_of_le_of_ne h1 (Ne.symm hne1)
      have heq : (fun t' : ℝ =>
            fdBoundaryToPolygonHomotopy (t', s)) =ᶠ[𝓝 t]
          (fun t' : ℝ =>
            let arc_point :=
              Complex.exp ((Real.pi / 3 +
                  (t' - 1) * (Real.pi / 2 -
                      Real.pi / 3)) * I)
            let chord_point :=
              chordSegment rho' iPoint (t' - 1)
            (1 - s) • arc_point +
              s • chord_point) := by
        filter_upwards [
          eventually_gt_nhds ht1,
          eventually_lt_nhds h2]
          with t' ht1' ht2'
        simp only [fdBoundaryToPolygonHomotopy]
        simp only [not_le.mpr ht1', ite_false,
          le_of_lt ht2', ite_true]
      exact heq.differentiableAt_iff.mpr (fdBoundaryToPolygonHomotopy_seg2_differentiable
          t s)
    · push Not at h2
      by_cases h3 : t < 3
      · have ht2 : t > 2 :=
          lt_of_le_of_ne h2 (Ne.symm hne2)
        have heq : (fun t' : ℝ =>
              fdBoundaryToPolygonHomotopy (t', s)) =ᶠ[𝓝 t]
            (fun t' : ℝ =>
              let arc_point :=
                Complex.exp ((Real.pi / 2 +
                    (t' - 2) * (2 * Real.pi / 3 -
                        Real.pi / 2)) * I)
              let chord_point :=
                chordSegment iPoint rho (t' - 2)
              (1 - s) • arc_point +
                s • chord_point) := by
          filter_upwards [
            eventually_gt_nhds ht2,
            eventually_lt_nhds h3]
            with t' ht2' ht3'
          simp only [fdBoundaryToPolygonHomotopy]
          simp only [
            not_le.mpr (lt_trans (by norm_num : (1 : ℝ) < 2) ht2'),
            ite_false, not_le.mpr ht2',
            le_of_lt ht3', ite_true]
        exact heq.differentiableAt_iff.mpr (fdBoundaryToPolygonHomotopy_seg3_differentiable
            t s)
      · push Not at h3
        by_cases h4 : t < 4
        · have ht3 : t > 3 :=
            lt_of_le_of_ne h3 (Ne.symm hne3)
          have heq : (fun t' : ℝ =>
                fdBoundaryToPolygonHomotopy (t', s)) =ᶠ[𝓝 t]
              (fun t' : ℝ => (-1/2 : ℂ) +
                  (Real.sqrt 3 / 2 + ((↑t' : ℂ) - 3) *
                      (HHeight -
                        Real.sqrt 3 / 2)) *
                    I) := by
            filter_upwards [
              eventually_gt_nhds ht3,
              eventually_lt_nhds h4]
              with t' ht3' ht4'
            simp only
              [fdBoundaryToPolygonHomotopy]
            simp only [
              not_le.mpr (lt_trans (by norm_num : (1 : ℝ) < 3)
                ht3'),
              ite_false,
              not_le.mpr (lt_trans (by norm_num : (2 : ℝ) < 3)
                ht3'),
              not_le.mpr ht3',
              le_of_lt ht4', ite_true]
          exact heq.differentiableAt_iff.mpr (fdBoundaryToPolygonHomotopy_seg4_differentiable
              t s)
        · push Not at h4
          have ht4 : t > 4 :=
            lt_of_le_of_ne h4 (Ne.symm hne4)
          have ht5 : t < 5 := ht.2
          have heq : (fun t' : ℝ =>
                fdBoundaryToPolygonHomotopy (t', s)) =ᶠ[𝓝 t]
              (fun t' : ℝ => ((↑t' : ℂ) - 9/2) +
                  HHeight * I) := by
            filter_upwards [
              eventually_gt_nhds ht4,
              eventually_lt_nhds ht5]
              with t' ht4' _ht5'
            simp only
              [fdBoundaryToPolygonHomotopy]
            simp only [
              not_le.mpr (lt_trans (by norm_num : (1 : ℝ) < 4)
                ht4'),
              ite_false,
              not_le.mpr (lt_trans (by norm_num : (2 : ℝ) < 4)
                ht4'),
              not_le.mpr (lt_trans (by norm_num : (3 : ℝ) < 4)
                ht4'),
              not_le.mpr ht4']
          exact heq.differentiableAt_iff.mpr (fdBoundaryToPolygonHomotopy_seg5_differentiable
              t s)

private lemma fdBoundaryToPolygonHomotopy_piecewise (p : ℂ) (hp_norm : ‖p‖ > 1)
    (hp_re : |p.re| < 1 / 2) (hp_im : p.im < HHeight) :
    let P : Finset ℝ := {1, 2, 3, 4}
    PiecewiseCurvesHomotopicAvoiding
      fdBoundary fdPolygon 0 5 p P :=
  ⟨fdBoundaryToPolygonHomotopy,
   fdBoundaryToPolygonHomotopy_continuous,
   fun t ht =>
    fdBoundaryToPolygonHomotopy_at_zero t ht,
   fun t ht =>
    fdBoundaryToPolygonHomotopy_at_one t ht,
   fun s hs =>
    fdBoundaryToPolygonHomotopy_closed s hs,
   fun t ht s hs =>
    fdBoundaryToPolygonHomotopy_avoids p
      hp_norm hp_re hp_im t ht s hs,
   fun t ht ht_not_P s hs =>
    fdBoundaryToPolygonHomotopy_diffAt_off_partition
      t ht ht_not_P s hs,
   fun p₁ p₂ hp hpiece hsub =>
    fdBoundaryToPolygonHomotopy_deriv_continuousOn_pieces
      p₁ p₂ hp hpiece hsub,
   fdBoundaryToPolygonHomotopy_deriv_bound⟩

/-- For interior points p in the fundamental domain,
    the generalized winding number of the FD boundary
    around p equals -1 (clockwise orientation). -/
theorem generalizedWindingNumber_fdBoundary_eq_neg_one (p : ℂ) (hp_norm : ‖p‖ > 1)
    (hp_re : |p.re| < 1 / 2) (hp_im_pos : 0 < p.im)
    (hp_im : p.im < HHeight) :
    generalizedWindingNumber' fdBoundary 0 5 p = -1 := by
  have h_wind_eq1 :
      generalizedWindingNumber' fdBoundary 0 5 p =
      generalizedWindingNumber' fdPolygon 0 5 p :=
    windingNumber_eq_of_piecewise_homotopic
      fdBoundary fdPolygon 0 5 p {1, 2, 3, 4} (by norm_num)
      (fdBoundaryToPolygonHomotopy_piecewise p hp_norm hp_re hp_im)
  have h_wind_eq2 :
      generalizedWindingNumber' fdPolygon 0 5 p =
      generalizedWindingNumber' (circleParamCW p 1 0 5) 0 5 p :=
    winding_fdPolygon_eq_circleParamCW p
      hp_norm hp_re hp_im_pos hp_im
  rw [h_wind_eq1, h_wind_eq2,
    circleParamCW_winding_eq_neg_one p 1 (by norm_num : (0 : ℝ) < 1) 0 5 (by norm_num)]

end RectHomotopyProof
