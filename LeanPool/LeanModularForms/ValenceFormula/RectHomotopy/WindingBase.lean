/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import LeanPool.LeanModularForms.ValenceFormula.RectHomotopy.AngleAnalysis
import LeanPool.LeanModularForms.GeneralizedResidueTheory.CurveAvoidance

/-!
# Winding number base lemmas

Establishes that the straight line from any interior point to the reference point
refP₀ avoids the fdPolygon boundary, derives slitPlane membership for the
translated curve, and proves continuity and limit behavior of the argument function
near the branch cut crossing point tL. These results underpin the winding number
computation for the fundamental domain boundary.

* `fdPolygon_avoids_line_to_ref` — line from p to refP₀ avoids fdPolygon
* `rc_sub_ref_p₀_mem_slitPlane` — radial circle minus refP₀ is in slitPlane
* `fdPolygon_sub_ref_p₀_mem_slitPlane` — fdPolygon minus refP₀ is in slitPlane
* `continuousOn_arg_w` — arg of translated curve is continuous away from tL
* `tendsto_arg_w_left`, `tendsto_arg_w_right` — limits of arg at tL from left/right
-/

open Complex Set Metric Filter Topology

namespace RectHomotopyProof

private lemma sqrt_one_minus_sq_plus_linear_ge_one (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    Real.sqrt (1 - x^2) + (2 - Real.sqrt 3) * x ≥ 1 := by
  have hsq3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hsq3_pos : 0 < Real.sqrt 3 := Real.sqrt_pos_of_pos (by norm_num : (0 : ℝ) < 3)
  have hsq3_lt2 : Real.sqrt 3 < 2 := by nlinarith [hsq3]
  have h_2ms_pos : 0 ≤ 2 - Real.sqrt 3 := by linarith
  have h1 : 0 ≤ 1 - x ^ 2 := by nlinarith
  have h_rhs : 0 ≤ 1 - (2 - Real.sqrt 3) * x := by nlinarith [sq_nonneg (Real.sqrt 3 - 1)]
  suffices h : Real.sqrt (1 - x ^ 2) ≥ 1 - (2 - Real.sqrt 3) * x by linarith
  rw [ge_iff_le, ← Real.sqrt_sq h_rhs]
  apply Real.sqrt_le_sqrt
  have key : x * ((8 - 4 * Real.sqrt 3) * x - (4 - 2 * Real.sqrt 3)) ≤ 0 := by
    apply mul_nonpos_of_nonneg_of_nonpos hx0
    have : (8 - 4 * Real.sqrt 3) * x ≤ (8 - 4 * Real.sqrt 3) * (1/2) := by
      apply mul_le_mul_of_nonneg_left hx1; nlinarith [hsq3]
    linarith
  nlinarith [sq_nonneg (1 - 2*x), sq_nonneg (Real.sqrt 3 * (1 - 2*x)), sq_nonneg x, hsq3, key]

private lemma convex_combo_gt_one' (s A Y₀ : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hY₀ : Y₀ > 1) (hA : A > 1) : (1 - s) * A + s * Y₀ > 1 := by
  rcases eq_or_lt_of_le hs0 with rfl | hs_pos
  · simp only [sub_zero, one_mul, zero_mul, add_zero]; linarith
  rcases eq_or_lt_of_le hs1 with rfl | hs_lt1
  · simp only [sub_self, zero_mul, zero_add, one_mul]; linarith
  · have : (1 - s) * A > (1 - s) := by nlinarith
    have : s * Y₀ > s := by nlinarith
    linarith

private lemma avoids_chord_rho'_to_i (p : ℂ)
    (hp_re : |p.re| < 1 / 2) (hp_im_pos : 0 < p.im)
    (hp_sq : p.re ^ 2 + p.im ^ 2 > 1)
    (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (h1s_nn : 0 ≤ 1 - s)
    (t : ℝ) (ht1 : 1 < t) (ht2 : t ≤ 2)
    (heq_re : (fdPolygon t).re = (1 - s) * p.re)
    (heq_im : (fdPolygon t).im = (1 - s) * p.im + s * refY₀) : False := by
  have hsq3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hsq3_pos : 0 < Real.sqrt 3 := Real.sqrt_pos_of_pos (by norm_num : (0 : ℝ) < 3)
  set u := t - 1 with hu_def
  have hu0 : 0 ≤ u := by linarith
  have hu1 : u ≤ 1 := by linarith
  have hfd : fdPolygon t = chordSegment rho' iPoint u := by
    simp only [fdPolygon, show ¬(t ≤ 1) from not_le.mpr ht1, ↓reduceIte, ht2, hu_def]
  have hfd_re : (fdPolygon t).re = (1 - u) / 2 := by
    rw [hfd]
    simp only [chordSegment, rho', iPoint, real_smul,
      add_re, mul_re, ofReal_re, ofReal_im, I_re, I_im, mul_zero, mul_one,
      sub_zero, zero_mul, add_zero, one_re, div_ofNat_re, div_ofNat_im]
    ring
  have hfd_im : (fdPolygon t).im = (1 - u) * (Real.sqrt 3 / 2) + u := by
    rw [hfd]
    simp only [chordSegment, rho', iPoint, real_smul,
      add_im, mul_im, ofReal_re, ofReal_im, I_re, I_im, mul_zero, mul_one,
      add_zero, zero_mul, one_im,
      div_ofNat_re, div_ofNat_im]
    ring
  rcases le_or_gt 0 p.re with hp_re_nn | hp_re_neg
  · rw [hfd_re] at heq_re
    rw [hfd_im] at heq_im
    have h_1mu : 1 - u = 2 * ((1 - s) * p.re) := by linarith
    have h_u : u = 1 - 2 * ((1 - s) * p.re) := by linarith
    have heq_im' : (1 - s) * (p.im + p.re * (2 - Real.sqrt 3)) + s * refY₀ = 1 := by
      have : (1 - u) * (Real.sqrt 3 / 2) + u =
        1 - (1 - s) * p.re * (2 - Real.sqrt 3) := by
        rw [h_1mu, h_u]; ring
      linarith
    have hp_im_bound : p.im > Real.sqrt (1 - p.re ^ 2) := by
      have h1 : 0 ≤ 1 - p.re ^ 2 := by nlinarith [abs_lt.mp hp_re]
      rw [show p.im = Real.sqrt (p.im ^ 2) from (Real.sqrt_sq (le_of_lt hp_im_pos)).symm]
      exact Real.sqrt_lt_sqrt h1 (by nlinarith)
    have hp_re_le : p.re ≤ 1/2 := by
      rcases abs_le.mp (le_of_lt hp_re) with ⟨_, h⟩; linarith
    have h_combo : p.im + p.re * (2 - Real.sqrt 3) > 1 := by
      have h_ge := sqrt_one_minus_sq_plus_linear_ge_one p.re hp_re_nn hp_re_le
      linarith
    have h_lhs_gt : (1 - s) * (p.im + p.re * (2 - Real.sqrt 3)) + s * refY₀ > 1 :=
      convex_combo_gt_one' s (p.im + p.re * (2 - Real.sqrt 3)) refY₀
        hs0 hs1 ref_Y₀_gt_one h_combo
    linarith
  · rw [hfd_re] at heq_re
    have h_lhs_nn : (1 - u) / 2 ≥ 0 := div_nonneg (by linarith) (by norm_num)
    have h_rhs_le : (1 - s) * p.re ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos h1s_nn (le_of_lt hp_re_neg)
    have h_both_zero : (1 - s) * p.re = 0 ∧ (1 - u) / 2 = 0 := by
      constructor <;> linarith
    have hs_eq : s = 1 := by
      rcases mul_eq_zero.mp h_both_zero.1 with h | h
      · linarith
      · exfalso; linarith
    rw [hs_eq] at heq_im
    simp only [sub_self, zero_mul, zero_add, one_mul] at heq_im
    rw [hfd_im] at heq_im
    have h_bound : (1 - u) * (Real.sqrt 3 / 2) + u ≤ 1 := by
      have : (1 - u) * (Real.sqrt 3 / 2) + u =
          Real.sqrt 3 / 2 + u * (1 - Real.sqrt 3 / 2) := by
        ring
      rw [this]
      have h1 : 1 - Real.sqrt 3 / 2 > 0 := by nlinarith [hsq3]
      have h2 : u * (1 - Real.sqrt 3 / 2) ≤ 1 * (1 - Real.sqrt 3 / 2) :=
        mul_le_mul_of_nonneg_right hu1 (le_of_lt h1)
      linarith
    linarith [ref_Y₀_gt_one]

private lemma avoids_chord_i_to_rho (p : ℂ)
    (hp_re : |p.re| < 1 / 2) (hp_im_pos : 0 < p.im)
    (hp_sq : p.re ^ 2 + p.im ^ 2 > 1)
    (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (_h1s_nn : 0 ≤ 1 - s)
    (t : ℝ) (ht2 : 2 < t) (ht3 : t ≤ 3)
    (heq_re : (fdPolygon t).re = (1 - s) * p.re)
    (heq_im : (fdPolygon t).im = (1 - s) * p.im + s * refY₀) : False := by
  have hsq3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hsq3_pos : 0 < Real.sqrt 3 := Real.sqrt_pos_of_pos (by norm_num : (0 : ℝ) < 3)
  set v := t - 2 with hv_def
  have hv0 : 0 ≤ v := by linarith
  have hv1 : v ≤ 1 := by linarith
  have hfd : fdPolygon t = chordSegment iPoint rho v := by
    simp only [fdPolygon, show ¬(t ≤ 1) from by linarith,
      show ¬(t ≤ 2) from not_le.mpr ht2, ↓reduceIte, ht3, hv_def]
  have hfd_re : (fdPolygon t).re = -v / 2 := by
    rw [hfd]
    simp only [chordSegment, iPoint, rho, real_smul,
      add_re, mul_re, ofReal_re, ofReal_im, I_re, I_im, mul_zero, mul_one,
      sub_zero, zero_mul, one_re,
      div_ofNat_re, div_ofNat_im, neg_re]
    ring
  have hfd_im : (fdPolygon t).im = 1 - v * (1 - Real.sqrt 3 / 2) := by
    rw [hfd]
    simp only [chordSegment, iPoint, rho,
      real_smul, add_im, mul_im, ofReal_re, ofReal_im,
      I_re, I_im, mul_zero, mul_one, add_zero, zero_mul,
      one_im, div_ofNat_re, div_ofNat_im,
      neg_im]
    ring
  rcases le_or_gt p.re 0 with hp_re_np | hp_re_pos
  · rcases eq_or_lt_of_le hp_re_np with hp_re_zero | hp_re_neg
    · rw [hfd_re] at heq_re
      rw [hp_re_zero, mul_zero] at heq_re
      have hv_eq : v = 0 := by linarith
      rw [hfd_im, hv_eq] at heq_im
      simp only [zero_mul, sub_zero] at heq_im
      have hp_im_gt1 : p.im > 1 := by
        have : p.im ^ 2 > 1 := by nlinarith [hp_re_zero]
        nlinarith [sq_nonneg (p.im - 1)]
      have : (1 - s) * p.im + s * refY₀ > 1 :=
        convex_combo_gt_one' s p.im refY₀ hs0 hs1 ref_Y₀_gt_one hp_im_gt1
      linarith
    · rw [hfd_re] at heq_re
      have hv_eq : v = -2 * ((1 - s) * p.re) := by linarith
      have hv_eq' : v = 2 * (1 - s) * (-p.re) := by linarith
      rw [hfd_im] at heq_im
      have heq_im' : (1 - s) * (p.im + (-p.re) * (2 - Real.sqrt 3)) + s * refY₀ = 1 := by
        have : v * (1 - Real.sqrt 3 / 2) = (1 - s) * (-p.re) * (2 - Real.sqrt 3) := by
          rw [hv_eq']; ring
        linarith
      have hp_abs_re : |p.re| = -p.re := abs_of_neg hp_re_neg
      have hp_re_nn' : 0 ≤ -p.re := by linarith
      have hp_re_le' : -p.re ≤ 1/2 := by
        rw [← hp_abs_re]; linarith
      have hp_im_bound : p.im > Real.sqrt (1 - p.re ^ 2) := by
        have h1 : 0 ≤ 1 - p.re ^ 2 := by nlinarith [abs_lt.mp hp_re]
        rw [show p.im = Real.sqrt (p.im ^ 2) from (Real.sqrt_sq (le_of_lt hp_im_pos)).symm]
        exact Real.sqrt_lt_sqrt h1 (by nlinarith)
      have h_neg_re_sq : (-p.re) ^ 2 = p.re ^ 2 := by ring
      have h_combo : p.im + (-p.re) * (2 - Real.sqrt 3) > 1 := by
        have h_ge := sqrt_one_minus_sq_plus_linear_ge_one (-p.re) hp_re_nn' hp_re_le'
        rw [h_neg_re_sq] at h_ge
        linarith
      have h_lhs_gt : (1 - s) * (p.im + (-p.re) * (2 - Real.sqrt 3)) + s * refY₀ > 1 :=
        convex_combo_gt_one' s (p.im + (-p.re) * (2 - Real.sqrt 3)) refY₀
          hs0 hs1 ref_Y₀_gt_one h_combo
      linarith
  · rw [hfd_re] at heq_re
    have h_rhs_nn : (1 - s) * p.re ≥ 0 := by positivity
    have h_lhs_le : -v / 2 ≤ 0 := by linarith
    have h_both_zero : (1 - s) * p.re = 0 ∧ v = 0 := by
      constructor <;> linarith
    have hs_eq : s = 1 := by
      rcases mul_eq_zero.mp h_both_zero.1 with h | h
      · linarith
      · exfalso; linarith
    rw [hs_eq] at heq_im; simp only [sub_self, zero_mul, zero_add, one_mul] at heq_im
    rw [hfd_im, show v = 0 from h_both_zero.2] at heq_im
    simp only [zero_mul, sub_zero] at heq_im
    linarith [ref_Y₀_gt_one]

/-- The straight line from any valid interior point p to refP₀ = I*Y₀
    avoids all points on the fdPolygon boundary. -/
lemma fdPolygon_avoids_line_to_ref (p : ℂ) (hp_norm : ‖p‖ > 1)
    (hp_re : |p.re| < 1 / 2) (hp_im_pos : 0 < p.im) (hp_im : p.im < HHeight) :
    ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 5,
      fdPolygon t ≠ (1 - (s : ℂ)) * p + (s : ℂ) * refP₀ := by
  have hsq3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hsq3_pos : 0 < Real.sqrt 3 := Real.sqrt_pos_of_pos (by norm_num : (0 : ℝ) < 3)
  have hsq3_lt2 : Real.sqrt 3 < 2 := by nlinarith [hsq3]
  have href_re : refP₀.re = 0 := by
    unfold refP₀
    simp only [mul_re, I_re, I_im, ofReal_re, ofReal_im, mul_zero, sub_zero, zero_mul]
  have href_im : refP₀.im = refY₀ := by
    unfold refP₀
    simp only [mul_im, I_re, I_im, ofReal_re, ofReal_im, mul_zero, zero_add, one_mul]
  have hp_sq : p.re ^ 2 + p.im ^ 2 > 1 := by
    rw [Complex.norm_eq_sqrt_sq_add_sq] at hp_norm
    nlinarith [Real.sq_sqrt (add_nonneg (sq_nonneg p.re) (sq_nonneg p.im)),
               sq_nonneg (Real.sqrt (p.re ^ 2 + p.im ^ 2) - 1)]
  intro s ⟨hs0, hs1⟩ t ⟨ht0, ht5⟩ heq
  have h1s_cast : (1 : ℂ) - (s : ℂ) = ((1 - s : ℝ) : ℂ) := by push_cast; ring
  have h1s_nn : 0 ≤ 1 - s := by linarith
  have heq_re : (fdPolygon t).re = (1 - s) * p.re := by
    have := congr_arg Complex.re heq
    simp only [add_re, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero, href_re,
      mul_zero, add_zero] at this
    rw [h1s_cast] at this
    simp only [ofReal_re, ofReal_im, zero_mul, sub_zero] at this
    linarith
  have heq_im : (fdPolygon t).im = (1 - s) * p.im + s * refY₀ := by
    have := congr_arg Complex.im heq
    simp only [add_im, mul_im, ofReal_re, ofReal_im, zero_mul,
      add_zero, href_im] at this
    rw [h1s_cast] at this
    simp only [ofReal_re, ofReal_im, zero_mul, add_zero] at this
    linarith
  by_cases ht1 : t ≤ 1
  · have hfd_re : (fdPolygon t).re = 1/2 := by
      simp only [fdPolygon, ht1, ↓reduceIte, add_re,
        div_ofNat_re, one_re, mul_re, I_re,
        mul_zero, I_im, mul_one]
      norm_num
    rw [hfd_re] at heq_re
    have h1 : |(1 - s) * p.re| ≤ |p.re| := by
      rw [abs_mul, abs_of_nonneg h1s_nn]
      exact mul_le_of_le_one_left (abs_nonneg _) (by linarith)
    have h2 : |(1 - s) * p.re| < 1/2 := lt_of_le_of_lt h1 hp_re
    have h3 : (1 - s) * p.re = 1/2 := by linarith
    have h4 : |(1 - s) * p.re| = 1/2 := by rw [h3]; norm_num
    linarith
  · push Not at ht1
    by_cases ht2 : t ≤ 2
    · exact (avoids_chord_rho'_to_i p hp_re hp_im_pos hp_sq s hs0 hs1 h1s_nn t
        ht1 ht2 heq_re heq_im).elim
    · push Not at ht2
      by_cases ht3 : t ≤ 3
      · exact (avoids_chord_i_to_rho p hp_re hp_im_pos hp_sq s hs0 hs1 h1s_nn t
          ht2 ht3 heq_re heq_im).elim
      · push Not at ht3
        by_cases ht4 : t ≤ 4
        · have hfd_re : (fdPolygon t).re = -1/2 := by
            simp only [fdPolygon, not_le.mpr ht1,
              not_le.mpr ht2, not_le.mpr ht3, ht4,
              ↓reduceIte, add_re, neg_re, one_re,
              div_ofNat_re, mul_re, ofReal_re,
              I_re, mul_zero, I_im, mul_one]
            norm_num
          rw [hfd_re] at heq_re
          have h1 : |(1 - s) * p.re| ≤ |p.re| := by
            rw [abs_mul, abs_of_nonneg h1s_nn]
            exact mul_le_of_le_one_left (abs_nonneg _) (by linarith)
          have h2 : |(1 - s) * p.re| < 1/2 := lt_of_le_of_lt h1 hp_re
          have h3 : (1 - s) * p.re = -1/2 := by linarith
          have h4 : |(1 - s) * p.re| = 1/2 := by rw [h3]; norm_num
          linarith
        · push Not at ht4
          have hfd_im : (fdPolygon t).im = HHeight := by
            simp only [fdPolygon, not_le.mpr ht1, not_le.mpr ht2, not_le.mpr ht3,
              not_le.mpr ht4, ↓reduceIte, add_im, ofReal_im, mul_im, ofReal_re,
              I_re, mul_zero, I_im, mul_one, add_zero, HHeight]
            norm_num
          rw [hfd_im] at heq_im
          rcases eq_or_lt_of_le hs0 with rfl | hs_pos
          · simp only [sub_zero, one_mul, zero_mul, add_zero] at heq_im; linarith
          rcases eq_or_lt_of_le hs1 with rfl | hs_lt1
          · simp only [sub_self, zero_mul, zero_add, one_mul] at heq_im; linarith [ref_Y₀_lt_H]
          · have : (1 - s) * p.im < (1 - s) * HHeight := by
              apply mul_lt_mul_of_pos_left hp_im; linarith
            have : s * refY₀ < s * HHeight := by
              apply mul_lt_mul_of_pos_left ref_Y₀_lt_H; linarith
            have : (1 - s) * p.im + s * refY₀ < (1 - s) * HHeight + s * HHeight := by linarith
            have : (1 - s) * HHeight + s * HHeight = HHeight := by ring
            linarith

/-- rc(t) - refP₀ lies in slitPlane for t ∈ [0, 5] with t ≠ tL refP₀.
Note: `CurveAvoidance.curve_sub_in_slitPlane` does not apply here because its `hpos`
hypothesis requires `0 < im ∨ 0 < re` uniformly on all of `Icc 0 5`, whereas at `tL`
the vector has `re < 0` and `im = 0` (a branch-cut crossing). slitPlane membership at
non-`tL` points relies on `im ≠ 0` (not `im > 0`), which is outside the API's scope. -/
lemma rc_sub_ref_p₀_mem_slitPlane (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 5)
    (htL : t ≠ tL refP₀) :
    fdPolygonRadialCircle refP₀ t - refP₀ ∈ Complex.slitPlane := by
  have hz_ne : fdPolygon t ≠ refP₀ :=
    fdPolygon_avoids_interior refP₀ ref_p₀_norm ref_p₀_re ref_p₀_im t ht
  set w := fdPolygon t - refP₀ with hw_def
  have hw_ne : w ≠ 0 := sub_ne_zero.mpr hz_ne
  have hnorm_pos : (0 : ℝ) < ‖w‖ := norm_pos_iff.mpr hw_ne
  have hgoal_eq : fdPolygonRadialCircle refP₀ t - refP₀ = w / ↑‖w‖ := by
    unfold fdPolygonRadialCircle polygonToCircleRadial
    simp only [← hw_def, sub_self, zero_mul, zero_add, add_sub_cancel_left, div_eq_mul_inv]
    exact one_smul ℝ _
  rw [hgoal_eq]
  suffices hw_slit : w ∈ Complex.slitPlane by
    simp only [Complex.slitPlane, Set.mem_setOf_eq] at hw_slit ⊢
    rw [Complex.div_ofReal_re, Complex.div_ofReal_im]
    rcases hw_slit with hre | him
    · left; exact div_pos hre hnorm_pos
    · right; exact div_ne_zero him (ne_of_gt hnorm_pos)
  simp only [Complex.slitPlane, Set.mem_setOf_eq]
  have ref_re : refP₀.re = 0 := by
    unfold refP₀
    simp only [mul_re, I_re, I_im, ofReal_re, ofReal_im, mul_zero, sub_zero, zero_mul]
  have ref_im : refP₀.im = refY₀ := by
    unfold refP₀
    simp only [mul_im, I_re, I_im, ofReal_re, ofReal_im, mul_zero, zero_add, one_mul]
  have hw_re : w.re = (fdPolygon t).re := by
    simp only [hw_def, Complex.sub_re, ref_re, sub_zero]
  have hw_im : w.im = (fdPolygon t).im - refY₀ := by
    simp only [hw_def, Complex.sub_im, ref_im]
  have ht0 : 0 ≤ t := ht.1
  have ht5 : t ≤ 5 := ht.2
  by_cases ht1 : t ≤ 1
  · left; rw [hw_re]
    simp only [fdPolygon, ht1, ↓reduceIte, add_re,
      mul_re, I_re, I_im, mul_zero, mul_one]
    norm_num
  · push Not at ht1
    by_cases ht2 : t ≤ 2
    · right; rw [hw_im]
      have hfd_eq : fdPolygon t = chordSegment rho' iPoint (t - 1) := by
        simp only [fdPolygon, show ¬(t ≤ 1) from not_le.mpr ht1, ht2, ↓reduceIte]
      have hfd_im_le : (fdPolygon t).im ≤ 1 := by
        rw [hfd_eq, chordSegment]
        have him : ((1 - (t - 1)) • rho' + (t - 1) • iPoint).im =
            (1 - (t - 1)) * rho'.im + (t - 1) * iPoint.im := by
          simp only [add_im, Complex.real_smul, mul_im, ofReal_re, ofReal_im,
            add_zero, zero_mul]
        rw [him]
        have hrho' : rho'.im = Real.sqrt 3 / 2 := by
          unfold rho'
          simp only [one_div, Complex.add_im, Complex.inv_im, Complex.im_ofNat, neg_zero,
            Complex.normSq_ofNat, zero_div, Complex.mul_im, Complex.div_ofNat_re,
            Complex.ofReal_re, Complex.I_im, mul_one, Complex.div_ofNat_im,
            Complex.ofReal_im, Complex.I_re, mul_zero, add_zero, zero_add]
        have hi : iPoint.im = 1 := by
          unfold iPoint; simp only [Complex.I_im]
        rw [hrho', hi]
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), sq_nonneg (2 - Real.sqrt 3)]
      intro h_eq; linarith [ref_Y₀_gt_one]
    · push Not at ht2
      by_cases ht3 : t ≤ 3
      · right; rw [hw_im]
        have hfd_eq : fdPolygon t = chordSegment iPoint rho (t - 2) := by
          simp only [fdPolygon, show ¬(t ≤ 1) from not_le.mpr ht1,
            show ¬(t ≤ 2) from not_le.mpr ht2, ht3, ↓reduceIte]
        have hfd_im_le : (fdPolygon t).im ≤ 1 := by
          rw [hfd_eq, chordSegment]
          have him : ((1 - (t - 2)) • iPoint + (t - 2) • rho).im =
              (1 - (t - 2)) * iPoint.im + (t - 2) * rho.im := by
            simp only [add_im, Complex.real_smul, mul_im, ofReal_re, ofReal_im,
              add_zero, zero_mul]
          rw [him]
          have hi : iPoint.im = 1 := by
            unfold iPoint; simp only [Complex.I_im]
          have hrho : rho.im = Real.sqrt 3 / 2 := by
            unfold rho
            simp only [add_im, div_ofNat_im, neg_im, one_im, neg_zero, zero_div, mul_im,
              div_ofNat_re, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero,
              zero_add]
          rw [hi, hrho]
          nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), sq_nonneg (2 - Real.sqrt 3)]
        intro h_eq; linarith [ref_Y₀_gt_one]
      · push Not at ht3
        by_cases ht4 : t ≤ 4
        · right; rw [hw_im]
          have hfd_im : (fdPolygon t).im =
              Real.sqrt 3 / 2 + (t - 3) * (HHeight - Real.sqrt 3 / 2) := by
            simp only [fdPolygon, not_le.mpr ht1, not_le.mpr ht2, not_le.mpr ht3, ht4, ↓reduceIte]
            have heq : (-1/2 + (↑(Real.sqrt 3) / 2 + (↑t - 3) *
                (↑HHeight - ↑(Real.sqrt 3) / 2)) * I) =
              ↑(-1/2 : ℝ) +
              ↑(Real.sqrt 3 / 2 + (t - 3) * (HHeight - Real.sqrt 3 / 2)) * I := by
              push_cast; ring
            rw [heq, add_im, ofReal_im, mul_im, ofReal_re, ofReal_im, I_re, I_im,
              mul_one, mul_zero, add_zero, zero_add]
          have hdenom_pos : HHeight - Real.sqrt 3 / 2 > 0 := by unfold HHeight; linarith
          intro h_eq
          have him_eq : (fdPolygon t).im = refY₀ := by linarith
          have him_eq' : (t - 3) * (HHeight - Real.sqrt 3 / 2) =
              refY₀ - Real.sqrt 3 / 2 := by linarith [hfd_im]
          have ht_eq : t - 3 = (refY₀ - Real.sqrt 3 / 2) / (HHeight - Real.sqrt 3 / 2) := by
            rw [eq_div_iff (ne_of_gt hdenom_pos)]; linarith
          have : t = tL refP₀ := by simp only [tL, ref_im]; linarith
          exact htL this
        · push Not at ht4
          right; rw [hw_im]
          have hfd_im : (fdPolygon t).im = HHeight := by
            simp only [fdPolygon, not_le.mpr ht1, not_le.mpr ht2, not_le.mpr ht3,
              not_le.mpr ht4, ↓reduceIte]
            have heq : ((↑t - 9/2) + ↑HHeight * I) = ↑(t - 9/2 : ℝ) + ↑HHeight * I := by
              push_cast; ring
            rw [heq, add_im, ofReal_im, mul_im, ofReal_re, ofReal_im, I_re, I_im,
              mul_one, mul_zero, add_zero, zero_add]
          linarith [ref_Y₀_lt_H]

/-- fdPolygon t - refP₀ is in slitPlane for t ∈ [0, 5] with t ≠ tL refP₀.
Derived from `rc_sub_ref_p₀_mem_slitPlane` via positive-scaling; the same
`curve_sub_in_slitPlane` incompatibility applies (see above). -/
lemma fdPolygon_sub_ref_p₀_mem_slitPlane (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 5)
    (htL : t ≠ tL refP₀) :
    fdPolygon t - refP₀ ∈ Complex.slitPlane := by
  have hw := rc_sub_ref_p₀_mem_slitPlane t ht htL
  set w := fdPolygon t - refP₀ with hw_def
  have hz_ne : fdPolygon t ≠ refP₀ :=
    fdPolygon_avoids_interior refP₀ ref_p₀_norm ref_p₀_re ref_p₀_im t ht
  have hw_ne : w ≠ 0 := sub_ne_zero.mpr hz_ne
  have hnorm_pos : (0 : ℝ) < ‖w‖ := norm_pos_iff.mpr hw_ne
  have hrc_eq : fdPolygonRadialCircle refP₀ t - refP₀ = w / ↑‖w‖ := by
    unfold fdPolygonRadialCircle polygonToCircleRadial
    simp only [← hw_def, sub_self, zero_mul, zero_add, add_sub_cancel_left, div_eq_mul_inv]
    exact one_smul ℝ _
  rw [hrc_eq] at hw
  simp only [Complex.slitPlane, Set.mem_setOf_eq] at hw ⊢
  rcases hw with hre | him
  · left
    rw [Complex.div_ofReal_re] at hre
    exact (div_pos_iff.mp hre).elim (fun h => h.1)
      (fun h => absurd h.2 (not_lt.mpr (le_of_lt hnorm_pos)))
  · right
    rw [Complex.div_ofReal_im] at him
    exact fun h => him (div_eq_zero_iff.mpr (Or.inl h))

/-- w = fdPolygon · - refP₀ is continuous. -/
lemma continuous_w : Continuous (fun t => fdPolygon t - refP₀) :=
  fdPolygon_continuous.sub continuous_const

/-- arg ∘ w is continuous on Icc 0 5 \ {tL refP₀}. -/
lemma continuousOn_arg_w :
    ContinuousOn (fun t => Complex.arg (fdPolygon t - refP₀))
      (Icc 0 5 \ {tL refP₀}) :=
  ContinuousOn.comp Complex.continuousOn_arg continuous_w.continuousOn
    (fun t ht => fdPolygon_sub_ref_p₀_mem_slitPlane t ht.1 (Set.notMem_singleton_iff.mp ht.2))

/-- At tL: w has re < 0 and im = 0. -/
lemma w_tL_re_neg : (fdPolygon (tL refP₀) - refP₀).re < 0 :=
  (seg4_vec_at_tL refP₀ ref_p₀_norm ref_p₀_re ref_p₀_im_pos ref_p₀_im).1

lemma w_tL_im_zero : (fdPolygon (tL refP₀) - refP₀).im = 0 :=
  (seg4_vec_at_tL refP₀ ref_p₀_norm ref_p₀_re ref_p₀_im_pos ref_p₀_im).2

/-- For t near tL from below, w(t).im < 0. -/
lemma w_im_neg_near_tL_left :
    ∀ᶠ t in 𝓝[Iio (tL refP₀)] (tL refP₀), (fdPolygon t - refP₀).im < 0 := by
  have htL := tL_mem_Ioo refP₀ ref_p₀_norm ref_p₀_re ref_p₀_im_pos ref_p₀_im
  exact Filter.mem_of_superset (Ioo_mem_nhdsLT htL.1) fun t ht =>
    (seg4_vec_im_sign refP₀ ref_p₀_norm ref_p₀_re ref_p₀_im_pos ref_p₀_im t
      ⟨ht.1, by linarith [ht.2, htL.2]⟩).1 ht.2

/-- For t near tL from above, w(t).im > 0. -/
lemma w_im_pos_near_tL_right :
    ∀ᶠ t in 𝓝[Ioi (tL refP₀)] (tL refP₀),
      0 < (fdPolygon t - refP₀).im := by
  have htL := tL_mem_Ioo refP₀ ref_p₀_norm ref_p₀_re ref_p₀_im_pos ref_p₀_im
  apply Filter.mem_of_superset (Ioo_mem_nhdsGT htL.2)
  intro t ht
  have ht_Ioc : t ∈ Set.Ioc (3 : ℝ) 4 := ⟨by linarith [ht.1, htL.1], by linarith [ht.2]⟩
  exact (seg4_vec_im_sign refP₀ ref_p₀_norm ref_p₀_re ref_p₀_im_pos ref_p₀_im
    t ht_Ioc).2.2 ht.1

/-- Tendsto arg(w(t)) from the left of tL to -π. -/
lemma tendsto_arg_w_left :
    Tendsto (fun t => Complex.arg (fdPolygon t - refP₀))
      (𝓝[Iio (tL refP₀)] (tL refP₀)) (𝓝 (-Real.pi)) := by
  exact (Complex.tendsto_arg_nhdsWithin_im_neg_of_re_neg_of_im_zero
    w_tL_re_neg w_tL_im_zero).comp (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      continuous_w.continuousAt.continuousWithinAt w_im_neg_near_tL_left)

/-- Tendsto arg(w(t)) from the right of tL to π. -/
lemma tendsto_arg_w_right :
    Tendsto (fun t => Complex.arg (fdPolygon t - refP₀))
      (𝓝[Ioi (tL refP₀)] (tL refP₀)) (𝓝 Real.pi) := by
  exact (Complex.tendsto_arg_nhdsWithin_im_nonneg_of_re_neg_of_im_zero
    w_tL_re_neg w_tL_im_zero).comp (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      continuous_w.continuousAt.continuousWithinAt
      (w_im_pos_near_tL_right.mono (fun t ht => le_of_lt ht)))

end RectHomotopyProof
