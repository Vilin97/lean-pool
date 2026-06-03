/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import LeanPool.LeanModularForms.ValenceFormula.RectHomotopy.BoundaryHomotopyDerivBounds
import LeanPool.LeanModularForms.ValenceFormula.RectHomotopy.BoundaryHomotopyDiff
import LeanPool.LeanModularForms.ValenceFormula.RectHomotopy.BoundaryHomotopySmooth

/-!
# Uniform derivative bound for the homotopy

Proves a uniform bound `‖deriv_t H(t,s)‖ ≤ 5` for all `(t,s) ∈ [0,5] × [0,1]`,
handling each segment case and the non-differentiable fallback.
-/

open Complex Set Metric Filter Topology

namespace RectHomotopyProof

/-- Derivative of an affine-angle complex exponential `t' ↦ exp((α + (t' - c)·β)·I)`. -/
private lemma mtb_hasDerivAt_arc_exp (α β c t : ℝ) :
    HasDerivAt (fun t' : ℝ => Complex.exp (((α : ℂ) + ((t' : ℂ) - c) * (β : ℂ)) * I))
      ((β : ℂ) * I * Complex.exp (((α : ℂ) + ((t : ℂ) - c) * (β : ℂ)) * I)) t := by
  have h_shift : HasDerivAt (fun t' : ℝ => (t' : ℂ) - c) 1 t :=
    Complex.ofRealCLM.hasDerivAt.sub_const (c : ℂ)
  have h_inner : HasDerivAt (fun t' : ℝ => (α : ℂ) + ((t' : ℂ) - c) * (β : ℂ)) (β : ℂ) t := by
    have h_mul := h_shift.mul_const (β : ℂ)
    simp only [one_mul] at h_mul
    exact h_mul.const_add (α : ℂ)
  have h := (Complex.hasDerivAt_exp (((α : ℂ) + ((t : ℂ) - c) * (β : ℂ)) * I)).comp t
    (h_inner.mul_const I)
  simp only [mul_comm (Complex.exp _)] at h
  exact h

/-- Derivative of the chord segment `t' ↦ chordSegment a b (t' - c)` is `b - a`. -/
private lemma mtb_hasDerivAt_chordSegment_shift (a b : ℂ) (c t : ℝ) :
    HasDerivAt (fun t' : ℝ => chordSegment a b (t' - c)) (b - a) t := by
  simp only [chordSegment]
  have h_shift : HasDerivAt (fun t' : ℝ => t' - c) (1 : ℝ) t := (hasDerivAt_id t).sub_const c
  have h1 : HasDerivAt (fun t' : ℝ => (1 - (t' - c)) • a) (-a) t := by
    have h_coef : HasDerivAt (fun t' : ℝ => (1 - (t' - c) : ℝ)) (-1 : ℝ) t := by
      have := (hasDerivAt_const t (1 : ℝ)).sub h_shift
      simp only [zero_sub] at this
      exact this
    have := h_coef.smul_const a
    simpa only [neg_one_smul] using this
  have h2 : HasDerivAt (fun t' : ℝ => (t' - c) • b) b t := by
    have := h_shift.smul_const b
    simpa only [one_smul] using this
  convert h1.add h2 using 1
  ring

/-- The homotopy is not differentiable at `t = 2` when `s ≠ 0`: the left limit of the slope
involves the arc-vs-chord increment `iPoint - rho'`, the right limit `rho - iPoint`, and these
disagree (their imaginary parts would force `√3 = 2`). -/
private lemma not_diffAt_at_two (s : ℝ) (hs0 : s ≠ 0) :
    ¬DifferentiableAt ℝ (fun t' ↦ fdBoundaryToPolygonHomotopy (t', s)) 2 := by
  intro hd_inner
  have h_slope_inner := hasDerivAt_iff_tendsto_slope.mp hd_inner.hasDerivAt
  let g_left : ℝ → ℂ := fun t' => (1 - s) •
      Complex.exp (((Real.pi : ℝ) / 3 + (t' - 1) * ((Real.pi : ℝ) / 6)) * I) +
    s • chordSegment rho' iPoint (t' - 1)
  have h_arc_left :
      HasDerivAt (fun t' : ℝ =>
          Complex.exp (((Real.pi : ℝ) / 3 + (t' - 1) * ((Real.pi : ℝ) / 6)) * I))
        (((Real.pi : ℝ) / 6) * I * I) (2 : ℝ) := by
    have h_raw := mtb_hasDerivAt_arc_exp (Real.pi / 3) (Real.pi / 6) 1 2
    have h_val : Complex.exp (((↑(Real.pi / 3) : ℂ) +
        ((↑(2 : ℝ) : ℂ) - ↑(1 : ℝ)) * (↑(Real.pi / 6) : ℂ)) * I) = I := by
      rw [show ((↑(Real.pi / 3) : ℂ) + ((↑(2 : ℝ) : ℂ) - ↑(1 : ℝ)) * (↑(Real.pi / 6) : ℂ)) =
          ↑(Real.pi / 2) from by push_cast; ring]
      exact exp_pi_div_two_eq_I
    rw [h_val] at h_raw
    convert h_raw using 2 <;> push_cast <;> ring
  have h_chord_left :
      HasDerivAt (fun t' : ℝ => chordSegment rho' iPoint (t' - 1)) (iPoint - rho') (2 : ℝ) :=
    mtb_hasDerivAt_chordSegment_shift rho' iPoint 1 2
  have h_combined_left :
      HasDerivAt g_left ((1 - s) • (((Real.pi : ℝ) / 6) * I * I) + s • (iPoint - rho')) (2 : ℝ) :=
    (h_arc_left.const_smul (1 - s)).add (h_chord_left.const_smul s)
  have h_slope_left_iio := (hasDerivAt_iff_tendsto_slope.mp h_combined_left).mono_left
    (nhdsWithin_mono (2 : ℝ) (fun y (hy : y < _) => ne_of_lt hy))
  have h_mem_left : Ioo 1 2 ∈ 𝓝[<] (2 : ℝ) := Ioo_mem_nhdsLT (by norm_num : (1 : ℝ) < 2)
  have h_left_val :
      Tendsto (slope (fun t' => fdBoundaryToPolygonHomotopy (t', s)) 2)
        (𝓝[<] 2) (𝓝 ((1 - s) • (((Real.pi : ℝ) / 6) * I * I) + s • (iPoint - rho'))) := by
    refine h_slope_left_iio.congr' ?_
    filter_upwards [h_mem_left] with t' ht'
    simp only [slope_def_module]
    congr 1
    have h_at_2 : fdBoundaryToPolygonHomotopy (2, s) = g_left 2 := by
      simp only [fdBoundaryToPolygonHomotopy, show (2 : ℝ) ≤ 2 from le_refl 2,
        show ¬(2 : ℝ) ≤ 1 from by norm_num, ite_false, ite_true]
      congr 1; congr 1; congr 1; ring
    have h_at_t' : fdBoundaryToPolygonHomotopy (t', s) = g_left t' := by
      simp only [fdBoundaryToPolygonHomotopy, not_le.mpr ht'.1, ite_false, le_of_lt ht'.2, ite_true]
      congr 1; congr 1; congr 1; ring
    rw [h_at_t', h_at_2]
  let g_right : ℝ → ℂ := fun t' => (1 - s) •
      Complex.exp (((Real.pi : ℝ) / 2 + (t' - 2) * ((Real.pi : ℝ) / 6)) * I) +
    s • chordSegment iPoint rho (t' - 2)
  have h_arc_right :
      HasDerivAt (fun t' : ℝ =>
          Complex.exp (((Real.pi : ℝ) / 2 + (t' - 2) * ((Real.pi : ℝ) / 6)) * I))
        (((Real.pi : ℝ) / 6) * I * I) (2 : ℝ) := by
    have h_raw := mtb_hasDerivAt_arc_exp (Real.pi / 2) (Real.pi / 6) 2 2
    have h_val : Complex.exp (((↑(Real.pi / 2) : ℂ) +
        ((↑(2 : ℝ) : ℂ) - ↑(2 : ℝ)) * (↑(Real.pi / 6) : ℂ)) * I) = I := by
      rw [show ((↑(Real.pi / 2) : ℂ) + ((↑(2 : ℝ) : ℂ) - ↑(2 : ℝ)) * (↑(Real.pi / 6) : ℂ)) =
          ↑(Real.pi / 2) from by push_cast; ring]
      exact exp_pi_div_two_eq_I
    rw [h_val] at h_raw
    convert h_raw using 2 <;> push_cast <;> ring
  have h_chord_right :
      HasDerivAt (fun t' : ℝ => chordSegment iPoint rho (t' - 2)) (rho - iPoint) (2 : ℝ) :=
    mtb_hasDerivAt_chordSegment_shift iPoint rho 2 2
  have h_combined_right :
      HasDerivAt g_right ((1 - s) • (((Real.pi : ℝ) / 6) * I * I) + s • (rho - iPoint)) (2 : ℝ) :=
    (h_arc_right.const_smul (1 - s)).add (h_chord_right.const_smul s)
  have h_slope_right_ioi := (hasDerivAt_iff_tendsto_slope.mp h_combined_right).mono_left
    (nhdsWithin_mono (2 : ℝ) (fun y (hy : _ < y) => ne_of_gt hy))
  have h_mem_right : Ioo 2 3 ∈ 𝓝[>] (2 : ℝ) := Ioo_mem_nhdsGT (by norm_num : (2 : ℝ) < 3)
  have h_right_val :
      Tendsto (slope (fun t' => fdBoundaryToPolygonHomotopy (t', s)) 2)
        (𝓝[>] 2) (𝓝 ((1 - s) • (((Real.pi : ℝ) / 6) * I * I) + s • (rho - iPoint))) := by
    refine h_slope_right_ioi.congr' ?_
    filter_upwards [h_mem_right] with t' ht'
    simp only [slope_def_module]
    congr 1
    have h_at_2r : fdBoundaryToPolygonHomotopy (2, s) = g_right 2 := by
      simp only [fdBoundaryToPolygonHomotopy, show (2 : ℝ) ≤ 2 from le_refl 2,
        show ¬(2 : ℝ) ≤ 1 from by norm_num, ite_false, ite_true, chordSegment]
      congr 1
      · congr 1; push_cast; ring_nf
      · rw [show (2 : ℝ) - 1 = 1 from by norm_num, show (2 : ℝ) - 2 = 0 from by norm_num]
        simp [chordSegment]
    have h_at_t'r : fdBoundaryToPolygonHomotopy (t', s) = g_right t' := by
      simp only [fdBoundaryToPolygonHomotopy,
        not_le.mpr (show (1 : ℝ) < t' by linarith [ht'.1]), not_le.mpr ht'.1, ite_false,
        le_of_lt ht'.2, ite_true]
      congr 1; congr 1; congr 1; ring
    rw [h_at_t'r, h_at_2r]
  have h_eq_left := tendsto_nhds_unique (h_slope_inner.mono_left (nhdsLT_le_nhdsNE 2)) h_left_val
  have h_eq_right := tendsto_nhds_unique (h_slope_inner.mono_left (nhdsGT_le_nhdsNE 2)) h_right_val
  rw [h_eq_left] at h_eq_right
  have h_pts_eq : iPoint - rho' = rho - iPoint := by
    have h_smul_eq : s • (iPoint - rho') = s • (rho - iPoint) := add_left_cancel h_eq_right
    exact (smul_right_injective ℂ hs0).eq_iff.mp h_smul_eq
  have h_im_left : Complex.im (iPoint - rho') = 1 - Real.sqrt 3 / 2 := by
    simp only [iPoint, rho']
    simp [Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re,
      Complex.I_im, Complex.I_re, Complex.div_ofNat_im, Complex.div_ofNat_re]
  have h_im_right : Complex.im (rho - iPoint) = Real.sqrt 3 / 2 - 1 := by
    simp only [rho, iPoint]
    simp [Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re,
      Complex.I_im, Complex.I_re, Complex.neg_im, Complex.div_ofNat_im, Complex.div_ofNat_re,
      Complex.one_im]
  have h_im_eq := congr_arg Complex.im h_pts_eq
  rw [h_im_left, h_im_right] at h_im_eq
  have h_sqrt3_eq : Real.sqrt 3 = 2 := by linarith
  have h_sq : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num : (3 : ℝ) ≥ 0)
  rw [h_sqrt3_eq] at h_sq
  norm_num at h_sq

/-- The derivative-norm bound at the corner `t = 2`, `s = 0` (the homotopy is smooth there). -/
private lemma deriv_bound_at_two_zero :
    ‖deriv (fun t' => fdBoundaryToPolygonHomotopy (t', 0)) 2‖ ≤ 5 := by
  have heq : (fun t' => fdBoundaryToPolygonHomotopy (t', 0)) =ᶠ[𝓝 2]
      (fun t' : ℝ => Complex.exp ((Real.pi / 3 + (t' - 1) * (Real.pi / 6)) * I)) := by
    filter_upwards [eventually_gt_nhds (by norm_num : (1 : ℝ) < 2),
      eventually_lt_nhds (by norm_num : (2 : ℝ) < 3)] with t' ht1' ht2'
    simp only [fdBoundaryToPolygonHomotopy]
    by_cases ht'_le2 : t' ≤ 2
    · simp only [not_le.mpr ht1', ht'_le2, ite_false, ite_true, sub_zero]
      erw [one_smul, zero_smul, add_zero]; congr 1; ring
    · simp only [not_le.mpr ht1', not_le.mpr (lt_of_not_ge ht'_le2), le_of_lt ht2', ite_false,
        ite_true, sub_zero]
      erw [one_smul, zero_smul, add_zero]; congr 1; ring
  rw [heq.deriv_eq]
  have h_deriv : HasDerivAt (fun t' : ℝ =>
      Complex.exp ((Real.pi / 3 + (t' - 1) * (Real.pi / 6)) * I))
      ((Real.pi / 6) * I * Complex.exp ((Real.pi / 2) * I)) 2 := by
    have h_raw := mtb_hasDerivAt_arc_exp (Real.pi / 3) (Real.pi / 6) 1 2
    rw [show ((↑(Real.pi / 3) : ℂ) + ((↑(2 : ℝ) : ℂ) - ↑(1 : ℝ)) * (↑(Real.pi / 6) : ℂ)) * I =
        ((Real.pi : ℝ) / 2 : ℂ) * I from by push_cast; ring] at h_raw
    convert h_raw using 2 <;> push_cast <;> ring
  rw [h_deriv.deriv]
  have h_exp_norm : ‖Complex.exp ((Real.pi / 2) * I)‖ = 1 := by
    rw [show ((Real.pi / 2) * I : ℂ) = ((Real.pi / 2 : ℝ) : ℂ) * I from by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I]
  rw [norm_mul, norm_mul, h_exp_norm, Complex.norm_I, mul_one, mul_one,
    show (Real.pi / 6 : ℂ) = ((Real.pi / 6 : ℝ) : ℂ) from by push_cast; ring, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < Real.pi / 6)]
  have := Real.pi_le_four; linarith

lemma fdBoundaryToPolygonHomotopy_deriv_bound :
    ∃ M : ℝ, ∀ t ∈ Icc 0 5,
      ∀ s ∈ Icc (0 : ℝ) 1,
        ‖deriv (fun t' =>
          fdBoundaryToPolygonHomotopy (t', s)) t‖ ≤ M := by
  use 5
  intro t ht s hs
  by_cases hd :
      DifferentiableAt ℝ (fun t' =>
          fdBoundaryToPolygonHomotopy (t', s))
        t
  · by_cases h1 : t < 1
    · have heq : (fun t' =>
            fdBoundaryToPolygonHomotopy (t', s)) =ᶠ[𝓝 t]
          (fun t' : ℝ => (1/2 : ℂ) +
              (HHeight - (↑t' : ℂ) * (HHeight -
                  Real.sqrt 3 / 2)) * I) := by
        filter_upwards [
          eventually_lt_nhds h1] with t' ht'
        simp only [fdBoundaryToPolygonHomotopy,
          le_of_lt ht', ite_true]
      rw [heq.deriv_eq]
      exact norm_deriv_H_seg1_le t s
    · by_cases h2 : t < 2
      · by_cases h1' : t = 1
        · exfalso
          subst h1'
          exact
            fdBoundaryToPolygonHomotopy_not_diffAt_134
              s hs 1 (Set.mem_insert 1 _) hd
        · have ht2' : t ∈ Ioo 1 2 :=
            ⟨lt_of_le_of_ne (not_lt.mp h1) (Ne.symm h1'), h2⟩
          have heq : (fun t' =>
                fdBoundaryToPolygonHomotopy (t', s)) =ᶠ[𝓝 t]
              (fun t' : ℝ =>
                let arc_point :=
                  Complex.exp ((Real.pi / 3 +
                      (t' - 1) * (Real.pi / 2 -
                          Real.pi / 3)) *
                      I)
                let chord_point :=
                  chordSegment rho' iPoint (t' - 1)
                (1 - s) • arc_point +
                  s • chord_point) := by
            filter_upwards [
              eventually_gt_nhds ht2'.1,
              eventually_lt_nhds ht2'.2]
              with t' ht1' ht2''
            simp only
              [fdBoundaryToPolygonHomotopy]
            simp only [not_le.mpr ht1',
              ite_false, le_of_lt ht2'',
              ite_true]
          rw [heq.deriv_eq]
          exact
            fdBoundaryToPolygonHomotopy_seg2_deriv_bound
              t ht2' s hs
      · by_cases h3 : t < 3
        · have ht2_ge : t ≥ 2 := not_lt.mp h2
          by_cases h2' : t = 2
          · subst h2'
            by_cases hs0 : s = 0
            · subst hs0; exact deriv_bound_at_two_zero
            · exact absurd hd (not_diffAt_at_two s hs0)
          · have ht3' : t ∈ Ioo 2 3 :=
              ⟨lt_of_le_of_ne ht2_ge (Ne.symm h2'), h3⟩
            have heq : (fun t' =>
                  fdBoundaryToPolygonHomotopy (t', s)) =ᶠ[𝓝 t]
                (fun t' : ℝ =>
                  let arc_point :=
                    Complex.exp ((Real.pi / 2 +
                        (t' - 2) * (2 * Real.pi / 3 -
                            Real.pi / 2)) *
                        I)
                  let chord_point :=
                    chordSegment iPoint rho (t' - 2)
                  (1 - s) • arc_point +
                    s • chord_point) := by
              filter_upwards [
                eventually_gt_nhds ht3'.1,
                eventually_lt_nhds ht3'.2]
                with t' ht2'' ht3''
              simp only
                [fdBoundaryToPolygonHomotopy]
              simp only [
                not_le.mpr (lt_trans (by norm_num : (1 : ℝ) < 2)
                  ht2''),
                ite_false,
                not_le.mpr ht2'',
                le_of_lt ht3'', ite_true]
            rw [heq.deriv_eq]
            exact
              fdBoundaryToPolygonHomotopy_seg3_deriv_bound
                t ht3' s hs
        · by_cases h4 : t < 4
          · by_cases h3' : t = 3
            · exfalso
              subst h3'
              exact
                fdBoundaryToPolygonHomotopy_not_diffAt_134
                  s hs 3 (Set.mem_insert_of_mem 1 (Set.mem_insert 3 _)) hd
            · have ht4' : t ∈ Ioo 3 4 :=
                ⟨lt_of_le_of_ne (not_lt.mp h3)
                  (Ne.symm h3'), h4⟩
              have heq : (fun t' =>
                    fdBoundaryToPolygonHomotopy (t', s)) =ᶠ[𝓝 t]
                  (fun t' : ℝ => (-1/2 : ℂ) +
                      ((Real.sqrt 3 / 2 : ℂ) + ((↑t' : ℂ) - 3) *
                          ((HHeight : ℂ) -
                            Real.sqrt 3 / 2)) *
                        I) := by
                filter_upwards [
                  eventually_gt_nhds ht4'.1,
                  eventually_lt_nhds ht4'.2]
                  with t' ht3' ht4''
                simp only
                  [fdBoundaryToPolygonHomotopy]
                have h1' : ¬(t' ≤ 1) :=
                  not_le.mpr (by linarith : 1 < t')
                have h2' : ¬(t' ≤ 2) :=
                  not_le.mpr (by linarith : 2 < t')
                have h3'' : ¬(t' ≤ 3) :=
                  not_le.mpr ht3'
                have h4''' : t' ≤ 4 :=
                  le_of_lt ht4''
                simp only [h1', h2', h3'',
                  h4''', ite_false, ite_true]
              rw [heq.deriv_eq]
              exact norm_deriv_H_seg4_le t s
          · by_cases h4' : t = 4
            · exfalso
              subst h4'
              exact
                fdBoundaryToPolygonHomotopy_not_diffAt_134
                  s hs 4 (Set.mem_insert_of_mem 1 (Set.mem_insert_of_mem 3
                    (Set.mem_singleton_iff.mpr rfl))) hd
            · have ht5' : t > 4 :=
                lt_of_le_of_ne (not_lt.mp h4)
                  (Ne.symm h4')
              have heq : (fun t' =>
                    fdBoundaryToPolygonHomotopy (t', s)) =ᶠ[𝓝 t]
                  (fun t' : ℝ => ((↑t' : ℂ) - 9/2) +
                      (HHeight : ℂ) * I) := by
                filter_upwards [
                  eventually_gt_nhds ht5']
                  with t' ht4'
                simp only
                  [fdBoundaryToPolygonHomotopy]
                have h1' : ¬(t' ≤ 1) :=
                  not_le.mpr (by linarith : 1 < t')
                have h2' : ¬(t' ≤ 2) :=
                  not_le.mpr (by linarith : 2 < t')
                have h3' : ¬(t' ≤ 3) :=
                  not_le.mpr (by linarith : 3 < t')
                have h4'' : ¬(t' ≤ 4) :=
                  not_le.mpr ht4'
                simp only [h1', h2', h3',
                  h4'', ite_false]
              rw [heq.deriv_eq]
              exact norm_deriv_H_seg5_le t s
  · simp only [
      deriv_zero_of_not_differentiableAt hd,
      norm_zero]
    norm_num

end RectHomotopyProof
