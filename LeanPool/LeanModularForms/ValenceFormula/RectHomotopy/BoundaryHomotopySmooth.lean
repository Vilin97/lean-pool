/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import LeanPool.LeanModularForms.ValenceFormula.RectHomotopy.HomotopyDef

/-!
# Non-differentiability at partition points and derivative continuity

Proves the homotopy is not differentiable at t ∈ {1, 3, 4} (left/right derivatives
differ) and that the per-segment derivatives are continuous.
-/

open Complex Set Metric Filter Topology

namespace RectHomotopyProof

/-- Derivative of a straight segment `t' ↦ c₀ + (c₁ + (t' - c)·d)·I` is `d·I`. -/
private lemma hasDerivAt_straight_seg (c₀ c₁ d : ℂ) (c t : ℝ) :
    HasDerivAt (fun t' : ℝ => c₀ + (c₁ + ((t' : ℂ) - c) * d) * I) (d * I) t := by
  have h2 : HasDerivAt (fun t' : ℝ => (t' : ℂ) - c) 1 t :=
    Complex.ofRealCLM.hasDerivAt.sub_const (c : ℂ)
  have h3 : HasDerivAt (fun t' : ℝ => ((t' : ℂ) - c) * d) d t := by
    have := h2.mul_const d; simpa only [one_mul] using this
  have h4 : HasDerivAt (fun t' : ℝ => c₁ + ((t' : ℂ) - c) * d) d t := by
    have := (hasDerivAt_const t c₁).add h3; simp only [zero_add] at this; exact this
  have h5 : HasDerivAt (fun t' : ℝ => (c₁ + ((t' : ℂ) - c) * d) * I) (d * I) t := h4.mul_const I
  have := (hasDerivAt_const t c₀).add h5; simp only [zero_add] at this; exact this

/-- The shared real-part inequality at the arc/chord endpoints:
strictly negative for `s ∈ [0,1]`. -/
private lemma arc_chord_re_neg (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    (1 - s) * (-Real.pi * Real.sqrt 3 / 12) + s * (-1/2) < 0 := by
  have hpi : Real.pi > 0 := Real.pi_pos
  have hsqrt3_pos : Real.sqrt 3 > 0 := Real.sqrt_pos.mpr (by norm_num : (3 : ℝ) > 0)
  by_cases hs0 : s = 0
  · subst hs0
    simp only [sub_zero, one_mul, zero_mul, add_zero]
    nlinarith [hpi, hsqrt3_pos]
  · have hs_pos : s > 0 := lt_of_le_of_ne hs.1 (Ne.symm hs0)
    nlinarith [hs.1, hs.2, hs_pos, mul_pos hpi hsqrt3_pos]

/-- The homotopy is not differentiable at `t = 1` (left/right derivatives differ). -/
private lemma not_diffAt_at_one (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    ¬DifferentiableAt ℝ (fun t' => fdBoundaryToPolygonHomotopy (t', s)) 1 := by
    intro hd
    have h_slope := hasDerivAt_iff_tendsto_slope.mp hd.hasDerivAt
    have h_left_val : Tendsto (slope (fun t' => fdBoundaryToPolygonHomotopy (t', s)) 1) (𝓝[<] 1)
        (𝓝 (-(HHeight - Real.sqrt 3 / 2) * I)) := by
      have h_mem : Ioo 0 1 ∈ 𝓝[<] (1 : ℝ) := Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)
      apply Tendsto.congr' (f₁ := fun _ => -(HHeight - Real.sqrt 3 / 2) * I)
      · filter_upwards [h_mem] with t ht
        have ht1 : t ≤ 1 := le_of_lt ht.2
        have h1_1 : (1 : ℝ) ≤ 1 := le_refl 1
        simp only [slope_def_module, fdBoundaryToPolygonHomotopy, ht1, h1_1, ite_true]
        erw [Complex.real_smul]
        have hne : (↑t : ℂ) - 1 ≠ 0 := by
          simp only [sub_ne_zero]; norm_cast
          exact ne_of_lt ht.2
        simp only [Complex.ofReal_inv, Complex.ofReal_sub]
        field_simp [hne]
        simp only [HHeight]; push_cast; ring
      · exact tendsto_const_nhds
    have h_right_val : Tendsto (slope (fun t' => fdBoundaryToPolygonHomotopy (t', s)) 1) (𝓝[>] 1)
        (𝓝 ((1 - s) * (-Real.pi * Real.sqrt 3 / 12 + Real.pi / 12 * I) +
            s * (-1/2 + (1 - Real.sqrt 3 / 2) * I))) := by
      have h_mem : Ioo 1 2 ∈ 𝓝[>] (1 : ℝ) := Ioo_mem_nhdsGT (by norm_num : (1 : ℝ) < 2)
      let g : ℝ → ℂ := fun t' => (1 - s) • Complex.exp
          (((Real.pi : ℝ) / 3 + (t' - 1) *
              ((Real.pi : ℝ) / 6)) * I) +
        s • chordSegment rho' iPoint (t' - 1)
      have h_arc : HasDerivAt (fun t' : ℝ =>
            Complex.exp (((Real.pi : ℝ) / 3 +
                (t' - 1) * ((Real.pi : ℝ) / 6)) * I))
          (((Real.pi : ℝ) / 6) * I * rho') (1 : ℝ) := by
        have h_raw := hasDerivAt_arc_exp (Real.pi / 3) (Real.pi / 6) 1 1
        have h_val : Complex.exp (((↑(Real.pi / 3) : ℂ) +
            ((↑(1 : ℝ) : ℂ) - ↑(1 : ℝ)) * (↑(Real.pi / 6) : ℂ)) * I) = rho' := by
          rw [show ((↑(1 : ℝ) : ℂ) - ↑(1 : ℝ)) = 0 from by norm_num, zero_mul, add_zero,
            exp_pi_div_three_eq_rho']
        rw [h_val] at h_raw
        convert h_raw using 2 <;> push_cast <;> ring
      have h_chord : HasDerivAt (fun t' : ℝ => chordSegment rho' iPoint (t' - 1))
          (iPoint - rho') (1 : ℝ) :=
        hasDerivAt_chordSegment_shift rho' iPoint 1 1
      have h_combined : HasDerivAt g
          ((1 - s) • (((Real.pi : ℝ) / 6) * I * rho') + s • (iPoint - rho')) (1 : ℝ) := by
        have h1 := h_arc.const_smul (1 - s)
        have h2 := h_chord.const_smul s
        exact h1.add h2
      have h_deriv_eq : (1 - s) • (((Real.pi : ℝ) / 6) * I * rho') + s • (iPoint - rho') =
          (1 - ↑s) * (-↑Real.pi * ↑(Real.sqrt 3) / 12 + ↑Real.pi / 12 * I) +
          ↑s * (-1 / 2 + (1 - ↑(Real.sqrt 3) / 2) * I) := by
        have h1 : ((Real.pi : ℝ) / 6 : ℂ) * I * rho' =
            -↑Real.pi * ↑(Real.sqrt 3) / 12 + ↑Real.pi / 12 * I := by
          simp only [rho']; apply Complex.ext <;> simp <;> ring
        have h2 : iPoint - rho' = (-1/2 : ℂ) + (1 - ↑(Real.sqrt 3) / 2) * I := by
          simp only [iPoint, rho']; apply Complex.ext <;> (simp; try norm_num)
        rw [h1, h2]
        simp only [Complex.real_smul]; push_cast; ring
      rw [h_deriv_eq] at h_combined
      refine (hasDerivAt_iff_tendsto_slope.mp h_combined
        |>.mono_left (nhdsWithin_mono (1 : ℝ) (fun y hy => ne_of_gt hy))).congr' ?_
      filter_upwards [h_mem] with t' ht'
      simp only [slope_def_module]
      congr 1
      have h_at_1 : fdBoundaryToPolygonHomotopy (1, s) = g 1 := by
        have h_lhs : fdBoundaryToPolygonHomotopy (1, s) = rho' := by
          simp only [fdBoundaryToPolygonHomotopy, show (1 : ℝ) ≤ 1 from le_refl 1, ite_true]
          simp only [rho', HHeight]; push_cast; ring
        have h_rhs : g 1 = rho' := by
          have h_exp :
              Complex.exp (((Real.pi : ℝ) / 3 +
                  ((1 : ℝ) - 1) * ((Real.pi : ℝ) / 6)) * I) =
                rho' := by
            conv_lhs =>
              rw [show (↑(Real.pi : ℝ) / 3 + (↑(1 : ℝ) - 1) *
                      (↑(Real.pi : ℝ) / 6) : ℂ) =
                  ↑(Real.pi / 3)
                from by push_cast; ring]
            exact exp_pi_div_three_eq_rho'
          have h_chord : chordSegment rho' iPoint ((1 : ℝ) - 1) = rho' := by
            simp only [chordSegment, show ((1 : ℝ) - 1) = (0 : ℝ) from by ring]
            simp [sub_zero]
          calc g 1 = (1 - s) •
                Complex.exp (((Real.pi : ℝ) / 3 +
                    ((1 : ℝ) - 1) * ((Real.pi : ℝ) / 6)) * I) +
                s • chordSegment rho' iPoint ((1 : ℝ) - 1) := rfl
            _ = (1 - s) • rho' + s • rho' := by rw [h_exp, h_chord]
            _ = rho' := by simp only [Complex.real_smul]; push_cast; ring
        rw [h_lhs, h_rhs]
      have h_at_t' : fdBoundaryToPolygonHomotopy (t', s) = g t' := by
        have ht'_not_le_1 : ¬(t' ≤ 1) := not_le.mpr ht'.1
        have ht'_le_2 : t' ≤ 2 := le_of_lt ht'.2
        unfold fdBoundaryToPolygonHomotopy
        simp only [ht'_not_le_1, ite_false, ht'_le_2, ite_true]
        congr 4; ring
      rw [h_at_t', h_at_1]
    have h_iio_subset : Set.Iio (1 : ℝ) ⊆ {1}ᶜ := fun y hy => ne_of_lt hy
    have h_ioi_subset : Set.Ioi (1 : ℝ) ⊆ {1}ᶜ := fun y hy => ne_of_gt hy
    have h_left_slope := h_slope.mono_left (nhdsWithin_mono 1 h_iio_subset)
    have h_right_slope := h_slope.mono_left (nhdsWithin_mono 1 h_ioi_subset)
    have h_eq_left := tendsto_nhds_unique h_left_slope h_left_val
    have h_eq_right := tendsto_nhds_unique h_right_slope h_right_val
    rw [h_eq_left] at h_eq_right
    have h_ne : (-(HHeight - Real.sqrt 3 / 2) * I) ≠
        ((1 - s) * (-Real.pi * Real.sqrt 3 / 12 + Real.pi / 12 * I) +
         s * (-1/2 + (1 - Real.sqrt 3 / 2) * I)) := by
      intro heq
      have h_lhs_re : Complex.re (-(HHeight - Real.sqrt 3 / 2) * I) = 0 := by
        have h1 : (HHeight : ℂ) - Real.sqrt 3 / 2 = (1 : ℂ) := by
          simp only [HHeight]; push_cast; ring
        rw [h1]; simp
      have h_rhs_re : Complex.re ((1 - (s:ℂ)) *
              (-Real.pi * Real.sqrt 3 / 12 + Real.pi / 12 * I) +
              (s:ℂ) * (-1/2 + (1 - Real.sqrt 3 / 2) * I)) =
            (1 - s) * (-Real.pi * Real.sqrt 3 / 12) + s * (-1/2) := by
        simp only [Complex.add_re, Complex.mul_re, Complex.sub_re, Complex.ofReal_re,
          Complex.one_re, Complex.div_ofNat_re, Complex.neg_re, Complex.ofReal_im, Complex.I_re,
          Complex.I_im,
          show Complex.im (1 - (s:ℂ)) = 0 from by simp [Complex.sub_im, Complex.ofReal_im],
          show Complex.im ((1:ℂ) - Real.sqrt 3 / 2) = 0 from by
            simp [Complex.sub_im, Complex.ofReal_im, Complex.div_ofNat_im],
          mul_zero, sub_zero, mul_one, Complex.neg_im, Complex.div_ofNat_im, add_zero]
        ring
      have h_re_eq := congr_arg Complex.re heq
      rw [h_lhs_re, h_rhs_re] at h_re_eq
      linarith [h_re_eq, arc_chord_re_neg s hs]
    exact h_ne h_eq_right

/-- The homotopy is not differentiable at `t = 3` (left/right derivatives differ). -/
private lemma not_diffAt_at_three (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    ¬DifferentiableAt ℝ (fun t' => fdBoundaryToPolygonHomotopy (t', s)) 3 := by
    intro hd
    have h_slope := hasDerivAt_iff_tendsto_slope.mp hd.hasDerivAt
    have h_left_val : Tendsto (slope (fun t' => fdBoundaryToPolygonHomotopy (t', s)) 3) (𝓝[<] 3)
        (𝓝 ((1 - s) * (-Real.pi * Real.sqrt 3 / 12 - Real.pi / 12 * I) +
            s * (-1/2 + (Real.sqrt 3 / 2 - 1) * I))) := by
      have h_mem : Ioo 2 3 ∈ 𝓝[<] (3 : ℝ) := Ioo_mem_nhdsLT (by norm_num : (2 : ℝ) < 3)
      let g : ℝ → ℂ := fun t' => (1 - s) • Complex.exp
          (((Real.pi : ℝ) / 2 + (t' - 2) *
              ((Real.pi : ℝ) / 6)) * I) +
        s • chordSegment iPoint rho (t' - 2)
      have h_arc : HasDerivAt (fun t' : ℝ =>
            Complex.exp (((Real.pi : ℝ) / 2 +
                (t' - 2) * ((Real.pi : ℝ) / 6)) * I))
          (((Real.pi : ℝ) / 6) * I * rho) (3 : ℝ) := by
        have h_raw := hasDerivAt_arc_exp (Real.pi / 2) (Real.pi / 6) 2 3
        have h_val : Complex.exp (((↑(Real.pi / 2) : ℂ) +
            ((↑(3 : ℝ) : ℂ) - ↑(2 : ℝ)) * (↑(Real.pi / 6) : ℂ)) * I) = rho := by
          rw [show ((↑(Real.pi / 2) : ℂ) + ((↑(3 : ℝ) : ℂ) - ↑(2 : ℝ)) * (↑(Real.pi / 6) : ℂ)) =
              ↑(2 * Real.pi / 3) from by push_cast; ring]
          exact exp_two_pi_div_three_eq_rho
        rw [h_val] at h_raw
        convert h_raw using 2 <;> push_cast <;> ring
      have h_chord : HasDerivAt (fun t' : ℝ => chordSegment iPoint rho (t' - 2))
          (rho - iPoint) (3 : ℝ) :=
        hasDerivAt_chordSegment_shift iPoint rho 2 3
      have h_combined : HasDerivAt g
          ((1 - s) • (((Real.pi : ℝ) / 6) * I * rho) + s • (rho - iPoint)) (3 : ℝ) := by
        have h1 := h_arc.const_smul (1 - s)
        have h2 := h_chord.const_smul s
        exact h1.add h2
      have h_deriv_eq : (1 - s) • (((Real.pi : ℝ) / 6) * I * rho) + s • (rho - iPoint) =
          (1 - ↑s) * (-↑Real.pi * ↑(Real.sqrt 3) / 12 - ↑Real.pi / 12 * I) +
          ↑s * (-1 / 2 + (↑(Real.sqrt 3) / 2 - 1) * I) := by
        have h1 : ((Real.pi : ℝ) / 6 : ℂ) * I * rho =
            -↑Real.pi * ↑(Real.sqrt 3) / 12 - ↑Real.pi / 12 * I := by
          simp only [rho]; apply Complex.ext <;> simp <;> ring
        have h2 : rho - iPoint = (-1/2 : ℂ) + (↑(Real.sqrt 3) / 2 - 1) * I := by
          simp only [rho, iPoint]; apply Complex.ext <;> simp
        rw [h1, h2]
        simp only [Complex.real_smul]; push_cast; ring
      rw [h_deriv_eq] at h_combined
      refine (hasDerivAt_iff_tendsto_slope.mp h_combined
        |>.mono_left (nhdsWithin_mono (3 : ℝ) (fun y hy => ne_of_lt hy))).congr' ?_
      filter_upwards [h_mem] with t' ht'
      simp only [slope_def_module]
      congr 1
      have h_at_3 : fdBoundaryToPolygonHomotopy (3, s) = g 3 := by
        simp only [fdBoundaryToPolygonHomotopy,
          show ¬(3 : ℝ) ≤ 1 from by norm_num,
          show ¬(3 : ℝ) ≤ 2 from by norm_num,
          show (3 : ℝ) ≤ 3 from le_refl 3,
          ite_false, ite_true]
        dsimp only [g]
        congr 2; congr 1; push_cast; ring
      have h_at_t' : fdBoundaryToPolygonHomotopy (t', s) = g t' := by
        simp only [fdBoundaryToPolygonHomotopy,
          not_le.mpr (lt_trans (by norm_num : (1 : ℝ) < 2) ht'.1), ite_false,
          not_le.mpr ht'.1, le_of_lt ht'.2, ite_true]
        dsimp only [g]; congr 2; congr 1; ring
      rw [h_at_t', h_at_3]
    have h_right_val : Tendsto (slope (fun t' => fdBoundaryToPolygonHomotopy (t', s)) 3) (𝓝[>] 3)
        (𝓝 ((HHeight - Real.sqrt 3 / 2) * I)) := by
      have h_mem : Ioo 3 4 ∈ 𝓝[>] (3 : ℝ) := Ioo_mem_nhdsGT (by norm_num : (3 : ℝ) < 4)
      let f4 : ℝ → ℂ := fun t' =>
        -1/2 + (Real.sqrt 3 / 2 +
            (t' - 3) * (HHeight - Real.sqrt 3 / 2)) * I
      have h_seg4_deriv : HasDerivAt f4 (((HHeight : ℂ) - Real.sqrt 3 / 2) * I)
          (3 : ℝ) :=
        hasDerivAt_straight_seg (-1/2) (Real.sqrt 3 / 2)
          ((HHeight : ℂ) - Real.sqrt 3 / 2) 3 3
      refine (hasDerivAt_iff_tendsto_slope.mp h_seg4_deriv
        |>.mono_left (nhdsWithin_mono (3 : ℝ) (fun y hy => ne_of_gt hy))).congr' ?_
      filter_upwards [h_mem] with t' ht'
      simp only [slope_def_module]
      congr 1
      have h_fbd_eq_rho : fdBoundaryToPolygonHomotopy (3, s) = rho := by
        simp only [fdBoundaryToPolygonHomotopy,
          show ¬(3 : ℝ) ≤ 1 from by norm_num,
          show ¬(3 : ℝ) ≤ 2 from by norm_num,
          show (3 : ℝ) ≤ 3 from le_refl 3,
          ite_false, ite_true]
        have h_exp :
            Complex.exp ((↑Real.pi / 2 +
                (↑(3 : ℝ) - 2) * (2 * ↑Real.pi / 3 -
                    ↑Real.pi / 2)) * I) =
              rho := by
          rw [show (↑Real.pi / 2 + (↑(3 : ℝ) - 2) *
                  (2 * ↑Real.pi / 3 -
                    ↑Real.pi / 2) : ℂ) * I =
            ↑(2 * Real.pi / 3) * I from by push_cast; ring]
          exact exp_two_pi_div_three_eq_rho
        rw [h_exp]
        simp only [chordSegment, iPoint, rho]
        simp only [Complex.real_smul]; push_cast; ring
      have h_f4_eq_rho : f4 3 = rho := by dsimp only [f4]; simp only [rho, HHeight]; push_cast; ring
      have h_at_3 : fdBoundaryToPolygonHomotopy (3, s) = f4 3 := by rw [h_fbd_eq_rho, h_f4_eq_rho]
      have h_at_t' : fdBoundaryToPolygonHomotopy (t', s) = f4 t' := by
        simp only [fdBoundaryToPolygonHomotopy,
          not_le.mpr (lt_trans (by norm_num : (1:ℝ) < 3) ht'.1),
          not_le.mpr (lt_trans (by norm_num : (2:ℝ) < 3) ht'.1),
          not_le.mpr ht'.1, ite_false, le_of_lt ht'.2, ite_true]
        dsimp only [f4]
      rw [h_at_t', h_at_3]
    have h_iio_subset : Set.Iio (3 : ℝ) ⊆ {3}ᶜ := fun y hy => ne_of_lt hy
    have h_ioi_subset : Set.Ioi (3 : ℝ) ⊆ {3}ᶜ := fun y hy => ne_of_gt hy
    have h_left_slope := h_slope.mono_left (nhdsWithin_mono 3 h_iio_subset)
    have h_right_slope := h_slope.mono_left (nhdsWithin_mono 3 h_ioi_subset)
    have h_eq_left := tendsto_nhds_unique h_left_slope h_left_val
    have h_eq_right := tendsto_nhds_unique h_right_slope h_right_val
    rw [h_eq_right] at h_eq_left
    have h_ne : ((1 - s) * (-Real.pi * Real.sqrt 3 / 12 - Real.pi / 12 * I) +
        s * (-1/2 + (Real.sqrt 3 / 2 - 1) * I)) ≠ ((HHeight : ℂ) - Real.sqrt 3 / 2) * I := by
      intro heq
      have h_rhs_re : Complex.re (((HHeight : ℂ) - Real.sqrt 3 / 2) * I) = 0 := by
        have h1 : (HHeight : ℂ) - Real.sqrt 3 / 2 = (1 : ℂ) := by
          simp only [HHeight]; push_cast; ring
        rw [h1, one_mul]; exact Complex.I_re
      have h_lhs_re : Complex.re ((1 - (s:ℂ)) *
              (-Real.pi * Real.sqrt 3 / 12 - Real.pi / 12 * I) +
              (s:ℂ) * (-1/2 + (Real.sqrt 3 / 2 - 1) * I)) =
            (1 - s) * (-Real.pi * Real.sqrt 3 / 12) + s * (-1/2) := by
        simp only [Complex.add_re, Complex.mul_re, Complex.sub_re, Complex.ofReal_re,
          Complex.one_re, Complex.div_ofNat_re, Complex.neg_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im,
          show Complex.im (1 - (s:ℂ)) = 0 from by simp [Complex.sub_im, Complex.ofReal_im],
          show Complex.im ((Real.sqrt 3 : ℂ) / 2 - 1) = 0 from by
            simp [Complex.sub_im, Complex.div_ofNat_im, Complex.ofReal_im],
          mul_zero, sub_zero, mul_one, Complex.neg_im, Complex.div_ofNat_im, add_zero]
        ring
      have h_re_eq := congr_arg Complex.re heq
      rw [h_lhs_re, h_rhs_re] at h_re_eq
      linarith [h_re_eq, arc_chord_re_neg s hs]
    exact h_ne h_eq_left.symm

/-- The homotopy is not differentiable at `t = 4` (left/right derivatives differ). -/
private lemma not_diffAt_at_four (s : ℝ) (_hs : s ∈ Set.Icc (0 : ℝ) 1) :
    ¬DifferentiableAt ℝ (fun t' => fdBoundaryToPolygonHomotopy (t', s)) 4 := by
    intro hd
    have h_slope := hasDerivAt_iff_tendsto_slope.mp hd.hasDerivAt
    have h_left_val : Tendsto (slope (fun t' => fdBoundaryToPolygonHomotopy (t', s)) 4) (𝓝[<] 4)
        (𝓝 ((HHeight - Real.sqrt 3 / 2) * I)) := by
      have h_mem : Ioo 3 4 ∈ 𝓝[<] (4 : ℝ) := Ioo_mem_nhdsLT (by norm_num : (3 : ℝ) < 4)
      apply Tendsto.congr' (f₁ := fun _ => (HHeight - Real.sqrt 3 / 2) * I)
      · filter_upwards [h_mem] with t ht
        simp only [slope_def_module, fdBoundaryToPolygonHomotopy,
          not_le.mpr (lt_trans (by norm_num : (1:ℝ) < 3) ht.1),
          not_le.mpr (lt_trans (by norm_num : (2:ℝ) < 3) ht.1),
          not_le.mpr ht.1, le_of_lt ht.2,
          show ¬(4:ℝ) ≤ 1 from by norm_num, show ¬(4:ℝ) ≤ 2 from by norm_num,
          show ¬(4:ℝ) ≤ 3 from by norm_num, le_refl (4:ℝ), ite_false, ite_true]
        erw [Complex.real_smul]
        have hne : (↑t : ℂ) - 4 ≠ 0 := by
          simp only [sub_ne_zero]; norm_cast; exact ne_of_lt ht.2
        simp only [Complex.ofReal_inv, Complex.ofReal_sub]
        field_simp [hne]; simp only [HHeight]; push_cast; ring
      · exact tendsto_const_nhds
    have h_right_val :
        Tendsto (slope (fun t' => fdBoundaryToPolygonHomotopy (t', s)) 4) (𝓝[>] 4) (𝓝 1) := by
      have h_mem : Ioo 4 5 ∈ 𝓝[>] (4 : ℝ) := Ioo_mem_nhdsGT (by norm_num : (4 : ℝ) < 5)
      apply Tendsto.congr' (f₁ := fun _ => (1 : ℂ))
      · filter_upwards [h_mem] with t ht
        simp only [slope_def_module, fdBoundaryToPolygonHomotopy,
          not_le.mpr (lt_trans (by norm_num : (1:ℝ) < 4) ht.1),
          not_le.mpr (lt_trans (by norm_num : (2:ℝ) < 4) ht.1),
          not_le.mpr (lt_trans (by norm_num : (3:ℝ) < 4) ht.1),
          not_le.mpr ht.1,
          show ¬(4:ℝ) ≤ 1 from by norm_num, show ¬(4:ℝ) ≤ 2 from by norm_num,
          show ¬(4:ℝ) ≤ 3 from by norm_num, le_refl (4:ℝ), ite_false, ite_true]
        erw [Complex.real_smul]
        have hne : (↑t : ℂ) - 4 ≠ 0 := by
          simp only [sub_ne_zero]; norm_cast
          exact ne_of_gt ht.1
        simp only [Complex.ofReal_inv, Complex.ofReal_sub]
        field_simp [hne]
        push_cast; ring
      · exact tendsto_const_nhds
    have h_iio_subset : Set.Iio (4 : ℝ) ⊆ {4}ᶜ := fun y hy => ne_of_lt hy
    have h_ioi_subset : Set.Ioi (4 : ℝ) ⊆ {4}ᶜ := fun y hy => ne_of_gt hy
    have h_left_slope := h_slope.mono_left (nhdsWithin_mono 4 h_iio_subset)
    have h_right_slope := h_slope.mono_left (nhdsWithin_mono 4 h_ioi_subset)
    have h_eq_left := tendsto_nhds_unique h_left_slope h_left_val
    have h_eq_right := tendsto_nhds_unique h_right_slope h_right_val
    rw [h_eq_left] at h_eq_right
    have h_ne : ((HHeight : ℂ) - Real.sqrt 3 / 2) * I ≠ 1 := by
      intro heq
      have h_im := congr_arg Complex.im heq
      simp only [Complex.mul_I_im, Complex.one_im,
                 Complex.sub_re, Complex.ofReal_re, Complex.div_ofNat_re] at h_im
      have h_H_pos : HHeight - Real.sqrt 3 / 2 > 0 := by simp only [HHeight]; norm_num
      linarith
    exact h_ne h_eq_right

/-- The homotopy is NOT differentiable at t ∈ {1, 3, 4}
because left/right derivatives differ. -/
lemma fdBoundaryToPolygonHomotopy_not_diffAt_134 (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (k : ℝ) (hk : k ∈ ({1, 3, 4} : Set ℝ)) :
    ¬DifferentiableAt ℝ (fun t' => fdBoundaryToPolygonHomotopy (t', s)) k := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hk
  rcases hk with rfl | rfl | rfl
  · exact not_diffAt_at_one s hs
  · exact not_diffAt_at_three s hs
  · exact not_diffAt_at_four s hs

/-- Segment 1 derivative continuity: constant function is continuous. -/
lemma deriv_seg1_continuousOn : ContinuousOn
    (fun (_q : ℝ × ℝ) => -(((HHeight : ℂ) - Real.sqrt 3 / 2) * I)) (Set.univ) :=
  continuousOn_const

/-- Segment 4 derivative continuity: constant function is continuous. -/
lemma deriv_seg4_continuousOn : ContinuousOn
    (fun (_q : ℝ × ℝ) => (((HHeight : ℂ) - Real.sqrt 3 / 2) * I)) (Set.univ) :=
  continuousOn_const

/-- Segment 5 derivative continuity: constant function is continuous. -/
lemma deriv_seg5_continuousOn : ContinuousOn (fun (_q : ℝ × ℝ) => (1 : ℂ)) (Set.univ) :=
  continuousOn_const

/-- An interval (p1, p2) avoiding {1,2,3,4} and inside (0,5) lies in exactly one segment. -/
lemma interval_in_segment (p₁ p₂ : ℝ) (_hp : p₁ < p₂)
    (h_avoid : ∀ t ∈ Set.Ioo p₁ p₂,
      t ∉ ({1, 2, 3, 4} : Finset ℝ))
    (_h_sub : Set.Ioo p₁ p₂ ⊆ Set.Ioo 0 5) : (p₂ ≤ 1) ∨ (p₁ ≥ 1 ∧ p₂ ≤ 2) ∨
    (p₁ ≥ 2 ∧ p₂ ≤ 3) ∨ (p₁ ≥ 3 ∧ p₂ ≤ 4) ∨ (p₁ ≥ 4) := by
  by_cases h1 : p₂ ≤ 1
  · left; exact h1
  · right
    by_cases h2 : p₂ ≤ 2
    · left
      constructor
      · by_contra hlt
        have h1_in : (1 : ℝ) ∈ Set.Ioo p₁ p₂ := ⟨not_le.mp hlt, not_le.mp h1⟩
        have := h_avoid 1 h1_in
        exact absurd (Finset.mem_insert_self 1 _) this
      · exact h2
    · right
      by_cases h3 : p₂ ≤ 3
      · left
        constructor
        · by_contra hlt
          have h2_in : (2 : ℝ) ∈ Set.Ioo p₁ p₂ := ⟨not_le.mp hlt, not_le.mp h2⟩
          have := h_avoid 2 h2_in
          exact absurd (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert_self 2 _))) this
        · exact h3
      · right
        by_cases h4 : p₂ ≤ 4
        · left
          constructor
          · by_contra hlt
            have h3_in : (3 : ℝ) ∈ Set.Ioo p₁ p₂ := ⟨not_le.mp hlt, not_le.mp h3⟩
            have := h_avoid 3 h3_in
            exact absurd (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr
              (Or.inr (Finset.mem_insert_self 3 _))))) this
          · exact h4
        · right
          by_contra hlt
          have h4_in : (4 : ℝ) ∈ Set.Ioo p₁ p₂ := ⟨not_le.mp hlt, not_le.mp h4⟩
          have := h_avoid 4 h4_in
          exact absurd (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr
            (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self 4))))))) this

end RectHomotopyProof
