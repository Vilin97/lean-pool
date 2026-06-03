/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import LeanPool.LeanModularForms.ValenceFormula.RectHomotopy.RadialHomotopy

/-!
# Angle analysis and winding number invariance

Defines angle functions for fdPolygonRadialCircle and circleParamCW, analyzes the
branch cut crossing on segment 4, constructs a lifted angle that tracks the full
-2π rotation, and proves center-translation invariance of the winding number.

* `angleOnCircle`, `fdPolygonRadialCircleAngle` — angle of radial projection
* `tL` — time when vector crosses negative real axis on seg4
* `fdPolygonRadialCircleAngleLifted` — lifted angle accounting for branch cut
* `refP₀` — reference point on imaginary axis
* `winding_fdPolygon_center_invariant` — winding number preserved under center translation
-/

open Complex Set Metric Filter Topology

namespace RectHomotopyProof

/-- The angle of a point on the unit circle around p. -/
noncomputable def angleOnCircle (p : ℂ) (z : ℂ) : ℝ := Complex.arg (z - p)

/-- The angle function for fdPolygonRadialCircle. -/
noncomputable def fdPolygonRadialCircleAngle (p : ℂ) : ℝ → ℝ := fun t =>
  angleOnCircle p (fdPolygonRadialCircle p t)

/-- The angle function for circleParamCW. -/
noncomputable def circleParamCWAngle : ℝ → ℝ := fun t =>
  2 * Real.pi * (5 - t) / 5

/-- S¹ angle interpolation homotopy. -/
noncomputable def angleHomotopy (p : ℂ) : ℝ × ℝ → ℂ := fun (t, s) =>
  let θ₁ := fdPolygonRadialCircleAngle p t
  let θ₂ := circleParamCWAngle t
  p + Complex.exp (I * ((1 - s) * θ₁ + s * θ₂))

/-- Polygon vertex at t=0: top-right corner (1/2 + HHeight·i). -/
lemma fdPolygon_at_zero : fdPolygon 0 = 1/2 + HHeight * I := by
  simp only [fdPolygon]
  norm_num

/-- Polygon vertex at t=1: rho'. -/
lemma fdPolygon_at_one : fdPolygon 1 = rho' := by
  simp only [fdPolygon, HHeight, rho', chordSegment]
  norm_num

/-- Polygon vertex at t=4: top-left corner (-1/2 + HHeight·i). -/
lemma fdPolygon_at_four : fdPolygon 4 = -1/2 + HHeight * I := by
  simp only [fdPolygon, HHeight]
  norm_num

/-- Direction from p to z0 is in Q1 (re > 0, im > 0). -/
lemma v0_quadrant (p : ℂ) (hp_re : |p.re| < 1 / 2) (hp_im : p.im < HHeight) :
    (fdPolygon 0 - p).re > 0 ∧ (fdPolygon 0 - p).im > 0 := by
  rw [fdPolygon_at_zero]
  have hpre : p.re < 1/2 := (abs_lt.mp hp_re).2
  constructor
  · have : (1/2 + HHeight * I - p).re = 1/2 - p.re := by
      simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
                 Complex.I_re, Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul,
                 Complex.div_ofNat_re, Complex.one_re, sub_self, add_zero]
    linarith
  · have : (1/2 + HHeight * I - p).im = HHeight - p.im := by
      simp only [Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.ofReal_re,
                 Complex.I_re, Complex.I_im, Complex.ofReal_im, mul_one, zero_mul, add_zero,
                 Complex.div_ofNat_im, Complex.one_im, zero_div, zero_add]
    linarith

/-- For interior points with ‖p‖ > 1, |p.re| < 1/2, 0 < p.im, we have p.im > √3/2. -/
lemma interior_point_im_bound (p : ℂ) (hp_norm : ‖p‖ > 1)
    (hp_re : |p.re| < 1 / 2) (hp_im_pos : 0 < p.im) :
    p.im > Real.sqrt 3 / 2 := by
  have hpre_sq : p.re ^ 2 < 1/4 := by
    have h := abs_lt.mp hp_re
    nlinarith [sq_abs p.re]
  have hnorm_sq : p.re ^ 2 + p.im ^ 2 > 1 := by
    rw [Complex.norm_eq_sqrt_sq_add_sq] at hp_norm
    have h_sum_nonneg : 0 ≤ p.re^2 + p.im^2 := by positivity
    calc p.re^2 + p.im^2 = (Real.sqrt (p.re^2 + p.im^2))^2 := (Real.sq_sqrt h_sum_nonneg).symm
      _ > 1^2 := by nlinarith
      _ = 1 := by ring
  have hp_im_sq : p.im ^ 2 > 3/4 := by linarith
  have h4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  have h3 : Real.sqrt (3/4) = Real.sqrt 3 / 2 := by
    rw [Real.sqrt_div (by norm_num : (3 : ℝ) ≥ 0), h4]
  rw [← h3, gt_iff_lt, Real.sqrt_lt' hp_im_pos]
  linarith

/-- Direction from p to fdPolygon 1 (= rho') is in Q4 (re > 0, im < 0). -/
lemma v1_quadrant (p : ℂ) (hp_norm : ‖p‖ > 1) (hp_re : |p.re| < 1 / 2)
    (hp_im_pos : 0 < p.im) : (fdPolygon 1 - p).re > 0 ∧ (fdPolygon 1 - p).im < 0 := by
  rw [fdPolygon_at_one]
  have hpre : p.re < 1/2 := (abs_lt.mp hp_re).2
  have hbound := interior_point_im_bound p hp_norm hp_re hp_im_pos
  have hre : (rho' - p).re = 1/2 - p.re := by simp [rho']
  have him : (rho' - p).im = Real.sqrt 3 / 2 - p.im := by simp [rho']
  exact ⟨by linarith, by linarith⟩

/-- Polygon vertex at t=3: rho. -/
lemma fdPolygon_at_three : fdPolygon 3 = rho := by
  simp only [fdPolygon, chordSegment, iPoint, rho]
  norm_num

/-- Direction from p to fdPolygon 3 (= rho) is in Q3 (re < 0, im < 0). -/
lemma v3_quadrant (p : ℂ) (hp_norm : ‖p‖ > 1) (hp_re : |p.re| < 1 / 2)
    (hp_im_pos : 0 < p.im) : (fdPolygon 3 - p).re < 0 ∧ (fdPolygon 3 - p).im < 0 := by
  rw [fdPolygon_at_three]
  have hpre : -1/2 < p.re := by linarith [(abs_lt.mp hp_re).1]
  have hbound := interior_point_im_bound p hp_norm hp_re hp_im_pos
  have hre : (rho - p).re = -1/2 - p.re := by simp [rho]
  have him : (rho - p).im = Real.sqrt 3 / 2 - p.im := by simp [rho]
  exact ⟨by linarith, by linarith⟩

/-- Direction from p to fdPolygon 4 is in Q2 (re < 0, im > 0). -/
lemma v4_quadrant (p : ℂ) (hp_re : |p.re| < 1 / 2) (hp_im : p.im < HHeight) :
    (fdPolygon 4 - p).re < 0 ∧ (fdPolygon 4 - p).im > 0 := by
  rw [fdPolygon_at_four]
  have hpre_neg : -(1/2) < p.re := (abs_lt.mp hp_re).1
  have hpre : -1/2 < p.re := by linarith
  have hre : (-1/2 + HHeight * I - p).re = -1/2 - p.re := by
    simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
               Complex.I_re, Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul,
               Complex.neg_re, Complex.div_ofNat_re, Complex.one_re, sub_self, add_zero]
  have him : (-1/2 + HHeight * I - p).im = HHeight - p.im := by
    simp only [Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.ofReal_re,
               Complex.I_re, Complex.I_im, Complex.ofReal_im, mul_one, zero_mul,
               Complex.neg_im, Complex.div_ofNat_im, Complex.one_im, zero_div, neg_zero,
               zero_add, add_zero]
  constructor
  · rw [hre]; linarith
  · rw [him]; linarith

/-- Q1: re > 0, im > 0 → 0 < arg < π/2. -/
lemma arg_Q1 (z : ℂ) (hz_re : 0 < z.re) (hz_im : 0 < z.im) :
    0 < z.arg ∧ z.arg < Real.pi / 2 := by
  constructor
  · have h_nonneg : 0 ≤ z.arg := Complex.arg_nonneg_iff.mpr hz_im.le
    have h_ne : z.arg ≠ 0 := by
      intro h_eq
      rw [Complex.arg_eq_zero_iff] at h_eq
      linarith [h_eq.2]
    exact lt_of_le_of_ne h_nonneg (Ne.symm h_ne)
  · rw [Complex.arg_lt_pi_div_two_iff]
    left; exact hz_re

/-- Q4: re > 0, im < 0 → -π/2 < arg < 0. -/
lemma arg_Q4 (z : ℂ) (hz_re : 0 < z.re) (hz_im : z.im < 0) :
    -(Real.pi / 2) < z.arg ∧ z.arg < 0 := by
  constructor
  · rw [Complex.neg_pi_div_two_lt_arg_iff]
    left; exact hz_re
  · rw [Complex.arg_neg_iff]
    exact hz_im

/-- Q3: im < 0 → -π < arg < 0. -/
lemma arg_Q3 (z : ℂ) (hz_im : z.im < 0) :
    -Real.pi < z.arg ∧ z.arg < 0 := by
  constructor
  · exact (Complex.arg_mem_Ioc z).1
  · rw [Complex.arg_neg_iff]
    exact hz_im

/-- Q2: re < 0, im > 0 → π/2 < arg ≤ π. -/
lemma arg_Q2 (z : ℂ) (hz_re : z.re < 0) (hz_im : 0 < z.im) :
    Real.pi / 2 < z.arg ∧ z.arg ≤ Real.pi := by
  constructor
  · by_contra h
    push Not at h
    rw [Complex.arg_le_pi_div_two_iff] at h
    cases h with
    | inl h_re_pos => linarith
    | inr h_im_neg => linarith
  · exact (Complex.arg_mem_Ioc z).2

/-- The unique time on seg4 where (fdPolygon t - p) crosses the negative real axis. -/
noncomputable def tL (p : ℂ) : ℝ :=
  3 + (p.im - Real.sqrt 3 / 2) / (HHeight - Real.sqrt 3 / 2)

/-- tL is in (3, 4) for interior points. -/
lemma tL_mem_Ioo (p : ℂ) (hp_norm : ‖p‖ > 1) (hp_re : |p.re| < 1 / 2)
    (hp_im_pos : 0 < p.im) (hp_im : p.im < HHeight) :
    tL p ∈ Set.Ioo (3 : ℝ) 4 := by
  have hbound := interior_point_im_bound p hp_norm hp_re hp_im_pos
  have hH : HHeight = Real.sqrt 3 / 2 + 1 := rfl
  have hdenom_pos : HHeight - Real.sqrt 3 / 2 > 0 := by rw [hH]; linarith
  have hnum_pos : p.im - Real.sqrt 3 / 2 > 0 := by linarith
  have hnum_lt : p.im - Real.sqrt 3 / 2 < HHeight - Real.sqrt 3 / 2 := by
    linarith
  simp only [tL, Set.mem_Ioo]
  constructor
  · linarith [div_pos hnum_pos hdenom_pos]
  · linarith [(div_lt_one hdenom_pos).mpr hnum_lt]

/-- On seg4, (fdPolygon t - p).re < 0. -/
lemma seg4_vec_re_neg (p : ℂ) (hp_re : |p.re| < 1 / 2) (t : ℝ)
    (ht : t ∈ Set.Ioc (3 : ℝ) 4) : (fdPolygon t - p).re < 0 := by
  have hpre : -1/2 < p.re := by linarith [(abs_lt.mp hp_re).1]
  have hseg4_re : (fdPolygon t).re = -1/2 := by
    simp only [fdPolygon]
    split_ifs with h1 h2 h3 h4
    · linarith [ht.1]
    · linarith [ht.1]
    · linarith [ht.1]
    · simp
    · linarith [ht.2]
  rw [Complex.sub_re, hseg4_re]
  linarith

/-- On seg4, the imaginary part of fdPolygon t. -/
lemma seg4_im_formula (t : ℝ) (ht : t ∈ Set.Ioc (3 : ℝ) 4) : (fdPolygon t).im =
      Real.sqrt 3 / 2 + (t - 3) * (HHeight - Real.sqrt 3 / 2) := by
  simp only [fdPolygon]
  split_ifs with h1 h2 h3 h4
  · linarith [ht.1]
  · linarith [ht.1]
  · linarith [ht.1]
  · have h : (-1/2 + (Real.sqrt 3 / 2 + (t - 3) * (HHeight - Real.sqrt 3 / 2)) * I).im =
        Real.sqrt 3 / 2 + (t - 3) * (HHeight - Real.sqrt 3 / 2) := by
      simp [Complex.add_im, Complex.mul_im, Complex.I_re,
        Complex.I_im, Complex.ofReal_im]
    exact h
  · linarith [ht.2]

/-- Sign of (fdPolygon t - p).im on seg4: negative before tL, zero at tL,
    positive after. -/
lemma seg4_vec_im_sign (p : ℂ) (hp_norm : ‖p‖ > 1) (hp_re : |p.re| < 1 / 2) (hp_im_pos : 0 < p.im)
    (hp_im : p.im < HHeight) (t : ℝ) (ht : t ∈ Set.Ioc (3 : ℝ) 4) :
    (t < tL p → (fdPolygon t - p).im < 0) ∧ (t = tL p → (fdPolygon t - p).im = 0) ∧
    (tL p < t → 0 < (fdPolygon t - p).im) := by
  have hbound := interior_point_im_bound p hp_norm hp_re hp_im_pos
  have hH : HHeight = Real.sqrt 3 / 2 + 1 := rfl
  have hdenom_pos : HHeight - Real.sqrt 3 / 2 > 0 := by rw [hH]; linarith
  have hdenom_ne : HHeight - Real.sqrt 3 / 2 ≠ 0 := ne_of_gt hdenom_pos
  have him := seg4_im_formula t ht
  set D := HHeight - Real.sqrt 3 / 2 with hD_def
  have him_eq : (fdPolygon t - p).im = D * (t - tL p) := by
    rw [Complex.sub_im, him, tL, hD_def]
    have h1 : Real.sqrt 3 / 2 + (t - 3) * (HHeight - Real.sqrt 3 / 2) - p.im =
        (HHeight - Real.sqrt 3 / 2) * (t - 3) + (Real.sqrt 3 / 2 - p.im) := by ring
    rw [h1]
    have h2 : (HHeight - Real.sqrt 3 / 2) * (t - (3 + (p.im - Real.sqrt 3 / 2) /
          (HHeight - Real.sqrt 3 / 2))) =
        (HHeight - Real.sqrt 3 / 2) * (t - 3) - (HHeight - Real.sqrt 3 / 2) *
            ((p.im - Real.sqrt 3 / 2) / (HHeight - Real.sqrt 3 / 2)) := by ring
    rw [h2, mul_div_cancel₀ _ hdenom_ne]
    ring
  refine ⟨?_, ?_, ?_⟩
  · intro hlt; rw [him_eq]
    exact mul_neg_of_pos_of_neg hdenom_pos (by linarith)
  · intro heq; rw [him_eq, heq, sub_self, mul_zero]
  · intro hgt; rw [him_eq]; exact mul_pos hdenom_pos (by linarith)

/-- At tL, the vector fdPolygon t - p is a nonzero negative real. -/
lemma seg4_vec_at_tL (p : ℂ) (hp_norm : ‖p‖ > 1) (hp_re : |p.re| < 1 / 2) (hp_im_pos : 0 < p.im)
    (hp_im : p.im < HHeight) : (fdPolygon (tL p) - p).re < 0 ∧ (fdPolygon (tL p) - p).im = 0 := by
  have htL := tL_mem_Ioo p hp_norm hp_re hp_im_pos hp_im
  have htL_Ioc : tL p ∈ Set.Ioc (3 : ℝ) 4 :=
    ⟨htL.1, le_of_lt htL.2⟩
  exact ⟨seg4_vec_re_neg p hp_re (tL p) htL_Ioc,
    (seg4_vec_im_sign p hp_norm hp_re hp_im_pos hp_im (tL p) htL_Ioc
      ).2.1 rfl⟩

/-- arg at tL equals π (negative real). -/
lemma arg_at_tL_eq_pi (p : ℂ) (hp_norm : ‖p‖ > 1) (hp_re : |p.re| < 1 / 2) (hp_im_pos : 0 < p.im)
    (hp_im : p.im < HHeight) :
    Complex.arg (fdPolygon (tL p) - p) = Real.pi := by
  have hvec := seg4_vec_at_tL p hp_norm hp_re hp_im_pos hp_im
  rw [Complex.arg_eq_pi_iff]
  exact ⟨hvec.1, hvec.2⟩

/-- Before tL on seg4: arg < 0. -/
lemma arg_seg4_before (p : ℂ) (hp_norm : ‖p‖ > 1) (hp_re : |p.re| < 1 / 2) (hp_im_pos : 0 < p.im)
    (hp_im : p.im < HHeight) (t : ℝ) (ht : t ∈ Set.Ioc (3 : ℝ) 4) (htL : t < tL p) :
    Complex.arg (fdPolygon t - p) < 0 := by
  have him := (seg4_vec_im_sign p hp_norm hp_re hp_im_pos hp_im t ht).1 htL
  exact (arg_Q3 (fdPolygon t - p) him).2

/-- After tL on seg4: arg > 0. -/
lemma arg_seg4_after (p : ℂ) (hp_norm : ‖p‖ > 1) (hp_re : |p.re| < 1 / 2) (hp_im_pos : 0 < p.im)
    (hp_im : p.im < HHeight) (t : ℝ) (ht : t ∈ Set.Ioc (3 : ℝ) 4) (htL : tL p < t) :
    0 < Complex.arg (fdPolygon t - p) := by
  have hre := seg4_vec_re_neg p hp_re t ht
  have him := (seg4_vec_im_sign p hp_norm hp_re hp_im_pos hp_im t ht).2.2 htL
  linarith [(arg_Q2 (fdPolygon t - p) hre him).1, Real.pi_pos]

/-- arg is preserved under normalization. -/
lemma arg_normalize_eq (z : ℂ) (hz : z ≠ 0) :
    Complex.arg (z / ‖z‖) = Complex.arg z := by
  rw [div_eq_mul_inv, show z * (↑‖z‖)⁻¹ = z * (‖z‖⁻¹ : ℝ) from by
    congr 1; simp only [Complex.ofReal_inv]]
  exact Complex.arg_mul_real (inv_pos_of_pos (norm_pos_iff.mpr hz)) z

/-- fdPolygonRadialCircleAngle equals arg(fdPolygon t - p). -/
lemma fdPolygonRadialCircle_angle_eq_arg (p : ℂ) (t : ℝ) (hne : fdPolygon t ≠ p) :
    fdPolygonRadialCircleAngle p t =
      Complex.arg (fdPolygon t - p) := by
  simp only [fdPolygonRadialCircleAngle, angleOnCircle,
    fdPolygonRadialCircle, polygonToCircleRadial]
  set dir := fdPolygon t - p with hdir_def
  simp only [show (1 - 1 : ℝ) * ‖dir‖ + 1 = 1 from by ring, add_sub_cancel_left]
  erw [one_smul]
  exact arg_normalize_eq dir (sub_ne_zero.mpr hne)

/-- Lifted angle function that accounts for branch cut crossing. -/
noncomputable def fdPolygonRadialCircleAngleLifted (p : ℂ) :
    ℝ → ℝ := fun t =>
  if t < tL p then Complex.arg (fdPolygon t - p)
  else Complex.arg (fdPolygon t - p) - 2 * Real.pi

/-- fdPolygon 0 ≠ p for interior points. -/
lemma fdPolygon_zero_ne_interior (p : ℂ) (hp_im : p.im < HHeight) : fdPolygon 0 ≠ p := by
  rw [fdPolygon_at_zero]
  intro heq
  have him : (1/2 + HHeight * I).im = HHeight := by
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re, Complex.I_im,
               Complex.ofReal_im, mul_one, zero_mul, Complex.div_ofNat_im, Complex.one_im,
               zero_div, zero_add, add_zero]
  have hp_im' : p.im = HHeight := by rw [← heq]; exact him
  linarith

/-- fdPolygon 5 ≠ p for interior points. -/
lemma fdPolygon_five_ne_interior (p : ℂ) (hp_im : p.im < HHeight) : fdPolygon 5 ≠ p := by
  have h : fdPolygon 5 = fdPolygon 0 := by
    simp only [fdPolygon]; norm_num
  rw [h]
  exact fdPolygon_zero_ne_interior p hp_im

/-- At t=0, the lifted angle equals the raw angle (0 < tL). -/
lemma lifted_angle_at_zero (p : ℂ) (hp_norm : ‖p‖ > 1) (hp_re : |p.re| < 1 / 2)
    (hp_im_pos : 0 < p.im)
    (hp_im : p.im < HHeight) :
    fdPolygonRadialCircleAngleLifted p 0 =
      fdPolygonRadialCircleAngle p 0 := by
  have htL := tL_mem_Ioo p hp_norm hp_re hp_im_pos hp_im
  simp only [fdPolygonRadialCircleAngleLifted]
  rw [if_pos (by linarith [htL.1] : (0 : ℝ) < tL p)]
  rw [← fdPolygonRadialCircle_angle_eq_arg p 0 (fdPolygon_zero_ne_interior p hp_im)]

/-- At t=5, the lifted angle is raw angle minus 2π (5 > tL). -/
lemma lifted_angle_at_five (p : ℂ) (hp_norm : ‖p‖ > 1) (hp_re : |p.re| < 1 / 2)
    (hp_im_pos : 0 < p.im)
    (hp_im : p.im < HHeight) :
    fdPolygonRadialCircleAngleLifted p 5 =
      fdPolygonRadialCircleAngle p 5 - 2 * Real.pi := by
  have htL := tL_mem_Ioo p hp_norm hp_re hp_im_pos hp_im
  simp only [fdPolygonRadialCircleAngleLifted]
  rw [if_neg (by linarith [htL.2] : ¬(5 : ℝ) < tL p)]
  rw [← fdPolygonRadialCircle_angle_eq_arg p 5 (fdPolygon_five_ne_interior p hp_im)]

/-- fdPolygon is periodic with period 5. -/
lemma fdPolygon_periodic : fdPolygon 5 = fdPolygon 0 := by
  simp only [fdPolygon]
  norm_num

/-- The raw angle at 5 equals the raw angle at 0. -/
lemma fdPolygonRadialCircle_angle_periodic (p : ℂ) :
    fdPolygonRadialCircleAngle p 5 =
      fdPolygonRadialCircleAngle p 0 := by
  simp only [fdPolygonRadialCircleAngle, angleOnCircle,
    fdPolygonRadialCircle, polygonToCircleRadial]
  rw [show fdPolygon 5 = fdPolygon 0 by simp only [fdPolygon]; norm_num]

/-- The lifted angle total change is -2π. -/
lemma fdPolygonRadialCircle_angle_lifted_change (p : ℂ) (hp_norm : ‖p‖ > 1) (hp_re : |p.re| < 1 / 2)
    (hp_im_pos : 0 < p.im) (hp_im : p.im < HHeight) :
    fdPolygonRadialCircleAngleLifted p 5 =
      fdPolygonRadialCircleAngleLifted p 0 - 2 * Real.pi := by
  rw [lifted_angle_at_zero p hp_norm hp_re hp_im_pos hp_im]
  rw [lifted_angle_at_five p hp_norm hp_re hp_im_pos hp_im]
  rw [fdPolygonRadialCircle_angle_periodic]

/-- Equality form of wrap count. -/
lemma fdPolygonRadialCircle_angle_change (p : ℂ) (hp_norm : ‖p‖ > 1) (hp_re : |p.re| < 1 / 2)
    (hp_im_pos : 0 < p.im) (hp_im : p.im < HHeight) :
    fdPolygonRadialCircleAngleLifted p 5 =
      fdPolygonRadialCircleAngleLifted p 0 - 2 * Real.pi :=
  fdPolygonRadialCircle_angle_lifted_change p hp_norm hp_re
    hp_im_pos hp_im

/-- Wrap count for the lifted angle function. -/
lemma fdPolygonRadialCircle_wrapCount (p : ℂ) (hp_norm : ‖p‖ > 1) (hp_re : |p.re| < 1 / 2)
    (hp_im_pos : 0 < p.im) (hp_im : p.im < HHeight) :
    ∃ θ₀ : ℝ,
      fdPolygonRadialCircleAngleLifted p 0 = θ₀ ∧
      fdPolygonRadialCircleAngleLifted p 5 = θ₀ - 2 * Real.pi := by
  exact ⟨_, rfl, fdPolygonRadialCircle_angle_change p hp_norm hp_re
    hp_im_pos hp_im⟩

/-- circleParamCW also makes exactly one clockwise loop. -/
lemma circleParamCW_wrapCount :
    circleParamCWAngle 0 = 2 * Real.pi ∧
      circleParamCWAngle 5 = 0 := by
  constructor
  · simp only [circleParamCWAngle]; norm_num
  · simp only [circleParamCWAngle]; norm_num

/-- Reference Y-coordinate on imaginary axis. -/
noncomputable def refY₀ : ℝ := (1 + HHeight) / 2

/-- The reference point p₀ = I * Y₀ on the imaginary axis. -/
noncomputable def refP₀ : ℂ := Complex.I * (refY₀ : ℂ)

lemma ref_Y₀_pos : 0 < refY₀ := by
  unfold refY₀ HHeight
  linarith [Real.sqrt_pos_of_pos (by norm_num : (0 : ℝ) < 3)]

lemma ref_Y₀_gt_one : 1 < refY₀ := by
  unfold refY₀ HHeight
  linarith [Real.sqrt_pos_of_pos (by norm_num : (0 : ℝ) < 3)]

lemma ref_Y₀_lt_H : refY₀ < HHeight := by
  unfold refY₀ HHeight
  linarith [Real.sqrt_pos_of_pos (by norm_num : (0 : ℝ) < 3)]

lemma ref_p₀_norm : ‖refP₀‖ > 1 := by
  unfold refP₀
  rw [Complex.norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos ref_Y₀_pos]
  exact ref_Y₀_gt_one

lemma ref_p₀_re : |refP₀.re| < 1 / 2 := by
  unfold refP₀
  simp only [Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, sub_zero]
  norm_num

lemma ref_p₀_im_pos : 0 < refP₀.im := by
  unfold refP₀
  simp only [Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul]
  linarith [ref_Y₀_pos]

lemma ref_p₀_im : refP₀.im < HHeight := by
  unfold refP₀
  simp only [Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul]
  linarith [ref_Y₀_lt_H]

/-- Center-translation homotopy invariance of winding number. -/
lemma winding_fdPolygon_center_invariant (p₁ p₂ : ℂ)
    (_hp₁_norm : ‖p₁‖ > 1) (_hp₁_re : |p₁.re| < 1 / 2) (_hp₁_im : p₁.im < HHeight)
    (_hp₂_norm : ‖p₂‖ > 1) (_hp₂_re : |p₂.re| < 1 / 2) (_hp₂_im : p₂.im < HHeight)
    (havoid : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 5,
      fdPolygon t ≠ (1 - (s : ℂ)) * p₁ + (s : ℂ) * p₂) :
    generalizedWindingNumber' fdPolygon 0 5 p₁ =
    generalizedWindingNumber' fdPolygon 0 5 p₂ := by
  have winding_translate : ∀ (γ : ℝ → ℂ) (c : ℂ),
      generalizedWindingNumber' (fun t => γ t - c) 0 5 0 =
      generalizedWindingNumber' γ 0 5 c := by
    intro γ c
    unfold generalizedWindingNumber' cauchyPrincipalValue'
    simp only [sub_zero]
  let γ₀ : ℝ → ℂ := fun t => fdPolygon t - p₁
  let γ₁ : ℝ → ℂ := fun t => fdPolygon t - p₂
  let H : ℝ × ℝ → ℂ := fun (t, s) =>
    fdPolygon t - ((1 - (s : ℂ)) * p₁ + (s : ℂ) * p₂)
  have hab : (0 : ℝ) < 5 := by norm_num
  suffices h_hom : PiecewiseCurvesHomotopicAvoiding γ₀ γ₁ 0 5 0
      ({1, 2, 3, 4} : Finset ℝ) by
    rw [← winding_translate fdPolygon p₁, ← winding_translate fdPolygon p₂]
    exact windingNumber_eq_of_piecewise_homotopic γ₀ γ₁ 0 5 0
      ({1, 2, 3, 4} : Finset ℝ) hab h_hom
  refine ⟨H, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fdPolygon_continuous.comp continuous_fst |>.sub ((continuous_const.sub
        (Complex.continuous_ofReal.comp continuous_snd)).mul
          continuous_const |>.add
        ((Complex.continuous_ofReal.comp continuous_snd).mul
          continuous_const))
  · intro t _ht; simp [H, γ₀]
  · intro t _ht; simp [H, γ₁]
  · intro s _hs; simp only [H]; rw [fdPolygon_closed]
  · intro t ht s hs
    simp only [H]; rw [sub_ne_zero]; exact havoid s hs t ht
  · intro t ht ht_not_P _s _hs
    exact (fdPolygon_differentiableAt_off_partition t ht ht_not_P
      ).sub_const _
  · intro q₁ q₂ hq₁q₂ hpiece h_sub
    have h_deriv_eq : ∀ q ∈ Ioo q₁ q₂ ×ˢ Icc (0 : ℝ) 1,
        deriv (fun t' => H (t', q.2)) q.1 = deriv fdPolygon q.1 := by
      intro ⟨t, s⟩ ⟨ht, _hs⟩
      change deriv (fun t' => fdPolygon t' - ((1 - ↑s) * p₁ + ↑s * p₂)) t = deriv fdPolygon t
      exact deriv_sub_const _
    suffices h_cont : ContinuousOn (fun q : ℝ × ℝ => deriv fdPolygon q.1)
        (Ioo q₁ q₂ ×ˢ Icc 0 1) by
      exact h_cont.congr (fun q hq => h_deriv_eq q hq)
    have h_deriv_fdPolygon_cont :
        ContinuousOn (deriv fdPolygon) (Ioo q₁ q₂) := by
      apply continuousOn_of_forall_continuousAt
      intro t ht
      have ht_Ioo : t ∈ Ioo 0 5 := h_sub ht
      have ht_not_P : t ∉ ({1, 2, 3, 4} : Finset ℝ) := hpiece t ht
      simp only [Finset.mem_insert, Finset.mem_singleton,
        not_or] at ht_not_P
      obtain ⟨ht_ne1, ht_ne2, ht_ne3, ht_ne4⟩ := ht_not_P
      by_cases h1 : t < 1
      · have h_eq_nhds : deriv fdPolygon =ᶠ[𝓝 t]
            fun _ => -(HHeight - Real.sqrt 3 / 2) * I := by
          have heq : fdPolygon =ᶠ[𝓝 t] fdPolygonSeg1 := (eventually_lt_nhds h1).and
              (eventually_gt_nhds ht_Ioo.1) |>.mono
              fun u ⟨hu1, hu2⟩ => by
                simp [fdPolygon, show u ≤ 1 from le_of_lt hu1,
                  fdPolygonSeg1]
          exact heq.deriv.trans (by filter_upwards with u; rw [fdPolygon_deriv_seg1])
        exact continuousAt_const.congr h_eq_nhds.symm
      · push Not at h1
        by_cases h2 : t < 2
        · have h1' : t > 1 :=
            lt_of_le_of_ne h1 (Ne.symm ht_ne1)
          have h_eq_nhds : deriv fdPolygon =ᶠ[𝓝 t]
              fun _ => iPoint - rho' := by
            have heq : fdPolygon =ᶠ[𝓝 t] fdPolygonSeg2 := (eventually_gt_nhds h1').and
                (eventually_lt_nhds h2) |>.mono
                fun u ⟨hu1, hu2⟩ => by
                  simp [fdPolygon, not_le.mpr hu1,
                    le_of_lt hu2, fdPolygonSeg2]
            exact heq.deriv.trans
              (by filter_upwards with u; rw [fdPolygon_deriv_seg2])
          exact continuousAt_const.congr h_eq_nhds.symm
        · push Not at h2
          by_cases h3 : t < 3
          · have h2' : t > 2 :=
              lt_of_le_of_ne h2 (Ne.symm ht_ne2)
            have h_eq_nhds : deriv fdPolygon =ᶠ[𝓝 t]
                fun _ => rho - iPoint := by
              have heq : fdPolygon =ᶠ[𝓝 t] fdPolygonSeg3 :=
                (eventually_gt_nhds h2').and (eventually_lt_nhds h3) |>.mono
                  fun u ⟨hu1, hu2⟩ => by
                    simp [fdPolygon,
                      not_le.mpr (lt_trans (by norm_num : (1 : ℝ) < 2) hu1),
                      not_le.mpr hu1, le_of_lt hu2,
                      fdPolygonSeg3]
              exact heq.deriv.trans
                (by filter_upwards with u; rw [fdPolygon_deriv_seg3])
            exact continuousAt_const.congr h_eq_nhds.symm
          · push Not at h3
            by_cases h4 : t < 4
            · have h3' : t > 3 :=
                lt_of_le_of_ne h3 (Ne.symm ht_ne3)
              have h_eq_nhds : deriv fdPolygon =ᶠ[𝓝 t]
                  fun _ => (HHeight - Real.sqrt 3 / 2) * I := by
                have heq : fdPolygon =ᶠ[𝓝 t]
                    fdPolygonSeg4 :=
                  (eventually_gt_nhds h3').and (eventually_lt_nhds h4) |>.mono
                    fun u ⟨hu1, hu2⟩ => by
                      simp [fdPolygon,
                        not_le.mpr (lt_trans (by norm_num : (1 : ℝ) < 3) hu1),
                        not_le.mpr (lt_trans (by norm_num : (2 : ℝ) < 3) hu1),
                        not_le.mpr hu1, le_of_lt hu2,
                        fdPolygonSeg4]
                exact heq.deriv.trans
                  (by filter_upwards with u; rw [fdPolygon_deriv_seg4])
              exact continuousAt_const.congr h_eq_nhds.symm
            · push Not at h4
              have h4' : t > 4 :=
                lt_of_le_of_ne h4 (Ne.symm ht_ne4)
              have h_eq_nhds : deriv fdPolygon =ᶠ[𝓝 t]
                  fun _ => (1 : ℂ) := by
                have heq : fdPolygon =ᶠ[𝓝 t]
                    fdPolygonSeg5 :=
                  (eventually_gt_nhds h4').and (eventually_lt_nhds ht_Ioo.2) |>.mono
                    fun u ⟨hu1, hu2⟩ => by
                      simp [fdPolygon,
                        not_le.mpr (lt_trans (by norm_num : (1 : ℝ) < 4) hu1),
                        not_le.mpr (lt_trans (by norm_num : (2 : ℝ) < 4) hu1),
                        not_le.mpr (lt_trans (by norm_num : (3 : ℝ) < 4) hu1),
                        not_le.mpr hu1, fdPolygonSeg5]
                exact heq.deriv.trans
                  (by filter_upwards with u; rw [fdPolygon_deriv_seg5])
              exact continuousAt_const.congr h_eq_nhds.symm
    exact h_deriv_fdPolygon_cont.comp continuous_fst.continuousOn
      (fun ⟨t, _s⟩ ⟨ht, _hs⟩ => ht)
  · obtain ⟨M, hM⟩ := fdPolygon_deriv_bounded
    exact ⟨M, fun t ht _s _hs => by
      rw [show (fun t' => H (t', _s)) =
        fun t' => fdPolygon t' - ((1 - ↑_s) * p₁ + ↑_s * p₂) from rfl,
        deriv_sub_const]
      exact hM t ht⟩

end RectHomotopyProof
