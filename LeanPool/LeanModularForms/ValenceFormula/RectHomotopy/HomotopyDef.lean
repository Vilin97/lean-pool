/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import LeanPool.LeanModularForms.ValenceFormula.RectHomotopy.Geometry
import LeanPool.LeanModularForms.ValenceFormula.TrigLemmas

/-!
# Homotopy infrastructure for FD boundary → polygon deformation

Defines the segment helper functions `HSeg1`..`HSeg5`, proves their
continuity and matching at breakpoints, and establishes the main results:

* `fdBoundaryToPolygonHomotopy_continuous`
* `fdBoundaryToPolygonHomotopy_avoids`
* `fdBoundaryToPolygonHomotopy_closed`
* `fdBoundaryToPolygon_homotopy_avoids_interior`
* `circleAround` and `polygonToCircleHomotopy`
-/

open Complex Set Metric Filter

/-- Work around mathlib 4.29-rc8 instance synthesis issue: `NormedSpace.toNormSMulClass` fails
to unify for `ℝ ℂ` during typeclass resolution, breaking `NormSMulClass`, `IsBoundedSMul`,
and `ContinuousSMul` for `ℝ ℂ`. We provide all three instances explicitly. -/
private noncomputable instance instNormSMulClassRealComplex : NormSMulClass ℝ ℂ :=
  @NormedSpace.toNormSMulClass ℝ ℂ _ _ _

private noncomputable instance instIsBoundedSMulRealComplex : IsBoundedSMul ℝ ℂ :=
  NormSMulClass.toIsBoundedSMul

private noncomputable instance instContinuousSMulRealComplex : ContinuousSMul ℝ ℂ :=
  IsBoundedSMul.continuousSMul

namespace RectHomotopyProof

/-- The homotopy on the first segment of the fundamental-domain boundary. -/
noncomputable def HSeg1 (p : ℝ × ℝ) : ℂ :=
  1/2 + (HHeight - p.1 * (HHeight - Real.sqrt 3 / 2)) * I

/-- The homotopy on the second segment, interpolating an arc and its chord. -/
noncomputable def HSeg2 (p : ℝ × ℝ) : ℂ :=
  let arc_point :=
    Complex.exp ((Real.pi / 3 + (p.1 - 1) * (Real.pi / 2 - Real.pi / 3)) * I)
  let chord_point := chordSegment rho' iPoint (p.1 - 1)
  (1 - p.2) • arc_point + p.2 • chord_point

/-- The homotopy on the third segment, interpolating an arc and its chord. -/
noncomputable def HSeg3 (p : ℝ × ℝ) : ℂ :=
  let arc_point :=
    Complex.exp ((Real.pi / 2 + (p.1 - 2) * (2 * Real.pi / 3 - Real.pi / 2)) * I)
  let chord_point := chordSegment iPoint rho (p.1 - 2)
  (1 - p.2) • arc_point + p.2 • chord_point

/-- The homotopy on the fourth segment of the fundamental-domain boundary. -/
noncomputable def HSeg4 (p : ℝ × ℝ) : ℂ :=
  -1/2 + (Real.sqrt 3 / 2 + (p.1 - 3) * (HHeight - Real.sqrt 3 / 2)) * I

/-- The homotopy on the fifth segment of the fundamental-domain boundary. -/
noncomputable def HSeg5 (p : ℝ × ℝ) : ℂ := (p.1 - 9/2) + HHeight * I

lemma H_seg1_continuous : Continuous HSeg1 := by unfold HSeg1; continuity

lemma H_seg2_continuous : Continuous HSeg2 := by unfold HSeg2 chordSegment; continuity

lemma H_seg3_continuous : Continuous HSeg3 := by unfold HSeg3 chordSegment; continuity

lemma H_seg4_continuous : Continuous HSeg4 := by unfold HSeg4; continuity

lemma H_seg5_continuous : Continuous HSeg5 := by unfold HSeg5; continuity

/-- Derivative of an affine-angle complex exponential `t' ↦ exp((α + (t' - c)·β)·I)`. -/
lemma hasDerivAt_arc_exp (α β c t : ℝ) :
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
lemma hasDerivAt_chordSegment_shift (a b : ℂ) (c t : ℝ) :
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
  rw [show b - a = -a + b from by ring]
  exact h1.add h2

lemma exp_pi_div_three_eq_rho' :
    Complex.exp (↑(Real.pi / 3) * I) = rho' := by
  rw [exp_real_angle_I, Real.cos_pi_div_three,
    Real.sin_pi_div_three]
  simp only [rho', Complex.ofReal_div,
    Complex.ofReal_one, Complex.ofReal_ofNat]

lemma exp_pi_div_two_eq_I :
    Complex.exp (↑(Real.pi / 2) * I) = I := by
  rw [exp_real_angle_I, Real.cos_pi_div_two,
    Real.sin_pi_div_two]
  simp only [Complex.ofReal_zero, Complex.ofReal_one,
    zero_add, one_mul]

lemma exp_two_pi_div_three_eq_rho :
    Complex.exp (↑(2 * Real.pi / 3) * I) = rho := by
  rw [exp_real_angle_I, cos_two_pi_div_three,
    sin_two_pi_div_three]
  simp only [rho, Complex.ofReal_neg, Complex.ofReal_div,
    Complex.ofReal_one, Complex.ofReal_ofNat]

lemma H_match_at_t1 (p : ℝ × ℝ) (hp : p.1 = 1) :
    HSeg1 p = HSeg2 p := by
  obtain ⟨t, s⟩ := p
  simp only at hp; subst hp
  simp only [HSeg1, HSeg2, chordSegment, HHeight,
    rho', iPoint]
  have hLHS : (↑(Real.sqrt 3 / 2 + 1) - ↑(1 : ℝ) *
        (↑(Real.sqrt 3 / 2 + 1) -
          ↑(Real.sqrt 3) / 2) : ℂ) =
        ↑(Real.sqrt 3) / 2 := by push_cast; ring
  simp only [hLHS]
  have hangle : (↑Real.pi / 3 + (↑(1 : ℝ) - 1) *
        (↑Real.pi / 2 - ↑Real.pi / 3) : ℂ) =
        ↑Real.pi / 3 := by
    simp only [Complex.ofReal_one, sub_self,
      zero_mul, add_zero]
  simp only [hangle]
  have hpi3 : (↑Real.pi / 3 : ℂ) = ↑(Real.pi / 3) := by push_cast; ring
  rw [hpi3, exp_pi_div_three_eq_rho']
  simp only [sub_self, rho']
  simp only [Complex.real_smul,
    Complex.ofReal_sub, Complex.ofReal_one,
    sub_zero, one_mul]
  push_cast; ring

lemma H_match_at_t2 (p : ℝ × ℝ) (hp : p.1 = 2) :
    HSeg2 p = HSeg3 p := by
  obtain ⟨t, s⟩ := p
  simp only at hp; subst hp
  unfold HSeg2 HSeg3 chordSegment rho' iPoint rho
  simp only [Complex.ofReal_ofNat]
  norm_num

lemma H_match_at_t3 (p : ℝ × ℝ) (hp : p.1 = 3) :
    HSeg3 p = HSeg4 p := by
  obtain ⟨t, s⟩ := p
  simp only at hp; subst hp
  unfold HSeg3 HSeg4 chordSegment iPoint rho HHeight
  simp only [Complex.ofReal_ofNat]
  norm_num
  have hexp :
      Complex.exp (2 * ↑Real.pi / 3 * I) =
        -1/2 + ↑(Real.sqrt 3) / 2 * I := by
    have h : (2 * ↑Real.pi / 3 * I : ℂ) =
        ↑(2 * Real.pi / 3) * I := by push_cast; ring
    rw [h, exp_two_pi_div_three_eq_rho, rho]
  simp only [hexp]; ring

lemma H_match_at_t4 (p : ℝ × ℝ) (hp : p.1 = 4) :
    HSeg4 p = HSeg5 p := by
  obtain ⟨t, s⟩ := p
  simp only at hp; subst hp
  simp only [HSeg4, HSeg5, HHeight]
  ring_nf
  simp only [Complex.ofReal_add, Complex.ofReal_ofNat]
  ring

lemma fdBoundaryToPolygonHomotopy_continuous :
    Continuous fdBoundaryToPolygonHomotopy := by
  have h45 : Continuous (fun p =>
      if p.1 ≤ 4 then HSeg4 p else HSeg5 p) :=
    Continuous.if_le H_seg4_continuous H_seg5_continuous continuous_fst continuous_const
      H_match_at_t4
  have h345 : Continuous (fun p =>
      if p.1 ≤ 3 then HSeg3 p else if p.1 ≤ 4 then HSeg4 p else HSeg5 p) := by
    apply Continuous.if_le H_seg3_continuous h45 continuous_fst continuous_const
    intro p hp
    simp only [show p.1 ≤ 4 from le_trans (le_of_eq hp) (by norm_num : (3 : ℝ) ≤ 4), if_true]
    exact H_match_at_t3 p hp
  have h2345 : Continuous (fun p =>
      if p.1 ≤ 2 then HSeg2 p else if p.1 ≤ 3 then HSeg3 p
      else if p.1 ≤ 4 then HSeg4 p else HSeg5 p) := by
    apply Continuous.if_le H_seg2_continuous h345 continuous_fst continuous_const
    intro p hp
    simp only [show p.1 ≤ 3 from le_trans (le_of_eq hp) (by norm_num : (2 : ℝ) ≤ 3), if_true]
    exact H_match_at_t2 p hp
  have h12345 : Continuous (fun p =>
      if p.1 ≤ 1 then HSeg1 p else if p.1 ≤ 2 then HSeg2 p else if p.1 ≤ 3 then HSeg3 p
      else if p.1 ≤ 4 then HSeg4 p else HSeg5 p) := by
    apply Continuous.if_le H_seg1_continuous h2345 continuous_fst continuous_const
    intro p hp
    simp only [show p.1 ≤ 2 from le_trans (le_of_eq hp) (by norm_num : (1 : ℝ) ≤ 2), if_true]
    exact H_match_at_t1 p hp
  exact h12345

lemma fdBoundaryToPolygonHomotopy_at_zero (t : ℝ) (_ht : t ∈ Icc 0 5) :
    fdBoundaryToPolygonHomotopy (t, 0) = fdBoundary t := by
  simp only [fdBoundaryToPolygonHomotopy, fdBoundary]
  split_ifs with h1 h2 h3 h4
  · rfl
  · simp
  · simp
  · rfl
  · rfl

lemma fdBoundaryToPolygonHomotopy_at_one (t : ℝ) (_ht : t ∈ Icc 0 5) :
    fdBoundaryToPolygonHomotopy (t, 1) = fdPolygon t := by
  simp only [fdBoundaryToPolygonHomotopy, fdPolygon]
  split_ifs with h1 h2 h3 h4
  · rfl
  · simp
  · simp
  · rfl
  · rfl

lemma fdBoundaryToPolygonHomotopy_avoids (p : ℂ) (hp_norm : ‖p‖ > 1) (hp_re : |p.re| < 1 / 2)
    (hp_im : p.im < HHeight) (t : ℝ) (_ht : t ∈ Icc 0 5) (s : ℝ)
    (hs : s ∈ Icc 0 1) :
    fdBoundaryToPolygonHomotopy (t, s) ≠ p := by
  simp only [fdBoundaryToPolygonHomotopy]
  split_ifs with h1 h2 h3 h4
  · intro heq
    have hre : (1/2 + (↑HHeight - ↑t *
          (↑HHeight - ↑(Real.sqrt 3) / 2)) *
            I : ℂ).re = 1/2 := by
      simp only [Complex.add_re, Complex.ofReal_re,
        Complex.mul_re, Complex.I_re, mul_zero,
        Complex.I_im, mul_one, Complex.sub_re,
        Complex.div_ofNat_re, Complex.sub_im,
        Complex.ofReal_im, Complex.div_ofNat_im,
        Complex.mul_im]
      norm_num
    rw [heq] at hre
    have : |p.re| = 1/2 := by rw [hre]; norm_num
    linarith
  · have ht2 : t - 1 ∈ Icc 0 1 := by constructor <;> linarith [h1, h2]
    have h_arc_in := segment2_arc_in_closed_unit_ball t
    have h_chord_in := chord1_in_closed_unit_ball (t - 1) ht2
    have h_in_ball : (1 - s) • Complex.exp
          ((Real.pi / 3 + (t - 1) * (Real.pi / 2 - Real.pi / 3)) * I) +
          s • chordSegment rho' iPoint (t - 1) ∈
            closedBall (0 : ℂ) 1 :=
      chordSegment_in_convex convex_closedBall_zero_one
        h_arc_in h_chord_in s hs
    have hp_out := outside_closed_unit_ball p hp_norm
    exact fun h => hp_out (h ▸ h_in_ball)
  · have ht3 : t - 2 ∈ Icc 0 1 := by constructor <;> linarith [h2, h3]
    have h_arc_in := segment3_arc_in_closed_unit_ball t
    have h_chord_in := chord2_in_closed_unit_ball (t - 2) ht3
    have h_in_ball : (1 - s) • Complex.exp
          ((Real.pi / 2 + (t - 2) * (2 * Real.pi / 3 - Real.pi / 2)) * I) +
          s • chordSegment iPoint rho (t - 2) ∈
            closedBall (0 : ℂ) 1 :=
      chordSegment_in_convex convex_closedBall_zero_one
        h_arc_in h_chord_in s hs
    have hp_out := outside_closed_unit_ball p hp_norm
    exact fun h => hp_out (h ▸ h_in_ball)
  · intro heq
    have hre : ((-1/2 : ℂ) + (↑(Real.sqrt 3) / 2 +
          (↑t - 3) * (↑HHeight -
            ↑(Real.sqrt 3) / 2)) * I).re = -1/2 := by
      simp only [Complex.add_re, Complex.mul_re,
        Complex.I_re, mul_zero,
        Complex.I_im, mul_one, Complex.sub_re,
        Complex.div_ofNat_re,
        Complex.sub_im, Complex.ofReal_im,
        Complex.div_ofNat_im]
      norm_num
    rw [heq] at hre
    have : |p.re| = 1/2 := by rw [hre]; norm_num
    linarith
  · intro heq
    have him : (↑t - 9/2 + ↑HHeight * I : ℂ).im =
          HHeight := by
      simp only [Complex.add_im, Complex.sub_im,
        Complex.ofReal_im, Complex.div_ofNat_im,
        Complex.mul_im, Complex.ofReal_re, Complex.I_re,
        mul_zero, Complex.I_im, mul_one]
      simp only [show (9 : ℂ).im = 0 from rfl,
        add_zero, zero_div, sub_zero, zero_add]
    rw [heq] at him; linarith

lemma fdBoundaryToPolygonHomotopy_closed (s : ℝ) (_hs : s ∈ Icc 0 1) :
    fdBoundaryToPolygonHomotopy (0, s) =
      fdBoundaryToPolygonHomotopy (5, s) := by
  simp only [fdBoundaryToPolygonHomotopy, show (0 : ℝ) ≤ 1 from by norm_num, ↓reduceIte,
    show ¬(5 : ℝ) ≤ 1 from by norm_num, show ¬(5 : ℝ) ≤ 2 from by norm_num,
    show ¬(5 : ℝ) ≤ 3 from by norm_num, show ¬(5 : ℝ) ≤ 4 from by norm_num,
    HHeight, Complex.ofReal_zero, zero_mul, sub_zero]
  norm_cast; ring

/-- The counterclockwise circle of radius `ε` centred at `p`. -/
noncomputable def circleAround (p : ℂ) (ε : ℝ) :
    ℝ → ℂ := fun t =>
  p + ε * Complex.exp (2 * Real.pi * I * t / 5)

lemma circleAround_closed (p : ℂ) (ε : ℝ) :
    circleAround p ε 0 = circleAround p ε 5 := by
  simp only [circleAround, Complex.ofReal_zero, mul_zero, zero_div, Complex.ofReal_ofNat]
  congr 1
  rw [show 2 * Real.pi * I * (5 : ℂ) / 5 = 2 * Real.pi * I from by ring,
    Complex.exp_zero, Complex.exp_two_pi_mul_I]

lemma circleAround_continuous (p : ℂ) (ε : ℝ) :
    Continuous (circleAround p ε) := by unfold circleAround; continuity

lemma circleAround_dist (p : ℂ) (ε : ℝ) (hε : 0 ≤ ε) (t : ℝ) : ‖circleAround p ε t - p‖ = ε := by
  simp only [circleAround, add_sub_cancel_left]
  rw [Complex.norm_mul, show 2 * Real.pi * I * (t : ℂ) / 5 = ↑(2 * Real.pi * t / 5) * I from by
    push_cast; ring, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real]
  exact abs_of_nonneg hε

/-- The homotopy contracting the boundary polygon onto a small circle around `p`. -/
noncomputable def polygonToCircleHomotopy (p : ℂ) (ε : ℝ) : ℝ × ℝ → ℂ := fun (t, s) =>
  let z := fdPolygon t
  let dir := z - p
  p + (1 - s) * dir + s * ε * (dir / ‖dir‖)

lemma fdPolygon_avoids_interior (p : ℂ) (hp_norm : ‖p‖ > 1) (hp_re : |p.re| < 1 / 2)
    (hp_im : p.im < HHeight) (t : ℝ) (_ht : t ∈ Icc 0 5) :
    fdPolygon t ≠ p := by
  have h := fdBoundaryToPolygonHomotopy_avoids p hp_norm
    hp_re hp_im t _ht 1 ⟨zero_le_one, le_refl 1⟩
  simp only [fdBoundaryToPolygonHomotopy_at_one t _ht] at h
  exact h

theorem fdBoundaryToPolygon_homotopy_avoids_interior
    (p : ℂ) (hp_norm : ‖p‖ > 1) (hp_re : |p.re| < 1 / 2) (hp_im : p.im < HHeight) :
    ∀ t ∈ Icc 0 5, ∀ s ∈ Icc (0 : ℝ) 1,
      fdBoundaryToPolygonHomotopy (t, s) ≠ p :=
  fdBoundaryToPolygonHomotopy_avoids p hp_norm hp_re hp_im

theorem fdBoundaryToPolygon_homotopy_closed :
    ∀ s ∈ Icc (0 : ℝ) 1,
      fdBoundaryToPolygonHomotopy (0, s) =
        fdBoundaryToPolygonHomotopy (5, s) :=
  fdBoundaryToPolygonHomotopy_closed

theorem fdBoundaryToPolygon_homotopy_continuous :
    Continuous fdBoundaryToPolygonHomotopy :=
  fdBoundaryToPolygonHomotopy_continuous

theorem winding_number_one_summary (p : ℂ) (hp_norm : ‖p‖ > 1) (hp_re : |p.re| < 1 / 2)
    (hp_im : p.im < HHeight) : (∀ t ∈ Icc 0 5, ∀ s ∈ Icc (0 : ℝ) 1,
      fdBoundaryToPolygonHomotopy (t, s) ≠ p) ∧
    Continuous fdBoundaryToPolygonHomotopy ∧ (∀ s ∈ Icc (0 : ℝ) 1,
      fdBoundaryToPolygonHomotopy (0, s) = fdBoundaryToPolygonHomotopy (5, s)) :=
  ⟨fdBoundaryToPolygon_homotopy_avoids_interior p hp_norm hp_re hp_im,
   fdBoundaryToPolygon_homotopy_continuous, fdBoundaryToPolygon_homotopy_closed⟩

end RectHomotopyProof
