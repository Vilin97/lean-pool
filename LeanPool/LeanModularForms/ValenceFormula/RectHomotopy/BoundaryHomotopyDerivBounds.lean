/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import LeanPool.LeanModularForms.ValenceFormula.RectHomotopy.HomotopyDef

/-!
# Derivative norm bounds for the homotopy segments

Proves that the derivative norm of each segment of
`fdBoundaryToPolygonHomotopy` is bounded by 5.
-/

open Complex Set Metric Filter Topology

namespace RectHomotopyProof

/-- Derivative of an affine-angle complex exponential `t' ↦ exp((α + (t' - c)·β)·I)`. -/
private lemma hasDerivAt_arc_exp (α β c t : ℝ) :
    HasDerivAt (fun t' : ℝ => Complex.exp (((α : ℂ) + ((t' : ℂ) - c) * (β : ℂ)) * I))
      ((β : ℂ) * I * Complex.exp (((α : ℂ) + ((t : ℂ) - c) * (β : ℂ)) * I)) t := by
  have h_shift : HasDerivAt (fun t' : ℝ => (t' : ℂ) - c) 1 t := by
    have h := @ContinuousLinearMap.hasDerivAt ℝ _ ℂ _ _ t Complex.ofRealCLM
    simp only [Complex.ofRealCLM_apply] at h
    exact h.sub_const (c : ℂ)
  have h_inner : HasDerivAt (fun t' : ℝ => (α : ℂ) + ((t' : ℂ) - c) * (β : ℂ)) (β : ℂ) t := by
    have h_mul := h_shift.mul_const (β : ℂ)
    simp only [one_mul] at h_mul
    exact h_mul.const_add (α : ℂ)
  have h_times_I : HasDerivAt (fun t' : ℝ => ((α : ℂ) + ((t' : ℂ) - c) * (β : ℂ)) * I)
      ((β : ℂ) * I) t := h_inner.mul_const I
  have h := (Complex.hasDerivAt_exp (((α : ℂ) + ((t : ℂ) - c) * (β : ℂ)) * I)).comp t h_times_I
  simp only [mul_comm (Complex.exp _)] at h
  exact h

/-- Derivative of the chord segment `t' ↦ chordSegment a b (t' - c)` is `b - a`. -/
private lemma hasDerivAt_chordSegment_shift (a b : ℂ) (c t : ℝ) :
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
  exact (h1.add h2).congr_deriv (by ring)

/-- Norm bound for segment 2 derivative. -/
lemma norm_deriv_H_seg2_le (t s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    ‖deriv (fun t' : ℝ =>
      let arc_point :=
        Complex.exp ((Real.pi / 3 +
            (t' - 1) * (Real.pi / 2 -
                Real.pi / 3)) * I)
      let chord_point :=
        chordSegment rho' iPoint (t' - 1)
      (1 - s) • arc_point +
        s • chord_point) t‖ ≤ 5 := by
  have h1s : |1 - s| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [hs.1, hs.2]
  have hs' : |s| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [hs.1, hs.2]
  have hpi6 : Real.pi / 6 ≤ 1 := by
    have := Real.pi_le_four; linarith
  have hi_rho : ‖iPoint - rho'‖ ≤ 2 := by
    calc ‖iPoint - rho'‖
        ≤ ‖iPoint‖ + ‖rho'‖ :=
          norm_sub_le _ _
      _ = 1 + 1 := by
          rw [i_point_norm, rho'_norm]
      _ = 2 := by norm_num
  by_cases hd : DifferentiableAt ℝ (fun t' : ℝ =>
        let arc_point :=
          Complex.exp ((Real.pi / 3 +
              (t' - 1) * (Real.pi / 2 -
                  Real.pi / 3)) * I)
        let chord_point :=
          chordSegment rho' iPoint (t' - 1)
        (1 - s) • arc_point +
          s • chord_point) t
  · have h_bound : ‖deriv (fun t' : ℝ =>
        let arc_point :=
          Complex.exp ((Real.pi / 3 +
              (t' - 1) * (Real.pi / 2 -
                  Real.pi / 3)) * I)
        let chord_point :=
          chordSegment rho' iPoint (t' - 1)
        (1 - s) • arc_point +
          s • chord_point) t‖ ≤
        |1 - s| * 1 + |s| * 2 := by
      have hpi : (Real.pi / 2 - Real.pi / 3 : ℂ) =
            Real.pi / 6 := by
        ring
      have func_eq : (fun t' : ℝ =>
            let arc_point :=
              Complex.exp ((Real.pi / 3 +
                  (t' - 1) * (Real.pi / 2 -
                      Real.pi / 3)) * I)
            let chord_point :=
              chordSegment rho' iPoint (t' - 1)
            (1 - s) • arc_point +
              s • chord_point) =
          (fun t' : ℝ =>
            let arc_point :=
              Complex.exp ((Real.pi / 3 +
                  (t' - 1) * (Real.pi / 6)) * I)
            let chord_point :=
              chordSegment rho' iPoint (t' - 1)
            (1 - s) • arc_point +
              s • chord_point) := by
        ext t'; simp only [hpi]
      rw [func_eq]
      have h_arc : HasDerivAt (fun t' : ℝ =>
            Complex.exp (((Real.pi : ℝ) / 3 +
                (t' - 1) * ((Real.pi : ℝ) / 6)) * I))
          (((Real.pi : ℝ) / 6) * I *
            Complex.exp (((Real.pi : ℝ) / 3 +
                (t - 1) * ((Real.pi : ℝ) / 6)) *
                I))
          t := by
        have := hasDerivAt_arc_exp (Real.pi / 3) (Real.pi / 6) 1 t
        push_cast at this ⊢
        convert this using 2
      have h_chord : HasDerivAt (fun t' : ℝ =>
            chordSegment rho' iPoint (t' - 1))
          (iPoint - rho') t :=
        hasDerivAt_chordSegment_shift rho' iPoint 1 t
      have h_combined : HasDerivAt (fun t' : ℝ =>
            let arc_point :=
              Complex.exp ((Real.pi / 3 +
                  (t' - 1) * (Real.pi / 6)) * I)
            let chord_point :=
              chordSegment rho' iPoint (t' - 1)
            (1 - s) • arc_point +
              s • chord_point)
          ((1 - s) • (((Real.pi : ℝ) / 6) * I *
              Complex.exp (((Real.pi : ℝ) / 3 +
                  (t - 1) * ((Real.pi : ℝ) / 6)) *
                  I)) +
           s • (iPoint - rho')) t := by
        have h1 := h_arc.const_smul (1 - s)
        have h2 := h_chord.const_smul s
        exact h1.add h2
      rw [h_combined.deriv]
      calc ‖(1 - s) • (((Real.pi : ℝ) / 6) * I *
                Complex.exp (((Real.pi : ℝ) / 3 +
                    (t - 1) * ((Real.pi : ℝ) / 6)) *
                    I)) +
             s • (iPoint - rho')‖
          ≤ ‖(1 - s) • (((Real.pi : ℝ) / 6) * I *
                Complex.exp (((Real.pi : ℝ) / 3 +
                    (t - 1) * ((Real.pi : ℝ) / 6)) *
                    I))‖ +
            ‖s • (iPoint - rho')‖ :=
          norm_add_le _ _
        _ = |1 - s| *
              ‖((Real.pi : ℝ) / 6) * I *
                Complex.exp (((Real.pi : ℝ) / 3 +
                    (t - 1) * ((Real.pi : ℝ) / 6)) *
                    I)‖ +
            |s| * ‖iPoint - rho'‖ := by
          rw [norm_smul, norm_smul,
            Real.norm_eq_abs,
            Real.norm_eq_abs]
        _ = |1 - s| * ((Real.pi / 6) *
                ‖Complex.exp (((Real.pi : ℝ) / 3 +
                    (t - 1) * ((Real.pi : ℝ) / 6)) *
                    I)‖) +
            |s| * ‖iPoint - rho'‖ := by
              congr 1
              rw [mul_assoc, norm_mul,
                norm_mul]
              have hpi_norm :
                  ‖(Real.pi : ℂ) / 6‖ =
                    Real.pi / 6 := by
                have h1 :
                    ‖(Real.pi : ℂ)‖ =
                      Real.pi := by
                  rw [Complex.norm_real]
                  exact abs_of_pos
                    Real.pi_pos
                have h2 :
                    ‖(6 : ℂ)‖ = 6 := by
                  norm_num
                rw [norm_div, h1, h2]
              rw [hpi_norm,
                Complex.norm_I, one_mul]
        _ = |1 - s| * ((Real.pi / 6) * 1) +
            |s| * ‖iPoint - rho'‖ := by
              congr 2
              have : ((Real.pi : ℝ) / 3 +
                    (t - 1) * ((Real.pi : ℝ) / 6)) *
                    I =
                  ((Real.pi / 3 + (t - 1) *
                      (Real.pi / 6)) : ℝ) *
                    I := by
                push_cast; ring
              rw [this,
                Complex.norm_exp_ofReal_mul_I]
        _ = |1 - s| * Real.pi / 6 +
            |s| * ‖iPoint - rho'‖ := by
          ring
        _ ≤ |1 - s| * 1 + |s| * 2 := by
            have h1 :
                |1 - s| * Real.pi / 6 ≤
                  |1 - s| * 1 := by
              have hpos : (0 : ℝ) ≤ |1 - s| :=
                abs_nonneg _
              calc |1 - s| * Real.pi / 6 = |1 - s| *
                        (Real.pi / 6) := by
                      ring
                  _ ≤ |1 - s| * 1 :=
                    mul_le_mul_of_nonneg_left
                      hpi6 hpos
            have h2 :
                |s| * ‖iPoint - rho'‖ ≤
                  |s| * 2 :=
              mul_le_mul_of_nonneg_left
                hi_rho (abs_nonneg _)
            linarith
    calc ‖deriv (fun t' : ℝ =>
          let arc_point :=
            Complex.exp ((Real.pi / 3 +
                (t' - 1) * (Real.pi / 2 -
                    Real.pi / 3)) * I)
          let chord_point :=
            chordSegment rho' iPoint (t' - 1)
          (1 - s) • arc_point +
            s • chord_point) t‖
        ≤ |1 - s| * 1 + |s| * 2 :=
          h_bound
      _ ≤ 1 * 1 + 1 * 2 := by
          nlinarith [h1s, hs']
      _ = 3 := by norm_num
      _ ≤ 5 := by norm_num
  · simp only [
      deriv_zero_of_not_differentiableAt hd,
      norm_zero]
    norm_num

/-- Norm bound for segment 3 derivative. -/
lemma norm_deriv_H_seg3_le (t s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    ‖deriv (fun t' : ℝ =>
      let arc_point :=
        Complex.exp ((Real.pi / 2 +
            (t' - 2) * (2 * Real.pi / 3 -
                Real.pi / 2)) * I)
      let chord_point :=
        chordSegment iPoint rho (t' - 2)
      (1 - s) • arc_point +
        s • chord_point) t‖ ≤ 5 := by
  have h1s : |1 - s| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [hs.1, hs.2]
  have hs' : |s| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [hs.1, hs.2]
  have hpi6 : Real.pi / 6 ≤ 1 := by
    have := Real.pi_le_four; linarith
  have hrho_i : ‖rho - iPoint‖ ≤ 2 := by
    calc ‖rho - iPoint‖
        ≤ ‖rho‖ + ‖iPoint‖ :=
          norm_sub_le _ _
      _ = 1 + 1 := by
          rw [rho_norm, i_point_norm]
      _ = 2 := by norm_num
  by_cases hd : DifferentiableAt ℝ (fun t' : ℝ =>
        let arc_point :=
          Complex.exp ((Real.pi / 2 +
              (t' - 2) * (2 * Real.pi / 3 -
                  Real.pi / 2)) * I)
        let chord_point :=
          chordSegment iPoint rho (t' - 2)
        (1 - s) • arc_point +
          s • chord_point) t
  · have h_bound : ‖deriv (fun t' : ℝ =>
        let arc_point :=
          Complex.exp ((Real.pi / 2 +
              (t' - 2) * (2 * Real.pi / 3 -
                  Real.pi / 2)) * I)
        let chord_point :=
          chordSegment iPoint rho (t' - 2)
        (1 - s) • arc_point +
          s • chord_point) t‖ ≤
        |1 - s| * 1 + |s| * 2 := by
      have hpi : (2 * Real.pi / 3 -
            Real.pi / 2 : ℂ) =
            Real.pi / 6 := by
        ring
      have func_eq : (fun t' : ℝ =>
            let arc_point :=
              Complex.exp ((Real.pi / 2 +
                  (t' - 2) * (2 * Real.pi / 3 -
                      Real.pi / 2)) * I)
            let chord_point :=
              chordSegment iPoint rho (t' - 2)
            (1 - s) • arc_point +
              s • chord_point) =
          (fun t' : ℝ =>
            let arc_point :=
              Complex.exp ((Real.pi / 2 +
                  (t' - 2) * (Real.pi / 6)) * I)
            let chord_point :=
              chordSegment iPoint rho (t' - 2)
            (1 - s) • arc_point +
              s • chord_point) := by
        ext t'; simp only [hpi]
      rw [func_eq]
      have h_arc : HasDerivAt (fun t' : ℝ =>
            Complex.exp (((Real.pi : ℝ) / 2 +
                (t' - 2) * ((Real.pi : ℝ) / 6)) *
                I))
          (((Real.pi : ℝ) / 6) * I *
            Complex.exp (((Real.pi : ℝ) / 2 +
                (t - 2) * ((Real.pi : ℝ) / 6)) *
                I))
          t := by
        have := hasDerivAt_arc_exp (Real.pi / 2) (Real.pi / 6) 2 t
        push_cast at this ⊢
        convert this using 2
      have h_chord : HasDerivAt (fun t' : ℝ =>
            chordSegment iPoint rho (t' - 2))
          (rho - iPoint) t :=
        hasDerivAt_chordSegment_shift iPoint rho 2 t
      have h_combined : HasDerivAt (fun t' : ℝ =>
            let arc_point :=
              Complex.exp ((Real.pi / 2 +
                  (t' - 2) * (Real.pi / 6)) * I)
            let chord_point :=
              chordSegment iPoint rho (t' - 2)
            (1 - s) • arc_point +
              s • chord_point)
          ((1 - s) • (((Real.pi : ℝ) / 6) * I *
              Complex.exp (((Real.pi : ℝ) / 2 +
                  (t - 2) * ((Real.pi : ℝ) / 6)) *
                  I)) +
           s • (rho - iPoint)) t := by
        have h1 := h_arc.const_smul (1 - s)
        have h2 := h_chord.const_smul s
        exact h1.add h2
      rw [h_combined.deriv]
      calc ‖(1 - s) • (((Real.pi : ℝ) / 6) * I *
                Complex.exp (((Real.pi : ℝ) / 2 +
                    (t - 2) * ((Real.pi : ℝ) / 6)) *
                    I)) +
             s • (rho - iPoint)‖
          ≤ ‖(1 - s) • (((Real.pi : ℝ) / 6) * I *
                Complex.exp (((Real.pi : ℝ) / 2 +
                    (t - 2) * ((Real.pi : ℝ) / 6)) *
                    I))‖ +
            ‖s • (rho - iPoint)‖ :=
          norm_add_le _ _
        _ = |1 - s| *
              ‖((Real.pi : ℝ) / 6) * I *
                Complex.exp (((Real.pi : ℝ) / 2 +
                    (t - 2) * ((Real.pi : ℝ) / 6)) *
                    I)‖ +
            |s| * ‖rho - iPoint‖ := by
          rw [norm_smul, norm_smul,
            Real.norm_eq_abs,
            Real.norm_eq_abs]
        _ = |1 - s| * ((Real.pi / 6) *
                ‖Complex.exp (((Real.pi : ℝ) / 2 +
                    (t - 2) * ((Real.pi : ℝ) / 6)) *
                    I)‖) +
            |s| * ‖rho - iPoint‖ := by
              congr 1
              rw [mul_assoc, norm_mul,
                norm_mul]
              have hpi_norm :
                  ‖(Real.pi : ℂ) / 6‖ =
                    Real.pi / 6 := by
                have h1 :
                    ‖(Real.pi : ℂ)‖ =
                      Real.pi := by
                  rw [Complex.norm_real]
                  exact abs_of_pos
                    Real.pi_pos
                have h2 :
                    ‖(6 : ℂ)‖ = 6 := by
                  norm_num
                rw [norm_div, h1, h2]
              rw [hpi_norm,
                Complex.norm_I, one_mul]
        _ = |1 - s| * ((Real.pi / 6) * 1) +
            |s| * ‖rho - iPoint‖ := by
              congr 2
              have : ((Real.pi : ℝ) / 2 +
                    (t - 2) * ((Real.pi : ℝ) / 6)) *
                    I =
                  ((Real.pi / 2 + (t - 2) *
                      (Real.pi / 6)) : ℝ) *
                    I := by
                push_cast; ring
              rw [this,
                Complex.norm_exp_ofReal_mul_I]
        _ = |1 - s| * Real.pi / 6 +
            |s| * ‖rho - iPoint‖ := by
          ring
        _ ≤ |1 - s| * 1 + |s| * 2 := by
            have h1 :
                |1 - s| * Real.pi / 6 ≤
                  |1 - s| * 1 := by
              have hpos : (0 : ℝ) ≤ |1 - s| :=
                abs_nonneg _
              calc |1 - s| * Real.pi / 6 = |1 - s| *
                        (Real.pi / 6) := by
                      ring
                  _ ≤ |1 - s| * 1 :=
                    mul_le_mul_of_nonneg_left
                      hpi6 hpos
            have h2 :
                |s| * ‖rho - iPoint‖ ≤
                  |s| * 2 :=
              mul_le_mul_of_nonneg_left
                hrho_i (abs_nonneg _)
            linarith
    calc ‖deriv (fun t' : ℝ =>
          let arc_point :=
            Complex.exp ((Real.pi / 2 +
                (t' - 2) * (2 * Real.pi / 3 -
                    Real.pi / 2)) * I)
          let chord_point :=
            chordSegment iPoint rho (t' - 2)
          (1 - s) • arc_point +
            s • chord_point) t‖
        ≤ |1 - s| * 1 + |s| * 2 :=
          h_bound
      _ ≤ 1 * 1 + 1 * 2 := by
          nlinarith [h1s, hs']
      _ = 3 := by norm_num
      _ ≤ 5 := by norm_num
  · simp only [
      deriv_zero_of_not_differentiableAt hd,
      norm_zero]
    norm_num

/-- Segment 2 derivative bound for t in (1,2). -/
lemma fdBoundaryToPolygonHomotopy_seg2_deriv_bound (t : ℝ) (_ht : t ∈ Ioo 1 2)
    (s : ℝ) (hs : s ∈ Icc 0 1) :
    ‖deriv (fun t' : ℝ =>
      let arc_point :=
        Complex.exp ((Real.pi / 3 +
            (t' - 1) * (Real.pi / 2 -
                Real.pi / 3)) * I)
      let chord_point :=
        chordSegment rho' iPoint (t' - 1)
      (1 - s) • arc_point +
        s • chord_point) t‖ ≤ 5 :=
  norm_deriv_H_seg2_le t s hs

/-- Segment 3 derivative bound for t in (2,3). -/
lemma fdBoundaryToPolygonHomotopy_seg3_deriv_bound (t : ℝ) (_ht : t ∈ Ioo 2 3)
    (s : ℝ) (hs : s ∈ Icc 0 1) :
    ‖deriv (fun t' : ℝ =>
      let arc_point :=
        Complex.exp ((Real.pi / 2 +
            (t' - 2) * (2 * Real.pi / 3 -
                Real.pi / 2)) * I)
      let chord_point :=
        chordSegment iPoint rho (t' - 2)
      (1 - s) • arc_point +
        s • chord_point) t‖ ≤ 5 :=
  norm_deriv_H_seg3_le t s hs

/-- Segment 1 derivative bound. -/
lemma norm_deriv_H_seg1_le (t : ℝ) (_s : ℝ) :
    ‖deriv (fun t' : ℝ => (1/2 : ℂ) +
        (HHeight - (↑t' : ℂ) * (HHeight - Real.sqrt 3 / 2)) *
          I) t‖ ≤ 5 := by
  have h_height : (HHeight : ℂ) - Real.sqrt 3 / 2 =
        1 := by
    simp only [HHeight]
    push_cast
    ring
  have h_deriv : HasDerivAt (fun t' : ℝ =>
        (1/2 : ℂ) + ((HHeight : ℂ) - (↑t' : ℂ) *
            ((HHeight : ℂ) -
              Real.sqrt 3 / 2)) * I)
      (-((HHeight : ℂ) -
        Real.sqrt 3 / 2) * I) t := by
    have h1 :
        HasDerivAt (fun t' : ℝ => (↑t' : ℂ))
          1 t :=
      Complex.ofRealCLM.hasDerivAt
    have h2 : HasDerivAt (fun t' : ℝ =>
          (↑t' : ℂ) * ((HHeight : ℂ) -
              Real.sqrt 3 / 2))
        ((HHeight : ℂ) -
          Real.sqrt 3 / 2) t := by
      have :=
        h1.mul_const ((HHeight : ℂ) -
            Real.sqrt 3 / 2)
      simp only [one_mul] at this
      exact this
    have h3 : HasDerivAt (fun t' : ℝ =>
          (HHeight : ℂ) - (↑t' : ℂ) * ((HHeight : ℂ) -
              Real.sqrt 3 / 2))
        (-((HHeight : ℂ) -
          Real.sqrt 3 / 2)) t := by
      have := (hasDerivAt_const t
          (HHeight : ℂ)).sub h2
      simp only [zero_sub] at this
      exact this
    have h4 : HasDerivAt (fun t' : ℝ =>
          ((HHeight : ℂ) - (↑t' : ℂ) * ((HHeight : ℂ) -
              Real.sqrt 3 / 2)) * I)
        (-((HHeight : ℂ) -
          Real.sqrt 3 / 2) * I) t :=
      h3.mul_const I
    have := (hasDerivAt_const t ((1/2 : ℂ))).add
        h4
    simp only [zero_add] at this
    exact this
  rw [h_deriv.deriv, h_height]
  simp only [neg_one_mul, norm_neg,
    Complex.norm_I]
  norm_num

/-- Segment 4 derivative bound. -/
lemma norm_deriv_H_seg4_le (t : ℝ) (_s : ℝ) :
    ‖deriv (fun t' : ℝ => (-1/2 : ℂ) +
        ((Real.sqrt 3 / 2 : ℂ) + ((↑t' : ℂ) - 3) *
            ((HHeight : ℂ) -
              Real.sqrt 3 / 2)) * I)
      t‖ ≤ 5 := by
  have h_height : (HHeight : ℂ) - Real.sqrt 3 / 2 =
        1 := by
    simp only [HHeight]
    push_cast
    ring
  have h_deriv : HasDerivAt (fun t' : ℝ =>
        (-1/2 : ℂ) + ((Real.sqrt 3 / 2 : ℂ) +
            ((↑t' : ℂ) - 3) * ((HHeight : ℂ) -
                Real.sqrt 3 / 2)) * I)
      (((HHeight : ℂ) -
        Real.sqrt 3 / 2) * I) t := by
    have h1 :
        HasDerivAt (fun t' : ℝ => (↑t' : ℂ))
          1 t :=
      Complex.ofRealCLM.hasDerivAt
    have h2 :
        HasDerivAt (fun t' : ℝ => (↑t' : ℂ) - 3)
          1 t :=
      h1.sub_const 3
    have h3 : HasDerivAt (fun t' : ℝ =>
          ((↑t' : ℂ) - 3) * ((HHeight : ℂ) -
              Real.sqrt 3 / 2))
        ((HHeight : ℂ) -
          Real.sqrt 3 / 2) t := by
      have :=
        h2.mul_const ((HHeight : ℂ) -
            Real.sqrt 3 / 2)
      simp only [one_mul] at this
      exact this
    have h4 : HasDerivAt (fun t' : ℝ =>
          (Real.sqrt 3 / 2 : ℂ) + ((↑t' : ℂ) - 3) *
              ((HHeight : ℂ) -
                Real.sqrt 3 / 2))
        ((HHeight : ℂ) -
          Real.sqrt 3 / 2) t := by
      have := (hasDerivAt_const t
          (Real.sqrt 3 / 2 : ℂ)).add h3
      simp only [zero_add] at this
      exact this
    have h5 : HasDerivAt (fun t' : ℝ =>
          ((Real.sqrt 3 / 2 : ℂ) + ((↑t' : ℂ) - 3) *
              ((HHeight : ℂ) -
                Real.sqrt 3 / 2)) * I)
        (((HHeight : ℂ) -
          Real.sqrt 3 / 2) * I) t :=
      h4.mul_const I
    have := (hasDerivAt_const t ((-1/2 : ℂ))).add
        h5
    simp only [zero_add] at this
    exact this
  rw [h_deriv.deriv, h_height]
  simp only [one_mul, Complex.norm_I]
  norm_num

/-- Segment 5 derivative bound. -/
lemma norm_deriv_H_seg5_le (t : ℝ) (_s : ℝ) :
    ‖deriv (fun t' : ℝ => ((↑t' : ℂ) - 9/2) +
        (HHeight : ℂ) * I) t‖ ≤ 5 := by
  have h_deriv : HasDerivAt (fun t' : ℝ =>
        ((↑t' : ℂ) - 9/2) + (HHeight : ℂ) * I) 1 t := by
    have h1 :
        HasDerivAt (fun t' : ℝ => (↑t' : ℂ))
          1 t :=
      Complex.ofRealCLM.hasDerivAt
    have h2 :
        HasDerivAt (fun t' : ℝ =>
            (↑t' : ℂ) - 9/2) 1 t :=
      h1.sub_const (9/2)
    have := h2.add_const ((HHeight : ℂ) * I)
    convert this using 1
  rw [h_deriv.deriv]
  norm_num

end RectHomotopyProof
