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

/-- Generic derivative-norm bound for an arc/chord homotopy segment with `β = π/6`.
    The arc is `exp((α + (t'-c)·(π/6))·I)` (norm-1 derivative `π/6 ≤ 1`) and the chord
    is `chordSegment a b (t'-c)` (derivative `b - a`, bounded by `2`). -/
private lemma norm_deriv_arc_chord_le (α c : ℝ) (a b : ℂ) (hab : ‖b - a‖ ≤ 2) (t s : ℝ)
    (hs : s ∈ Icc (0 : ℝ) 1) :
    ‖deriv (fun t' : ℝ =>
      (1 - s) • Complex.exp (((α : ℝ) + (t' - c) * (Real.pi / 6)) * I) +
        s • chordSegment a b (t' - c)) t‖ ≤ 5 := by
  have h1s : |1 - s| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hs.1, hs.2]
  have hs' : |s| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hs.1, hs.2]
  have hpi6 : Real.pi / 6 ≤ 1 := by have := Real.pi_le_four; linarith
  have h_arc : HasDerivAt (fun t' : ℝ => Complex.exp (((α : ℝ) + (t' - c) * (Real.pi / 6)) * I))
      (((Real.pi : ℝ) / 6) * I * Complex.exp (((α : ℝ) + (t - c) * (Real.pi / 6)) * I)) t := by
    have := hasDerivAt_arc_exp α (Real.pi / 6) c t
    push_cast at this ⊢
    convert this using 2
  have h_chord : HasDerivAt (fun t' : ℝ => chordSegment a b (t' - c)) (b - a) t :=
    hasDerivAt_chordSegment_shift a b c t
  have h_combined : HasDerivAt (fun t' : ℝ =>
      (1 - s) • Complex.exp (((α : ℝ) + (t' - c) * (Real.pi / 6)) * I) +
        s • chordSegment a b (t' - c))
      ((1 - s) • (((Real.pi : ℝ) / 6) * I *
          Complex.exp (((α : ℝ) + (t - c) * (Real.pi / 6)) * I)) + s • (b - a)) t :=
    (h_arc.const_smul (1 - s)).add (h_chord.const_smul s)
  rw [h_combined.deriv]
  have h_exp_norm : ‖Complex.exp (((α : ℝ) + (t - c) * (Real.pi / 6)) * I)‖ = 1 := by
    rw [show (((α : ℝ) + (t - c) * (Real.pi / 6)) * I) =
      (((α + (t - c) * (Real.pi / 6)) : ℝ) : ℂ) * I from by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I]
  have harc_norm : ‖((Real.pi : ℝ) / 6) * I *
      Complex.exp (((α : ℝ) + (t - c) * (Real.pi / 6)) * I)‖ = Real.pi / 6 := by
    rw [norm_mul, norm_mul, h_exp_norm, mul_one, Complex.norm_I, mul_one,
      show ((Real.pi : ℝ) / 6 : ℂ) = ((Real.pi / 6 : ℝ) : ℂ) from by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  calc ‖(1 - s) • (((Real.pi : ℝ) / 6) * I *
            Complex.exp (((α : ℝ) + (t - c) * (Real.pi / 6)) * I)) + s • (b - a)‖
      ≤ ‖(1 - s) • (((Real.pi : ℝ) / 6) * I *
            Complex.exp (((α : ℝ) + (t - c) * (Real.pi / 6)) * I))‖ + ‖s • (b - a)‖ :=
        norm_add_le _ _
    _ = |1 - s| * (Real.pi / 6) + |s| * ‖b - a‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, harc_norm]
    _ ≤ 1 * 1 + 1 * 2 := by
        have hb1 : |1 - s| * (Real.pi / 6) ≤ 1 * 1 := by nlinarith [abs_nonneg (1 - s)]
        have hb2 : |s| * ‖b - a‖ ≤ 1 * 2 :=
          mul_le_mul hs' hab (norm_nonneg _) (by norm_num)
        linarith
    _ ≤ 5 := by norm_num

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
  have hi_rho : ‖iPoint - rho'‖ ≤ 2 :=
    le_trans (norm_sub_le _ _) (by rw [i_point_norm, rho'_norm]; norm_num)
  have func_eq : (fun t' : ℝ =>
        let arc_point := Complex.exp ((Real.pi / 3 + (t' - 1) * (Real.pi / 2 - Real.pi / 3)) * I)
        let chord_point := chordSegment rho' iPoint (t' - 1)
        (1 - s) • arc_point + s • chord_point) =
      (fun t' : ℝ => (1 - s) • Complex.exp (((Real.pi / 3 : ℝ) + (t' - 1) * (Real.pi / 6)) * I) +
        s • chordSegment rho' iPoint (t' - 1)) := by
    ext t'
    simp only [show (Real.pi / 2 - Real.pi / 3 : ℂ) = Real.pi / 6 from by ring]
    norm_num
  rw [func_eq]
  exact norm_deriv_arc_chord_le (Real.pi / 3) 1 rho' iPoint hi_rho t s hs

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
  have hrho_i : ‖rho - iPoint‖ ≤ 2 :=
    le_trans (norm_sub_le _ _) (by rw [rho_norm, i_point_norm]; norm_num)
  have func_eq : (fun t' : ℝ =>
        let arc_point :=
          Complex.exp ((Real.pi / 2 + (t' - 2) * (2 * Real.pi / 3 - Real.pi / 2)) * I)
        let chord_point := chordSegment iPoint rho (t' - 2)
        (1 - s) • arc_point + s • chord_point) =
      (fun t' : ℝ => (1 - s) • Complex.exp (((Real.pi / 2 : ℝ) + (t' - 2) * (Real.pi / 6)) * I) +
        s • chordSegment iPoint rho (t' - 2)) := by
    ext t'
    simp only [show (2 * Real.pi / 3 - Real.pi / 2 : ℂ) = Real.pi / 6 from by ring]
    norm_num
  rw [func_eq]
  exact norm_deriv_arc_chord_le (Real.pi / 2) 2 iPoint rho hrho_i t s hs

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

private lemma HHeight_sub_sqrt3_div2 : (HHeight : ℂ) - Real.sqrt 3 / 2 = 1 := by
  simp only [HHeight]; push_cast; ring

/-- Segment 1 derivative bound. -/
lemma norm_deriv_H_seg1_le (t : ℝ) (_s : ℝ) :
    ‖deriv (fun t' : ℝ => (1/2 : ℂ) +
        (HHeight - (↑t' : ℂ) * (HHeight - Real.sqrt 3 / 2)) *
          I) t‖ ≤ 5 := by
  have h_deriv : HasDerivAt (fun t' : ℝ =>
        (1/2 : ℂ) + ((HHeight : ℂ) - (↑t' : ℂ) *
            ((HHeight : ℂ) - Real.sqrt 3 / 2)) * I)
      (-((HHeight : ℂ) - Real.sqrt 3 / 2) * I) t := by
    have h2 : HasDerivAt (fun t' : ℝ =>
          (↑t' : ℂ) * ((HHeight : ℂ) - Real.sqrt 3 / 2))
        ((HHeight : ℂ) - Real.sqrt 3 / 2) t := by
      simpa using Complex.ofRealCLM.hasDerivAt.mul_const ((HHeight : ℂ) - Real.sqrt 3 / 2)
    have h4 := (((hasDerivAt_const t (HHeight : ℂ)).sub h2).mul_const I)
    have := (hasDerivAt_const t ((1/2 : ℂ))).add h4
    simp only [zero_add, zero_sub] at this; exact this
  rw [h_deriv.deriv, HHeight_sub_sqrt3_div2]
  simp only [neg_one_mul, norm_neg, Complex.norm_I]; norm_num

/-- Segment 4 derivative bound. -/
lemma norm_deriv_H_seg4_le (t : ℝ) (_s : ℝ) :
    ‖deriv (fun t' : ℝ => (-1/2 : ℂ) +
        ((Real.sqrt 3 / 2 : ℂ) + ((↑t' : ℂ) - 3) *
            ((HHeight : ℂ) - Real.sqrt 3 / 2)) * I) t‖ ≤ 5 := by
  have h_deriv : HasDerivAt (fun t' : ℝ =>
        (-1/2 : ℂ) + ((Real.sqrt 3 / 2 : ℂ) +
            ((↑t' : ℂ) - 3) * ((HHeight : ℂ) - Real.sqrt 3 / 2)) * I)
      (((HHeight : ℂ) - Real.sqrt 3 / 2) * I) t := by
    have h3 : HasDerivAt (fun t' : ℝ =>
          ((↑t' : ℂ) - 3) * ((HHeight : ℂ) - Real.sqrt 3 / 2))
        ((HHeight : ℂ) - Real.sqrt 3 / 2) t := by
      simpa using (Complex.ofRealCLM.hasDerivAt.sub_const 3).mul_const
        ((HHeight : ℂ) - Real.sqrt 3 / 2)
    have h5 := (((hasDerivAt_const t (Real.sqrt 3 / 2 : ℂ)).add h3).mul_const I)
    have := (hasDerivAt_const t ((-1/2 : ℂ))).add h5
    simp only [zero_add] at this; exact this
  rw [h_deriv.deriv, HHeight_sub_sqrt3_div2]
  simp only [one_mul, Complex.norm_I]; norm_num

/-- Segment 5 derivative bound. -/
lemma norm_deriv_H_seg5_le (t : ℝ) (_s : ℝ) :
    ‖deriv (fun t' : ℝ => ((↑t' : ℂ) - 9/2) +
        (HHeight : ℂ) * I) t‖ ≤ 5 := by
  have h_deriv : HasDerivAt (fun t' : ℝ =>
        ((↑t' : ℂ) - 9/2) + (HHeight : ℂ) * I) 1 t :=
    (Complex.ofRealCLM.hasDerivAt.sub_const (9/2)).add_const ((HHeight : ℂ) * I)
  rw [h_deriv.deriv]
  norm_num

end RectHomotopyProof
