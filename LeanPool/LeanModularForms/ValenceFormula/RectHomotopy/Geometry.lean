/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import LeanPool.LeanModularForms.GeneralizedResidueTheory.Homotopy.CircleParam
import LeanPool.LeanModularForms.ValenceFormula.Boundary.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Convex.Basic
import Mathlib.MeasureTheory.Integral.CircleIntegral

/-!
# Rect Homotopy: Geometry and Definitions

Basic geometry for the rectangle/chord homotopy proof that
the winding number of `fdBoundary` around interior points is -1.

## Main Definitions

* `RectHomotopyProof.rho`, `rho'`, `iPoint` — elliptic points
* `RectHomotopyProof.chordSegment` — straight line between two points
* `RectHomotopyProof.fdPolygon` — FD boundary with arcs replaced by chords
* `RectHomotopyProof.fdBoundary` — the actual FD boundary curve
* `RectHomotopyProof.HHeight` — height parameter (= `heightCutoff`)
-/

open Complex MeasureTheory Set Filter Topology Metric
open scoped Real Interval

noncomputable section

namespace RectHomotopyProof

/-- The elliptic point ρ = e^{2πi/3} = -1/2 + √3/2 · i -/
def rho : ℂ := -1/2 + Real.sqrt 3 / 2 * I

/-- The elliptic point ρ' = e^{πi/3} = 1/2 + √3/2 · i -/
def rho' : ℂ := 1/2 + Real.sqrt 3 / 2 * I

/-- The elliptic point i -/
def iPoint : ℂ := I

lemma rho_norm : ‖rho‖ = 1 := by
  rw [Complex.norm_eq_sqrt_sq_add_sq]
  simp only [rho, add_re, neg_re, one_re, div_ofNat_re,
    mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im,
    mul_one, add_im, neg_im, one_im, div_ofNat_im,
    mul_im, add_zero]
  ring_nf
  have h : (Real.sqrt 3) ^ 2 = 3 :=
    Real.sq_sqrt (by linarith : (0 : ℝ) ≤ 3)
  rw [h]; norm_num

lemma rho'_norm : ‖rho'‖ = 1 := by
  rw [Complex.norm_eq_sqrt_sq_add_sq]
  simp only [rho', add_re, one_re, div_ofNat_re,
    mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im,
    mul_one, add_im, one_im, div_ofNat_im,
    mul_im, add_zero]
  ring_nf
  have h : (Real.sqrt 3) ^ 2 = 3 :=
    Real.sq_sqrt (by linarith : (0 : ℝ) ≤ 3)
  rw [h]; norm_num

lemma i_point_norm : ‖iPoint‖ = 1 := by
  simp only [iPoint, Complex.norm_I]

lemma outside_closed_unit_ball (z : ℂ) (hz : ‖z‖ > 1) :
    z ∉ closedBall (0 : ℂ) 1 := by
  simp only [mem_closedBall, dist_zero_right, not_le]
  exact hz

/-- The chord (straight line segment) from z₁ to z₂. -/
def chordSegment (z₁ z₂ : ℂ) : ℝ → ℂ :=
  fun t => (1 - t) • z₁ + t • z₂

lemma chordSegment_in_convex {z₁ z₂ : ℂ} {S : Set ℂ} (hS : Convex ℝ S) (hz₁ : z₁ ∈ S) (hz₂ : z₂ ∈ S)
    (t : ℝ) (ht : t ∈ Icc 0 1) :
    chordSegment z₁ z₂ t ∈ S := by
  simp only [chordSegment]
  have ht0 : 0 ≤ t := ht.1
  have ht1 : t ≤ 1 := ht.2
  have h1 : 0 ≤ 1 - t := by linarith
  have h2 : 1 - t + t = 1 := by ring
  exact hS hz₁ hz₂ h1 ht0 h2

lemma convex_closedBall_zero_one :
    Convex ℝ (closedBall (0 : ℂ) 1) :=
  convex_closedBall 0 1

lemma chord_in_closed_unit_ball (z₁ z₂ : ℂ) (hz₁ : ‖z₁‖ = 1) (hz₂ : ‖z₂‖ = 1)
    (t : ℝ) (ht : t ∈ Icc 0 1) :
    chordSegment z₁ z₂ t ∈ closedBall (0 : ℂ) 1 := by
  apply chordSegment_in_convex convex_closedBall_zero_one
  · simp only [mem_closedBall, dist_zero_right, hz₁, le_refl]
  · simp only [mem_closedBall, dist_zero_right, hz₂, le_refl]
  · exact ht

/-- The straight-line homotopy interpolating between an arc and a chord. -/
def arcToChordHomotopy (arc chord : ℝ → ℂ) :
    ℝ × ℝ → ℂ :=
  fun (t, s) => (1 - s) • arc t + s • chord t

lemma arcToChordHomotopy_in_closed_unit_ball (arc chord : ℝ → ℂ)
    (harc : ∀ t ∈ Icc 0 1,
      arc t ∈ closedBall (0 : ℂ) 1)
    (hchord : ∀ t ∈ Icc 0 1,
      chord t ∈ closedBall (0 : ℂ) 1)
    (t : ℝ) (ht : t ∈ Icc 0 1) (s : ℝ) (hs : s ∈ Icc 0 1) :
    arcToChordHomotopy arc chord (t, s) ∈
      closedBall (0 : ℂ) 1 := by
  simp only [arcToChordHomotopy]
  exact chordSegment_in_convex convex_closedBall_zero_one (harc t ht) (hchord t ht) s hs

lemma arcToChordHomotopy_avoids (arc chord : ℝ → ℂ) (p : ℂ) (hp : ‖p‖ > 1)
    (harc : ∀ t ∈ Icc 0 1,
      arc t ∈ closedBall (0 : ℂ) 1)
    (hchord : ∀ t ∈ Icc 0 1,
      chord t ∈ closedBall (0 : ℂ) 1)
    (t : ℝ) (ht : t ∈ Icc 0 1) (s : ℝ) (hs : s ∈ Icc 0 1) :
    arcToChordHomotopy arc chord (t, s) ≠ p := by
  have hH := arcToChordHomotopy_in_closed_unit_ball
    arc chord harc hchord t ht s hs
  have hp_out := outside_closed_unit_ball p hp
  exact fun h => hp_out (h ▸ hH)

/-- The argument of the lower-corner point `ρ'` on the unit circle, `π / 3`. -/
def θRho' : ℝ := Real.pi / 3
/-- The argument of the point `i` on the unit circle, `π / 2`. -/
def θI : ℝ := Real.pi / 2
/-- The argument of the corner point `ρ` on the unit circle, `2π / 3`. -/
def θRho : ℝ := 2 * Real.pi / 3

/-- The unit-circle arc from `ρ'` to `i`. -/
def arc1 (t : ℝ) : ℂ :=
  Complex.exp (I * (θRho' + t * (θI - θRho')))

/-- The unit-circle arc from `i` to `ρ`. -/
def arc2 (t : ℝ) : ℂ :=
  Complex.exp (I * (θI + t * (θRho - θI)))

lemma arc1_on_unit_circle (t : ℝ) : ‖arc1 t‖ = 1 := by
  simp only [arc1]
  have h : I * (↑θRho' + ↑t * (↑θI - ↑θRho')) =
      I * ↑(θRho' + t * (θI - θRho')) := by
    simp only [ofReal_add, ofReal_mul, ofReal_sub]
  rw [h, mul_comm]
  exact Complex.norm_exp_ofReal_mul_I _

lemma arc2_on_unit_circle (t : ℝ) : ‖arc2 t‖ = 1 := by
  simp only [arc2]
  have h : I * (↑θI + ↑t * (↑θRho - ↑θI)) =
      I * ↑(θI + t * (θRho - θI)) := by
    simp only [ofReal_add, ofReal_mul, ofReal_sub]
  rw [h, mul_comm]
  exact Complex.norm_exp_ofReal_mul_I _

lemma arc1_in_closed_unit_ball (t : ℝ) (_ : t ∈ Icc 0 1) :
    arc1 t ∈ closedBall (0 : ℂ) 1 := by
  simp only [mem_closedBall, dist_zero_right,
    arc1_on_unit_circle, le_refl]

lemma arc2_in_closed_unit_ball (t : ℝ) (_ : t ∈ Icc 0 1) :
    arc2 t ∈ closedBall (0 : ℂ) 1 := by
  simp only [mem_closedBall, dist_zero_right,
    arc2_on_unit_circle, le_refl]

/-- The straight chord from `ρ'` to `i`. -/
def chord1 : ℝ → ℂ := chordSegment rho' iPoint
/-- The straight chord from `i` to `ρ`. -/
def chord2 : ℝ → ℂ := chordSegment iPoint rho

lemma chord1_in_closed_unit_ball (t : ℝ) (ht : t ∈ Icc 0 1) :
    chord1 t ∈ closedBall (0 : ℂ) 1 :=
  chord_in_closed_unit_ball rho' iPoint
    rho'_norm i_point_norm t ht

lemma chord2_in_closed_unit_ball (t : ℝ) (ht : t ∈ Icc 0 1) :
    chord2 t ∈ closedBall (0 : ℂ) 1 :=
  chord_in_closed_unit_ball iPoint rho
    i_point_norm rho_norm t ht

lemma exists_ball_in_polygon_interior (p : ℂ) (hp : ‖p‖ > 1) (hp_im : 0 < p.im) :
    ∃ ε > 0, ∀ z, ‖z - p‖ < ε →
      z.im > 0 ∧ ‖z‖ > 1 := by
  use min ((‖p‖ - 1)/2) (p.im/2)
  constructor
  · exact lt_min (by linarith) (by linarith)
  intro z hz
  have hz₁ : ‖z - p‖ < (‖p‖ - 1)/2 :=
    lt_of_lt_of_le hz (min_le_left _ _)
  have hz₂ : ‖z - p‖ < p.im/2 :=
    lt_of_lt_of_le hz (min_le_right _ _)
  constructor
  · have h_im_bound : |z.im - p.im| ≤ ‖z - p‖ :=
      Complex.abs_im_le_norm (z - p)
    have : z.im - p.im > -(p.im/2) := by
      have : |z.im - p.im| < p.im/2 :=
        lt_of_le_of_lt h_im_bound hz₂
      linarith [abs_lt.mp this]
    linarith
  · have h_norm_bound : |‖z‖ - ‖p‖| ≤ ‖z - p‖ :=
      abs_norm_sub_norm_le z p
    have : ‖z‖ - ‖p‖ > -((‖p‖ - 1)/2) := by
      have : |‖z‖ - ‖p‖| < (‖p‖ - 1)/2 :=
        lt_of_le_of_lt h_norm_bound hz₁
      linarith [abs_lt.mp this]
    linarith

lemma circleIntegral_winding (p : ℂ) (ε : ℝ) (hε : 0 < ε) :
    (∮ z in C(p, ε), (z - p)⁻¹) =
      2 * Real.pi * I :=
  circleIntegral.integral_sub_inv_of_mem_ball (Metric.mem_ball_self hε)

/-- Height parameter H = √3/2 + 1 for FD boundary. -/
noncomputable def HHeight : ℝ := Real.sqrt 3 / 2 + 1

lemma H_height_eq_heightCutoff : HHeight = heightCutoff := rfl

/-- Polygon: FD boundary with arcs replaced by chords. -/
noncomputable def fdPolygon : ℝ → ℂ := fun t =>
  if t ≤ 1 then
    1/2 + (HHeight - t * (HHeight -
      Real.sqrt 3 / 2)) * I
  else if t ≤ 2 then
    chordSegment rho' iPoint (t - 1)
  else if t ≤ 3 then
    chordSegment iPoint rho (t - 2)
  else if t ≤ 4 then
    -1/2 + (Real.sqrt 3 / 2 + (t - 3) * (HHeight - Real.sqrt 3 / 2)) * I
  else (t - 9/2) + HHeight * I

/-- The FD boundary curve (local copy matching clean
folder's `fdBoundary`). -/
noncomputable def fdBoundary : ℝ → ℂ := fun t =>
  if t ≤ 1 then
    1/2 + (HHeight - t * (HHeight -
      Real.sqrt 3 / 2)) * I
  else if t ≤ 2 then
    Complex.exp ((Real.pi / 3 + (t - 1) * (Real.pi / 2 - Real.pi / 3)) * I)
  else if t ≤ 3 then
    Complex.exp ((Real.pi / 2 + (t - 2) * (2 * Real.pi / 3 - Real.pi / 2)) * I)
  else if t ≤ 4 then
    -1/2 + (Real.sqrt 3 / 2 + (t - 3) * (HHeight - Real.sqrt 3 / 2)) * I
  else (t - 9/2) + HHeight * I

/-- The homotopy from FD boundary (s=0) to
polygon (s=1). Segments 1,4,5 unchanged;
segments 2,3 use arc-to-chord interpolation. -/
noncomputable def fdBoundaryToPolygonHomotopy :
    ℝ × ℝ → ℂ := fun (t, s) =>
  if t ≤ 1 then
    1/2 + (HHeight - t * (HHeight -
      Real.sqrt 3 / 2)) * I
  else if t ≤ 2 then
    let arc_point := Complex.exp ((Real.pi / 3 + (t - 1) * (Real.pi / 2 - Real.pi / 3)) * I)
    let chord_point := chordSegment rho' iPoint (t - 1)
    (1 - s) • arc_point + s • chord_point
  else if t ≤ 3 then
    let arc_point := Complex.exp ((Real.pi / 2 + (t - 2) * (2 * Real.pi / 3 -
        Real.pi / 2)) * I)
    let chord_point := chordSegment iPoint rho (t - 2)
    (1 - s) • arc_point + s • chord_point
  else if t ≤ 4 then
    -1/2 + (Real.sqrt 3 / 2 + (t - 3) * (HHeight - Real.sqrt 3 / 2)) * I
  else (t - 9/2) + HHeight * I

lemma fdBoundary_at_zero :
    fdBoundary 0 = (1/2 : ℂ) + HHeight * I := by
  simp only [fdBoundary,
    show (0 : ℝ) ≤ 1 from by norm_num, ↓reduceIte, HHeight]
  simp only [Complex.ofReal_zero, zero_mul, sub_zero]

lemma fdBoundary_at_five :
    fdBoundary 5 = (1/2 : ℂ) + HHeight * I := by
  simp only [fdBoundary,
    show ¬(5 : ℝ) ≤ 1 from by norm_num, ↓reduceIte,
    show ¬(5 : ℝ) ≤ 2 from by norm_num,
    show ¬(5 : ℝ) ≤ 3 from by norm_num,
    show ¬(5 : ℝ) ≤ 4 from by norm_num, HHeight]
  norm_cast
  ring_nf

lemma fdBoundaryToPolygonHomotopy_at_t_zero (s : ℝ) :
    fdBoundaryToPolygonHomotopy (0, s) = (1/2 : ℂ) + HHeight * I := by
  simp only [fdBoundaryToPolygonHomotopy,
    show (0 : ℝ) ≤ 1 from by norm_num, ↓reduceIte, HHeight]
  simp only [Complex.ofReal_zero, zero_mul, sub_zero]

lemma fdBoundaryToPolygonHomotopy_at_t_five (s : ℝ) :
    fdBoundaryToPolygonHomotopy (5, s) = (1/2 : ℂ) + HHeight * I := by
  simp only [fdBoundaryToPolygonHomotopy,
    show ¬(5 : ℝ) ≤ 1 from by norm_num, ↓reduceIte,
    show ¬(5 : ℝ) ≤ 2 from by norm_num,
    show ¬(5 : ℝ) ≤ 3 from by norm_num,
    show ¬(5 : ℝ) ≤ 4 from by norm_num, HHeight]
  norm_cast
  ring_nf

lemma segment2_arc_on_unit_circle (t : ℝ) :
    ‖Complex.exp ((Real.pi / 3 + (t - 1) * (Real.pi / 2 - Real.pi / 3)) * I)‖ = 1 := by
  conv_lhs =>
    rw [show ((Real.pi / 3 + (t - 1) * (Real.pi / 2 - Real.pi / 3)) * I : ℂ) =
      ↑(Real.pi / 3 + (t - 1) * (Real.pi / 2 - Real.pi / 3)) * I by
      push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

lemma segment3_arc_on_unit_circle (t : ℝ) :
    ‖Complex.exp ((Real.pi / 2 + (t - 2) * (2 * Real.pi / 3 - Real.pi / 2)) * I)‖ =
    1 := by
  conv_lhs =>
    rw [show ((Real.pi / 2 + (t - 2) * (2 * Real.pi / 3 - Real.pi / 2)) * I : ℂ) =
      ↑(Real.pi / 2 + (t - 2) * (2 * Real.pi / 3 - Real.pi / 2)) * I by
      push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

lemma segment2_arc_in_closed_unit_ball (t : ℝ) :
    Complex.exp ((Real.pi / 3 + (t - 1) * (Real.pi / 2 - Real.pi / 3)) * I) ∈
    closedBall (0 : ℂ) 1 := by
  simp only [mem_closedBall, dist_zero_right,
    segment2_arc_on_unit_circle, le_refl]

lemma segment3_arc_in_closed_unit_ball (t : ℝ) :
    Complex.exp ((Real.pi / 2 + (t - 2) * (2 * Real.pi / 3 - Real.pi / 2)) * I) ∈
    closedBall (0 : ℂ) 1 := by
  simp only [mem_closedBall, dist_zero_right,
    segment3_arc_on_unit_circle, le_refl]

lemma norm_ge_abs_im (z : ℂ) : ‖z‖ ≥ |z.im| :=
  Complex.abs_im_le_norm z

lemma H_height_gt_one : HHeight > 1 := by
  unfold HHeight
  have : Real.sqrt 3 > 0 :=
    Real.sqrt_pos.mpr (by norm_num : (3 : ℝ) > 0)
  linarith

end RectHomotopyProof

end
