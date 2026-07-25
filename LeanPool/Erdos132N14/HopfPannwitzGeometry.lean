/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
import LeanPool.Erdos132N14.Basic

/-!
# Coordinate geometry for the planar diameter bound

This file isolates the two algebraic facts used in the Perles charging proof
of the planar diameter bound.  Working with dot products and signed areas
keeps all collinear cases explicit and avoids a general-position assumption.
-/

namespace LeanPool.Erdos132N14

noncomputable section

/-- The real dot product on the complex model of the Euclidean plane. -/
def diameterDot (z w : ℂ) : ℝ :=
  z.re * w.re + z.im * w.im

/-- The signed two-dimensional cross product on the complex plane. -/
def planeCross (z w : ℂ) : ℝ :=
  z.re * w.im - z.im * w.re

/-- The signed turn from the ray `a ⟶ b` to the ray `a ⟶ c`. -/
def planeTurn (a b c : ℂ) : ℝ :=
  planeCross (b - a) (c - a)

theorem planeDot_self (z : ℂ) :
    diameterDot z z = Complex.normSq z := by
  simp [diameterDot, Complex.normSq_apply]

theorem planeCross_swap (z w : ℂ) :
    planeCross w z = -planeCross z w := by
  simp [planeCross]
  ring

theorem planeTurn_swap (a b c : ℂ) :
    planeTurn a c b = -planeTurn a b c := by
  unfold planeTurn
  rw [planeCross_swap]

/-- Lagrange's identity in the form needed by the diameter argument. -/
theorem plane_lagrange (x y z : ℂ) :
    diameterDot x x * diameterDot y z =
      diameterDot x y * diameterDot x z + planeCross x y * planeCross x z := by
  simp [diameterDot, planeCross]
  ring

private theorem normSq_of_dist_eq {a b : ℂ} {d : ℝ} (h : dist a b = d) :
    Complex.normSq (b - a) = d ^ 2 := by
  rw [Complex.normSq_eq_norm_sq]
  have hnorm : ‖b - a‖ = d := by
    simpa [Complex.dist_eq, norm_sub_rev] using h
  rw [hnorm]

/-- Two equal-length rays with zero signed area coincide if the distance
between their endpoints is no longer than the rays. -/
theorem equal_rays_of_cross_eq_zero
    {u v w : ℂ} {d : ℝ}
    (huv : dist u v = d) (huw : dist u w = d)
    (hvw : dist v w ≤ d) (hd : 0 < d)
    (hcross : planeCross (v - u) (w - u) = 0) :
    v = w := by
  let x := v - u
  let y := w - u
  have hx : diameterDot x x = d ^ 2 := by
    rw [planeDot_self]
    exact normSq_of_dist_eq huv
  have hy : diameterDot y y = d ^ 2 := by
    rw [planeDot_self]
    exact normSq_of_dist_eq huw
  have hxySq :
      (diameterDot x y) ^ 2 = (d ^ 2) ^ 2 := by
    have hlagrange := plane_lagrange x y y
    rw [hcross, mul_zero, add_zero, hx, hy] at hlagrange
    simpa [pow_two] using hlagrange.symm
  have hvwSq :
      Complex.normSq (y - x) ≤ d ^ 2 := by
    rw [Complex.normSq_eq_norm_sq]
    have hnorm : ‖y - x‖ = dist v w := by
      simp [x, y, Complex.dist_eq, norm_sub_rev]
    rw [hnorm]
    exact (sq_le_sq₀ (dist_nonneg) hd.le).2 hvw
  have hdotLower : d ^ 2 / 2 ≤ diameterDot x y := by
    rw [Complex.normSq_apply] at hvwSq
    simp only [Complex.sub_re, Complex.sub_im] at hvwSq
    simp only [diameterDot] at hx hy
    change d ^ 2 / 2 ≤ x.re * y.re + x.im * y.im
    nlinarith
  have hdot : diameterDot x y = d ^ 2 := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hxySq with hpos | hneg
    · exact hpos
    · have hdSq : 0 < d ^ 2 := sq_pos_of_pos hd
      nlinarith
  have hzero : Complex.normSq (y - x) = 0 := by
    rw [Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im]
    simp only [diameterDot] at hx hy hdot
    nlinarith
  have hyx : y = x := sub_eq_zero.mp (Complex.normSq_eq_zero.mp hzero)
  dsimp [x, y] at hyx
  exact sub_left_injective hyx.symm

/-- If three equal-length edges leave the two ends of a fourth one on
opposite signed sides, the two free endpoints are farther apart.

This is the algebraic core of the fact that two disjoint diameter edges in
the plane must cross. -/
theorem opposite_turns_force_longer_pair
    {u v a b : ℂ} {d : ℝ}
    (huv : dist u v = d) (hua : dist u a = d) (hvb : dist v b = d)
    (hd : 0 < d)
    (ha : planeTurn u v a < 0) (hb : planeTurn v u b < 0) :
    d < dist a b := by
  let x := v - u
  let y := a - u
  let z := b - v
  have hx : diameterDot x x = d ^ 2 := by
    rw [planeDot_self]
    exact normSq_of_dist_eq huv
  have hy : diameterDot y y = d ^ 2 := by
    rw [planeDot_self]
    exact normSq_of_dist_eq hua
  have hz : diameterDot z z = d ^ 2 := by
    rw [planeDot_self]
    exact normSq_of_dist_eq hvb
  have hxy : planeCross x y < 0 := by
    simpa [planeTurn, x, y] using ha
  have hxz : 0 < planeCross x z := by
    have h := hb
    simp [planeTurn, x, z, planeCross] at h ⊢
    nlinarith
  have hdotXY : diameterDot x y ≤ d ^ 2 := by
    have hnonneg := Complex.normSq_nonneg (x - y)
    rw [Complex.normSq_apply] at hnonneg
    simp only [Complex.sub_re, Complex.sub_im] at hnonneg
    simp only [diameterDot] at hx hy ⊢
    nlinarith
  have hdotXZ : -(d ^ 2) ≤ diameterDot x z := by
    have hnonneg := Complex.normSq_nonneg (x + z)
    rw [Complex.normSq_apply] at hnonneg
    simp only [Complex.add_re, Complex.add_im] at hnonneg
    simp only [diameterDot] at hx hz ⊢
    nlinarith
  have hlagrange :
      d ^ 2 * diameterDot y z =
        diameterDot x y * diameterDot x z + planeCross x y * planeCross x z := by
    simpa [hx] using plane_lagrange x y z
  have hnormExpand :
      Complex.normSq (y - x - z) - d ^ 2 =
        2 * (d ^ 2 + diameterDot x z - diameterDot x y - diameterDot y z) := by
    rw [Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im]
    simp only [diameterDot] at hx hy hz ⊢
    nlinarith
  have hidentity :
      d ^ 2 * (Complex.normSq (y - x - z) - d ^ 2) =
        2 * ((d ^ 2 - diameterDot x y) * (d ^ 2 + diameterDot x z) -
          planeCross x y * planeCross x z) := by
    calc
      d ^ 2 * (Complex.normSq (y - x - z) - d ^ 2) =
          d ^ 2 *
            (2 * (d ^ 2 + diameterDot x z - diameterDot x y - diameterDot y z)) := by
              rw [hnormExpand]
      _ = 2 * (d ^ 2 * (d ^ 2 + diameterDot x z - diameterDot x y) -
            d ^ 2 * diameterDot y z) := by ring
      _ = 2 * (d ^ 2 * (d ^ 2 + diameterDot x z - diameterDot x y) -
            (diameterDot x y * diameterDot x z +
              planeCross x y * planeCross x z)) := by rw [hlagrange]
      _ = 2 * ((d ^ 2 - diameterDot x y) * (d ^ 2 + diameterDot x z) -
            planeCross x y * planeCross x z) := by ring
  have hproduct :
      0 ≤ (d ^ 2 - diameterDot x y) * (d ^ 2 + diameterDot x z) :=
    mul_nonneg (sub_nonneg.mpr hdotXY) (by linarith)
  have hcrossProduct :
      planeCross x y * planeCross x z < 0 :=
    mul_neg_of_neg_of_pos hxy hxz
  have hmul :
      0 < d ^ 2 * (Complex.normSq (y - x - z) - d ^ 2) := by
    rw [hidentity]
    nlinarith
  have hnormSq : d ^ 2 < Complex.normSq (y - x - z) := by
    have hdSq : 0 ≤ d ^ 2 := sq_nonneg d
    exact sub_pos.mp (pos_of_mul_pos_right hmul hdSq)
  have habVector : y - x - z = a - b := by
    dsimp [x, y, z]
    ring
  rw [habVector, Complex.normSq_eq_norm_sq] at hnormSq
  have hnorm : d < ‖a - b‖ := by
    nlinarith [norm_nonneg (a - b)]
  simpa [Complex.dist_eq] using hnorm

end

end LeanPool.Erdos132N14
