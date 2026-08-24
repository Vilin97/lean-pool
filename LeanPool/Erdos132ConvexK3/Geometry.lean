/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
import LeanPool.Erdos132ConvexK3.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.StrictConvexSpace
import Mathlib.Analysis.InnerProductSpace.Convex
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Geometric inputs for the convex three-distance argument

This file proves the strict edge--diagonal inequality, its diameter and
red--blue consequences, chord half-plane separation, and same-half-plane
uniqueness for two-circle intersections.
-/

namespace LeanPool.Erdos132ConvexK3

private def toComplex (p : Point ℝ) : ℂ := ⟨p.1, p.2⟩

/-- Ordinary Euclidean distance between real Cartesian points. -/
noncomputable def euclideanDist (a b : Point ℝ) : ℝ :=
  dist (toComplex a) (toComplex b)

/-- The ordinary distance squares to the polynomial Cartesian squared
distance used by the top-three graph. -/
theorem euclideanDist_sq (a b : Point ℝ) :
    euclideanDist a b ^ 2 = sqDist a b := by
  simp [euclideanDist, Complex.dist_eq, Complex.sq_norm,
    Complex.normSq_apply, toComplex, sqDist]
  ring

private def complexCross (z w : ℂ) : ℝ :=
  z.re * w.im - z.im * w.re

private def complexTurn (a b c : ℂ) : ℝ :=
  complexCross (b - a) (c - a)

private def complexInterpolate (a c : ℂ) (t : ℝ) : ℂ :=
  a + (t : ℂ) * (c - a)

private theorem not_sameRay_of_cross_ne_zero {x y : ℂ}
    (h : complexCross x y ≠ 0) : ¬ SameRay ℝ x y := by
  intro hsame
  rcases hsame with hx | hy | ⟨r₁, r₂, hr₁, hr₂, heq⟩
  · subst x
    exact h (by simp [complexCross])
  · subst y
    exact h (by simp [complexCross])
  · change (r₁ : ℂ) * x = (r₂ : ℂ) * y at heq
    have hre : r₁ * x.re = r₂ * y.re := by
      simpa using congrArg Complex.re heq
    have him : r₁ * x.im = r₂ * y.im := by
      simpa using congrArg Complex.im heq
    have hscaled : (r₁ * r₂) * complexCross x y = 0 := by
      calc
        (r₁ * r₂) * complexCross x y =
            (r₁ * x.re) * (r₂ * y.im) - (r₁ * x.im) * (r₂ * y.re) := by
              simp [complexCross]
              ring
        _ = (r₂ * y.re) * (r₂ * y.im) - (r₂ * y.im) * (r₂ * y.re) := by
              rw [hre, him]
        _ = 0 := by ring
    rcases mul_eq_zero.mp hscaled with hprod | hcross
    · exact (mul_pos hr₁ hr₂).ne' hprod
    · exact h hcross

private theorem strict_triangle_of_cross_ne_zero {a p b : ℂ}
    (h : complexCross (p - a) (b - p) ≠ 0) :
    dist a b < dist a p + dist p b := by
  have hnorm := norm_add_lt_of_not_sameRay (not_sameRay_of_cross_ne_zero h)
  have hsum : (p - a) + (b - p) = b - a := by ring
  rw [hsum] at hnorm
  simpa [Complex.dist_eq, norm_sub_rev] using hnorm

private theorem dist_interpolate_left (a c : ℂ) {t : ℝ} (ht : 0 ≤ t) :
    dist a (complexInterpolate a c t) = t * dist a c := by
  rw [Complex.dist_eq, Complex.dist_eq]
  simp [complexInterpolate, Real.norm_eq_abs, abs_of_nonneg ht, norm_sub_rev]

private theorem dist_interpolate_right (a c : ℂ) {t : ℝ} (ht : t ≤ 1) :
    dist (complexInterpolate a c t) c = (1 - t) * dist a c := by
  rw [Complex.dist_eq, Complex.dist_eq]
  have hnonneg : 0 ≤ 1 - t := sub_nonneg.mpr ht
  have hid : complexInterpolate a c t - c = ((1 - t : ℝ) : ℂ) * (a - c) := by
    apply Complex.ext <;> simp [complexInterpolate] <;> ring
  rw [hid, norm_mul]
  have hnorm : ‖((1 - t : ℝ) : ℂ)‖ = 1 - t := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg]
  rw [hnorm]

private structure ProperDiagonalCrossing (a b c d : ℂ) where
  point : ℂ
  acRatio : ℝ
  bdRatio : ℝ
  acRatio_pos : 0 < acRatio
  acRatio_lt_one : acRatio < 1
  bdRatio_pos : 0 < bdRatio
  bdRatio_lt_one : bdRatio < 1
  on_ac : point = complexInterpolate a c acRatio
  on_bd : point = complexInterpolate b d bdRatio

private def complexStrictQuad (a b c d : ℂ) : Prop :=
  0 < complexTurn a b c ∧ 0 < complexTurn a b d ∧
    0 < complexTurn b c d ∧ 0 < complexTurn c d a

private noncomputable def properDiagonalCrossing
    {a b c d : ℂ} (h : complexStrictQuad a b c d) :
    ProperDiagonalCrossing a b c d := by
  let den := complexCross (c - a) (d - b)
  let nt := complexCross (b - a) (d - b)
  let nu := complexCross (b - a) (c - a)
  have hnt : 0 < nt := by
    rcases h with ⟨_, habd, _, _⟩
    dsimp [nt, complexTurn, complexCross] at habd ⊢
    nlinarith
  have hdenSubT : 0 < den - nt := by
    rcases h with ⟨_, _, hbcd, _⟩
    have hidentity : den - nt = complexTurn b c d := by
      dsimp [den, nt, complexTurn, complexCross]
      ring
    rw [hidentity]
    exact hbcd
  have hnu : 0 < nu := h.1
  have hdenSubU : 0 < den - nu := by
    rcases h with ⟨_, _, _, hcda⟩
    dsimp [den, nu, complexTurn, complexCross] at hcda ⊢
    nlinarith
  have hden : 0 < den := by linarith
  let t := nt / den
  let u := nu / den
  have ht0 : 0 < t := div_pos hnt hden
  have ht1 : t < 1 := (div_lt_one hden).mpr (by linarith)
  have hu0 : 0 < u := div_pos hnu hden
  have hu1 : u < 1 := (div_lt_one hden).mpr (by linarith)
  let p := complexInterpolate a c t
  refine ⟨p, t, u, ht0, ht1, hu0, hu1, rfl, ?_⟩
  change complexInterpolate a c (nt / den) = complexInterpolate b d (nu / den)
  apply Complex.ext
  · simp only [complexInterpolate, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.sub_re, zero_mul, sub_zero]
    field_simp [ne_of_gt hden]
    dsimp [nt, nu, den, complexCross]
    ring
  · simp only [complexInterpolate, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.sub_im, zero_mul, add_zero]
    field_simp [ne_of_gt hden]
    dsimp [nt, nu, den, complexCross]
    ring

private theorem cross_first_triangle (a b c : ℂ) (t : ℝ) :
    complexCross (complexInterpolate a c t - a) (b - complexInterpolate a c t) =
      -t * complexTurn a b c := by
  simp [complexInterpolate, complexTurn, complexCross]
  ring

private theorem cross_second_triangle (a c d : ℂ) (t : ℝ) :
    complexCross (complexInterpolate a c t - c) (d - complexInterpolate a c t) =
      -(1 - t) * complexTurn c d a := by
  simp [complexInterpolate, complexTurn, complexCross]
  ring

private theorem complex_edge_diagonal_inequality
    {a b c d : ℂ} (h : complexStrictQuad a b c d) :
    dist a b + dist c d < dist a c + dist b d := by
  let X := properDiagonalCrossing h
  have habc : 0 < complexTurn a b c := h.1
  have hcda : 0 < complexTurn c d a := h.2.2.2
  have hcrossAB : complexCross (X.point - a) (b - X.point) ≠ 0 := by
    rw [X.on_ac, cross_first_triangle]
    exact mul_ne_zero (neg_ne_zero.mpr X.acRatio_pos.ne') habc.ne'
  have hcrossCD : complexCross (X.point - c) (d - X.point) ≠ 0 := by
    rw [X.on_ac, cross_second_triangle]
    exact mul_ne_zero
      (neg_ne_zero.mpr (sub_pos.mpr X.acRatio_lt_one).ne') hcda.ne'
  have hab := strict_triangle_of_cross_ne_zero hcrossAB
  have hcd := strict_triangle_of_cross_ne_zero hcrossCD
  have hac : dist a X.point + dist X.point c = dist a c := by
    rw [X.on_ac, dist_interpolate_left _ _ X.acRatio_pos.le,
      dist_interpolate_right _ _ X.acRatio_lt_one.le]
    ring
  have hbd : dist b X.point + dist X.point d = dist b d := by
    rw [X.on_bd, dist_interpolate_left _ _ X.bdRatio_pos.le,
      dist_interpolate_right _ _ X.bdRatio_lt_one.le]
    ring
  calc
    dist a b + dist c d <
        (dist a X.point + dist X.point b) + (dist c X.point + dist X.point d) :=
      add_lt_add hab hcd
    _ = (dist a X.point + dist X.point c) +
        (dist b X.point + dist X.point d) := by
      rw [dist_comm X.point b, dist_comm c X.point]
      ring
    _ = dist a c + dist b d := by rw [hac, hbd]

/-- **Edge--diagonal inequality.** Opposite side sums in a strictly convex
cyclic quadrilateral are strictly smaller than the diagonal sum. -/
theorem edge_diagonal_inequality
    {a b c d : Point ℝ} (h : StrictConvexQuad a b c d) :
    euclideanDist a b + euclideanDist c d <
      euclideanDist a c + euclideanDist b d := by
  apply complex_edge_diagonal_inequality
  simpa [complexStrictQuad, complexTurn, complexCross, toComplex, StrictConvexQuad,
    turn] using h

/-- Four strictly acute interior angles are impossible in a strict convex
quadrilateral.  This is the algebraic form of the final sentence in ErLV's
majorant argument. -/
theorem strict_convex_quad_not_all_acute
    {a b c d : Point ℝ} (hquad : StrictConvexQuad a b c d)
    (ha : 0 < dot (b - a) (d - a))
    (hb : 0 < dot (a - b) (c - b))
    (hc : 0 < dot (b - c) (d - c))
    (hd : 0 < dot (c - d) (a - d)) : False := by
  let X := properDiagonalCrossing (a := toComplex a) (b := toComplex b)
    (c := toComplex c) (d := toComplex d) (by
      simpa [complexStrictQuad, complexTurn, complexCross, toComplex, StrictConvexQuad,
        turn] using hquad)
  let Xp : Point ℝ := (X.point.re, X.point.im)
  let A : Point ℝ := a - Xp
  let B : Point ℝ := b - Xp
  let lam := (1 - X.acRatio) / X.acRatio
  let mu := (1 - X.bdRatio) / X.bdRatio
  have hlam : 0 < lam := div_pos (sub_pos.mpr X.acRatio_lt_one) X.acRatio_pos
  have hmu : 0 < mu := div_pos (sub_pos.mpr X.bdRatio_lt_one) X.bdRatio_pos
  have hcX : c - Xp = -lam • A := by
    apply Prod.ext
    · change c.1 - X.point.re = -lam * (a.1 - X.point.re)
      rw [X.on_ac]
      simp only [lam, complexInterpolate, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.sub_re, zero_mul, sub_zero, toComplex]
      field_simp [ne_of_gt X.acRatio_pos]
      ring
    · change c.2 - X.point.im = -lam * (a.2 - X.point.im)
      rw [X.on_ac]
      simp only [lam, complexInterpolate, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.sub_im, zero_mul, add_zero, toComplex]
      field_simp [ne_of_gt X.acRatio_pos]
      ring
  have hdX : d - Xp = -mu • B := by
    apply Prod.ext
    · change d.1 - X.point.re = -mu * (b.1 - X.point.re)
      rw [X.on_bd]
      simp only [mu, complexInterpolate, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.sub_re, zero_mul, sub_zero, toComplex]
      field_simp [ne_of_gt X.bdRatio_pos]
      ring
    · change d.2 - X.point.im = -mu * (b.2 - X.point.im)
      rw [X.on_bd]
      simp only [mu, complexInterpolate, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.sub_im, zero_mul, add_zero, toComplex]
      field_simp [ne_of_gt X.bdRatio_pos]
      ring
  have hba : B - A = b - a := by
    apply Prod.ext <;> simp [A, B, Xp]
  have hab : A - B = a - b := by
    apply Prod.ext <;> simp [A, B, Xp]
  have hda : -mu • B - A = d - a := by
    rw [← hdX]
    apply Prod.ext <;> simp [A, Xp]
  have hcb : -lam • A - B = c - b := by
    rw [← hcX]
    apply Prod.ext <;> simp [B, Xp]
  have hbc : B + lam • A = b - c := by
    have hx1 := congrArg Prod.fst hcX
    have hx2 := congrArg Prod.snd hcX
    apply Prod.ext
    · change B.1 + lam * A.1 = b.1 - c.1
      change c.1 - Xp.1 = -lam * A.1 at hx1
      simp [B]
      linarith
    · change B.2 + lam * A.2 = b.2 - c.2
      change c.2 - Xp.2 = -lam * A.2 at hx2
      simp [B]
      linarith
  have hdc : -mu • B + lam • A = d - c := by
    have hcx1 := congrArg Prod.fst hcX
    have hcx2 := congrArg Prod.snd hcX
    have hdx1 := congrArg Prod.fst hdX
    have hdx2 := congrArg Prod.snd hdX
    apply Prod.ext
    · change (-mu) * B.1 + lam * A.1 = d.1 - c.1
      change c.1 - Xp.1 = -lam * A.1 at hcx1
      change d.1 - Xp.1 = -mu * B.1 at hdx1
      linarith
    · change (-mu) * B.2 + lam * A.2 = d.2 - c.2
      change c.2 - Xp.2 = -lam * A.2 at hcx2
      change d.2 - Xp.2 = -mu * B.2 at hdx2
      linarith
  have hcd : -lam • A + mu • B = c - d := by
    have hcx1 := congrArg Prod.fst hcX
    have hcx2 := congrArg Prod.snd hcX
    have hdx1 := congrArg Prod.fst hdX
    have hdx2 := congrArg Prod.snd hdX
    apply Prod.ext
    · change (-lam) * A.1 + mu * B.1 = c.1 - d.1
      change c.1 - Xp.1 = -lam * A.1 at hcx1
      change d.1 - Xp.1 = -mu * B.1 at hdx1
      linarith
    · change (-lam) * A.2 + mu * B.2 = c.2 - d.2
      change c.2 - Xp.2 = -lam * A.2 at hcx2
      change d.2 - Xp.2 = -mu * B.2 at hdx2
      linarith
  have had : A + mu • B = a - d := by
    have hx1 := congrArg Prod.fst hdX
    have hx2 := congrArg Prod.snd hdX
    apply Prod.ext
    · change A.1 + mu * B.1 = a.1 - d.1
      change d.1 - Xp.1 = -mu * B.1 at hx1
      simp [A]
      linarith
    · change A.2 + mu * B.2 = a.2 - d.2
      change d.2 - Xp.2 = -mu * B.2 at hx2
      simp [A]
      linarith
  have ha' : 0 < dot (B - A) (-mu • B - A) := by
    rw [hba, hda]
    exact ha
  have hb' : 0 < dot (A - B) (-lam • A - B) := by
    rw [hab, hcb]
    exact hb
  have hc' : 0 < dot (B + lam • A) (-mu • B + lam • A) := by
    rw [hbc, hdc]
    exact hc
  have hd' : 0 < dot (-lam • A + mu • B) (A + mu • B) := by
    rw [hcd, had]
    exact hd
  let D := lam * dot A A - mu * dot B B
  have hleft :
      0 < dot (B + lam • A) (-mu • B + lam • A) +
        lam * dot (B - A) (-mu • B - A) :=
    add_pos hc' (mul_pos hlam ha')
  have hleftId :
      dot (B + lam • A) (-mu • B + lam • A) +
          lam * dot (B - A) (-mu • B - A) = (lam + 1) * D := by
    simp [D, dot]
    ring
  have hD : 0 < D := by
    rw [hleftId] at hleft
    rcases mul_pos_iff.mp hleft with hpos | hneg
    · exact hpos.2
    · linarith
  have hright :
      0 < dot (-lam • A + mu • B) (A + mu • B) +
        mu * dot (A - B) (-lam • A - B) :=
    add_pos hd' (mul_pos hmu hb')
  have hrightId :
      dot (-lam • A + mu • B) (A + mu • B) +
          mu * dot (A - B) (-lam • A - B) = -(mu + 1) * D := by
    simp [D, dot]
    ring
  rw [hrightId] at hright
  have hnegative : -(mu + 1) * D < 0 := mul_neg_of_neg_of_pos (by linarith) hD
  linarith

/-- **Avoiding-diameter impossibility.** Two opposite sides of a strictly
convex cyclic quadrilateral cannot both realize its diameter. -/
theorem avoiding_diameters_impossible
    {a b c d : Point ℝ} {diameter : ℝ}
    (hquad : StrictConvexQuad a b c d)
    (hab : euclideanDist a b = diameter)
    (hcd : euclideanDist c d = diameter)
    (hac : euclideanDist a c ≤ diameter)
    (hbd : euclideanDist b d ≤ diameter) : False := by
  have hed := edge_diagonal_inequality hquad
  linarith

/-- **Red--blue forcing.** Avoiding sides in the largest and second-largest
classes force both diagonals into the largest class. -/
theorem red_blue_forcing
    {a b c d : Point ℝ} {d₁ d₂ : ℝ}
    (hquad : StrictConvexQuad a b c d)
    (hd : d₂ < d₁)
    (hab : euclideanDist a b = d₁)
    (hcd : euclideanDist c d = d₂)
    (hac : euclideanDist a c ≤ d₂ ∨ euclideanDist a c = d₁)
    (hbd : euclideanDist b d ≤ d₂ ∨ euclideanDist b d = d₁) :
    euclideanDist a c = d₁ ∧ euclideanDist b d = d₁ := by
  have hed := edge_diagonal_inequality hquad
  rcases hac with hac | hac <;> rcases hbd with hbd | hbd
  · linarith
  · linarith
  · linarith
  · exact ⟨hac, hbd⟩

theorem turn_cyclic
    {K : Type*} [CommRing K] (a b c : Point K) : turn a b c = turn b c a := by
  simp [turn]
  ring

theorem turn_swap
    {K : Type*} [CommRing K] (a b c : Point K) : turn a c b = -turn a b c := by
  simp [turn]
  ring

/-- **Chord half-plane separation.** In cyclic order `a,b,c,d`, the two
boundary arcs represented by `b` and `d` lie in opposite open half-planes
of chord `ac`. -/
theorem chord_half_plane_separation
    {K : Type*} [CommRing K] [LinearOrder K]
    {a b c d : Point K}
    (h : StrictConvexQuad a b c d) :
    InLeftOpenHalfPlane a c d ∧ InLeftOpenHalfPlane c a b := by
  constructor
  · have hcda := h.2.2.2
    simpa [InLeftOpenHalfPlane, turn_cyclic a c d] using hcda
  · have habc := h.1
    rw [InLeftOpenHalfPlane, turn_cyclic c a b]
    exact habc

/-- **Same-half-plane two-circle uniqueness.** Two points with the same
distances to distinct centers coincide if both are in the same open
half-plane bounded by the line of centers. -/
theorem same_half_plane_two_circle_unique
    {a b p q : Point ℝ} (hab : a ≠ b)
    (hap : sqDist a p = sqDist a q)
    (hbp : sqDist b p = sqDist b q)
    (hp : InLeftOpenHalfPlane a b p)
    (hq : InLeftOpenHalfPlane a b q) : p = q := by
  let ac := toComplex a
  let bc := toComplex b
  let pc := toComplex p
  let qc := toComplex q
  have habc : ac ≠ bc := by
    intro heq
    apply hab
    apply Prod.ext
    · exact congrArg Complex.re heq
    · exact congrArg Complex.im heq
  let vx := bc.re - ac.re
  let vy := bc.im - ac.im
  let px := pc.re - ac.re
  let py := pc.im - ac.im
  let qx := qc.re - ac.re
  let qy := qc.im - ac.im
  let dp := vx * px + vy * py
  let dq := vx * qx + vy * qy
  let cp := vx * py - vy * px
  let cq := vx * qy - vy * qx
  have hnorm : px ^ 2 + py ^ 2 = qx ^ 2 + qy ^ 2 := by
    simpa [sqDist, ac, pc, qc, toComplex, px, py, qx, qy] using hap
  have hdot : dp = dq := by
    dsimp [sqDist, ac, bc, pc, qc, toComplex, vx, vy, px, py, qx, qy, dp, dq]
      at hap hbp ⊢
    nlinarith
  have hlagP : dp ^ 2 + cp ^ 2 = (vx ^ 2 + vy ^ 2) * (px ^ 2 + py ^ 2) := by
    dsimp [dp, cp]
    ring
  have hlagQ : dq ^ 2 + cq ^ 2 = (vx ^ 2 + vy ^ 2) * (qx ^ 2 + qy ^ 2) := by
    dsimp [dq, cq]
    ring
  have hcrossSq : cp ^ 2 = cq ^ 2 := by
    rw [hdot] at hlagP
    nlinarith [hlagP, hlagQ, hnorm]
  have hcp : 0 < cp := by
    simpa [InLeftOpenHalfPlane, turn, ac, bc, pc, toComplex, vx, vy, px, py, cp]
      using hp
  have hcq : 0 < cq := by
    simpa [InLeftOpenHalfPlane, turn, ac, bc, qc, toComplex, vx, vy, qx, qy, cq]
      using hq
  have hcross : cp = cq := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hcrossSq with heq | heq
    · exact heq
    · rw [heq] at hcp
      exact (not_lt_of_ge (neg_nonpos.mpr hcq.le) hcp).elim
  have hv : 0 < vx ^ 2 + vy ^ 2 := by
    have hba : bc - ac ≠ 0 := sub_ne_zero.mpr habc.symm
    have hnormPos := Complex.normSq_pos.mpr hba
    simpa [Complex.normSq_apply, vx, vy, pow_two] using hnormPos
  have hx : px = qx := by
    have hid : (vx ^ 2 + vy ^ 2) * (px - qx) =
        vx * (dp - dq) - vy * (cp - cq) := by
      dsimp [dp, dq, cp, cq]
      ring
    have hmul : (vx ^ 2 + vy ^ 2) * (px - qx) = 0 := by
      rw [hid, hdot, hcross]
      ring
    exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left hv.ne')
  have hy : py = qy := by
    have hid : (vx ^ 2 + vy ^ 2) * (py - qy) =
        vy * (dp - dq) + vx * (cp - cq) := by
      dsimp [dp, dq, cp, cq]
      ring
    have hmul : (vx ^ 2 + vy ^ 2) * (py - qy) = 0 := by
      rw [hid, hdot, hcross]
      ring
    exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left hv.ne')
  apply Prod.ext
  · dsimp [px, qx, pc, qc, ac, toComplex] at hx
    linarith
  · dsimp [py, qy, pc, qc, ac, toComplex] at hy
    linarith

/-- A point distinct from both endpoints and contained in both closed disks
whose common diameter is the endpoint segment has abscissa strictly between
the endpoint abscissae.  The disk bounds are the explicit diameter property
needed for the strict box `0 < X < 2c`. -/
theorem diameter_lens_abscissa
    {c X Y : ℝ} (hc : 0 < c)
    (hleft : sqDist (0, 0) (X, Y) ≤ (2 * c) ^ 2)
    (hright : sqDist (2 * c, 0) (X, Y) ≤ (2 * c) ^ 2)
    (hneLeft : (X, Y) ≠ (0, 0))
    (hneRight : (X, Y) ≠ (2 * c, 0)) :
    0 < X ∧ X < 2 * c := by
  have hxNonneg : 0 ≤ X := by
    simp [sqDist] at hright
    nlinarith [sq_nonneg X, sq_nonneg Y]
  have hxNe : X ≠ 0 := by
    intro hx
    apply hneLeft
    apply Prod.ext
    · exact hx
    · simp [sqDist, hx] at hright
      have hy : Y = 0 := by nlinarith [sq_nonneg Y]
      exact hy
  have hxUpper : X ≤ 2 * c := by
    simp [sqDist] at hleft
    nlinarith [sq_nonneg X, sq_nonneg Y]
  have hxUpperNe : X ≠ 2 * c := by
    intro hx
    apply hneRight
    apply Prod.ext
    · exact hx
    · simp [sqDist, hx] at hleft
      have hy : Y = 0 := by nlinarith [sq_nonneg Y]
      exact hy
  exact ⟨lt_of_le_of_ne hxNonneg hxNe.symm, lt_of_le_of_ne hxUpper hxUpperNe⟩

/-- The exact algebra behind draft equation (5.5).  The displayed constraint
`2cd + d² = Δ(H + (H - Δ))` is essential; without it the identity is false. -/
theorem two_rung_sum_identity
    {c d H Δ X Y : ℝ}
    (hconstraint : 2 * c * d + d ^ 2 = Δ * (H + (H - Δ))) :
    sqDist (X, Y) (c + d, H - Δ) + sqDist (X, Y) (c - d, H - Δ) -
        2 * sqDist (X, Y) (c, H) = -4 * c * d + 4 * Δ * Y := by
  simp only [sqDist]
  nlinarith [hconstraint]

/-- Draft equation (5.5), with `B - A = -4cd` made explicit. -/
theorem two_rung_sum_identity_with_classes
    {c d H Δ X Y A B : ℝ}
    (hconstraint : 2 * c * d + d ^ 2 = Δ * (H + (H - Δ)))
    (hclasses : B - A = -4 * c * d) :
    sqDist (X, Y) (c + d, H - Δ) + sqDist (X, Y) (c - d, H - Δ) -
        2 * sqDist (X, Y) (c, H) = B - A + 4 * Δ * Y := by
  rw [two_rung_sum_identity hconstraint, hclasses]

end LeanPool.Erdos132ConvexK3
