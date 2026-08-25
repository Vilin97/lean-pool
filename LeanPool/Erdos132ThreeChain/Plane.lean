/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos132ThreeChain.Basic

/-!
# Planarity constraints on squared distances

Three exact identities carry all of the geometry in this project.  Each is a polynomial
identity in the coordinates of the points involved, so each is proved by `ring`.

* `four_mul_mul_sub_sq_eq` is Heron's formula in squared-distance form.  Its corollary
  `sq_le_four_mul` is the triangle inequality written without square roots, and it is the
  only inequality the classification of chain triangles needs.
* `gramDet_eq_zero` says that the doubled Gram matrix of three plane vectors anchored at a
  fourth point is singular.  Expressed in the six squared distances of four points this is the
  Cayley--Menger relation, and it is the only equation the four-point catalogue needs.
* `gram3_det_eq_zero` is the same singularity written directly in inner products; together
  with `sq_nonneg_combo` it supplies the five-point obstruction.
-/

namespace Erdos132ThreeChain

/-- Twice the signed area of the triangle `p q r`; equivalently the two-dimensional cross
product of `q - p` and `r - p`. -/
def cross (p q r : Point) : ℝ := (q.1 - p.1) * (r.2 - p.2) - (r.1 - p.1) * (q.2 - p.2)

/-- Heron's formula in squared-distance form: the Cayley--Menger expression of a triangle is
four times the square of its doubled signed area. -/
theorem four_mul_mul_sub_sq_eq (p q r : Point) :
    4 * sqDist p q * sqDist p r - (sqDist q r - sqDist p q - sqDist p r) ^ 2
      = 4 * cross p q r ^ 2 := by
  simp only [sqDist, cross]; ring

/-- The triangle inequality for three plane points, stated without square roots. -/
theorem sq_le_four_mul (p q r : Point) :
    (sqDist q r - sqDist p q - sqDist p r) ^ 2 ≤ 4 * sqDist p q * sqDist p r := by
  have h := four_mul_mul_sub_sq_eq p q r
  nlinarith [sq_nonneg (cross p q r)]

/-- The inner product of `p - o` and `q - o`. -/
def dotp (o p q : Point) : ℝ := (p.1 - o.1) * (q.1 - o.1) + (p.2 - o.2) * (q.2 - o.2)

theorem dotp_self (o p : Point) : dotp o p p = sqDist p o := by
  simp only [dotp, sqDist]; ring

theorem two_mul_dotp (o p q : Point) :
    2 * dotp o p q = sqDist p o + sqDist q o - sqDist p q := by
  simp only [dotp, sqDist]; ring

/-- The determinant of the doubled Gram matrix of `b - a`, `c - a`, `d - a`, written in the six
squared distances of `a`, `b`, `c`, `d`. -/
def gramDet (dab dac dad dbc dbd dcd : ℝ) : ℝ :=
  2 * dab * (2 * dac * (2 * dad) - (dac + dad - dcd) ^ 2)
    - (dab + dac - dbc) * ((dab + dac - dbc) * (2 * dad)
        - (dac + dad - dcd) * (dab + dad - dbd))
    + (dab + dad - dbd) * ((dab + dac - dbc) * (dac + dad - dcd)
        - 2 * dac * (dab + dad - dbd))

/-- Three vectors of the plane are linearly dependent, so the anchored Gram determinant of any
four plane points vanishes.  This is the Cayley--Menger relation for four coplanar points. -/
theorem gramDet_eq_zero (a b c d : Point) :
    gramDet (sqDist a b) (sqDist a c) (sqDist a d) (sqDist b c) (sqDist b d) (sqDist c d) = 0 := by
  simp only [gramDet, sqDist]; ring

/-- The Gram determinant of three plane vectors vanishes. -/
theorem gram3_det_eq_zero (o p q r : Point) :
    dotp o p p * (dotp o q q * dotp o r r - dotp o q r ^ 2)
      - dotp o p q * (dotp o p q * dotp o r r - dotp o q r * dotp o p r)
      + dotp o p r * (dotp o p q * dotp o q r - dotp o q q * dotp o p r) = 0 := by
  simp only [dotp]; ring

/-- The squared length of a linear combination of four plane vectors is nonnegative, expanded
in inner products. -/
theorem sq_nonneg_combo (o p q r s : Point) (x y z w : ℝ) :
    0 ≤ x ^ 2 * dotp o p p + y ^ 2 * dotp o q q + z ^ 2 * dotp o r r + w ^ 2 * dotp o s s
      + 2 * (x * y * dotp o p q + x * z * dotp o p r + x * w * dotp o p s
          + y * z * dotp o q r + y * w * dotp o q s + z * w * dotp o r s) := by
  calc (0 : ℝ)
      ≤ (x * (p.1 - o.1) + y * (q.1 - o.1) + z * (r.1 - o.1) + w * (s.1 - o.1)) ^ 2
        + (x * (p.2 - o.2) + y * (q.2 - o.2) + z * (r.2 - o.2) + w * (s.2 - o.2)) ^ 2 := by
        positivity
    _ = _ := by simp only [dotp]; ring

end Erdos132ThreeChain
