/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
import LeanPool.Erdos132ConvexK3.Geometry
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The shared-diameter lens

This file formalizes the unique-farthest lemma used in draft Section 6.  The
normalization is

`e = (0,0)`, `t = (2c,0)`, `s = (c,H)`, `d₁² = c² + H²`.

The P5-1 correction is explicit in the theorem statement: the lower point
`P = (X,Y)` must satisfy `|Ps|² ≤ d₁²`.  Convexity supplies `Y < 0`, but it
does not by itself supply `0 < X < 2c`; the diameter bound does.
-/

namespace LeanPool.Erdos132ConvexK3

/-- The intersection of the two closed radius-`d₁` disks centered at
`(0,0)` and `(2c,0)`, where `d₁² = c² + H²`. -/
def InSharedDiameterLens (c H : ℝ) (v : Point ℝ) : Prop :=
  sqDist (0, 0) v ≤ c ^ 2 + H ^ 2 ∧
    sqDist (2 * c, 0) v ≤ c ^ 2 + H ^ 2

/-- **P5-1, explicit.** If a lower point's distance to the shared diameter
tip is at most the diameter, then its abscissa lies strictly between the two
centers.  The diameter hypothesis is load-bearing. -/
theorem diameter_partner_abscissa
    {c H X Y : ℝ} (hc : 0 < c) (hH : 0 < H) (hY : Y < 0)
    (hdiameter : sqDist (X, Y) (c, H) ≤ c ^ 2 + H ^ 2) :
    0 < X ∧ X < 2 * c := by
  have hHY : H * Y < 0 := mul_neg_of_pos_of_neg hH hY
  have hvertical : H ^ 2 < (H - Y) ^ 2 := by
    nlinarith [sq_nonneg Y]
  have hxSq : (X - c) ^ 2 < c ^ 2 := by
    simp only [sqDist] at hdiameter
    nlinarith
  constructor <;> nlinarith [sq_nonneg X, sq_nonneg (X - 2 * c)]

/-- Every point of the shared-diameter lens has ordinate at most that of the
upper tip `(c,H)`. -/
theorem shared_diameter_lens_ordinate_le
    {c H x y : ℝ} (hH : 0 ≤ H)
    (hv : InSharedDiameterLens c H (x, y)) : y ≤ H := by
  rcases hv with ⟨hleft, hright⟩
  simp only [sqDist] at hleft hright
  have hradial : (x - c) ^ 2 + y ^ 2 ≤ H ^ 2 := by
    nlinarith
  by_contra hnot
  have hy : H < y := lt_of_not_ge hnot
  have hsum : 0 < y + H := by linarith
  have hprod : 0 < (y - H) * (y + H) :=
    mul_pos (sub_pos.mpr hy) hsum
  nlinarith [sq_nonneg (x - c)]

/-- **Diameter-lens unique farthest point.** Let `P=(X,Y)` be below the
center line and no farther than the diameter from the upper tip `s`.  Then
every other point of the shared-diameter lens is strictly closer to `P` than
`s` is.

This is the exact squared-distance form of draft (5.2), used in Section 6.
The `hPdiameter` hypothesis is the formal repair of P5-1. -/
theorem diameter_lens_unique_farthest
    {c H X Y : ℝ} (hc : 0 < c) (hH : 0 < H) (hY : Y < 0)
    (hPdiameter : sqDist (X, Y) (c, H) ≤ c ^ 2 + H ^ 2)
    {v : Point ℝ} (hv : InSharedDiameterLens c H v)
    (hne : v ≠ (c, H)) :
    sqDist (X, Y) v < sqDist (X, Y) (c, H) := by
  obtain ⟨hX0, hX2⟩ := diameter_partner_abscissa hc hH hY hPdiameter
  rcases v with ⟨x, y⟩
  have hyLe : y ≤ H := shared_diameter_lens_ordinate_le hH.le hv
  rcases hv with ⟨hleft, hright⟩
  simp only [sqDist] at hleft hright ⊢
  have hradial : (x - c) ^ 2 + y ^ 2 ≤ H ^ 2 := by
    nlinarith
  have hyNe : y ≠ H := by
    intro hy
    apply hne
    have hx : x = c := by
      nlinarith [sq_nonneg (x - c)]
    exact Prod.ext hx hy
  have hyLt : y < H := lt_of_le_of_ne hyLe hyNe
  have hA : 0 ≤ c ^ 2 + H ^ 2 - (x ^ 2 + y ^ 2) := by
    nlinarith
  have hB : 0 ≤ c ^ 2 + H ^ 2 - ((x - 2 * c) ^ 2 + y ^ 2) := by
    nlinarith
  have htermA :
      0 ≤ (2 * c - X) * (c ^ 2 + H ^ 2 - (x ^ 2 + y ^ 2)) :=
    mul_nonneg (by linarith) hA
  have htermB :
      0 ≤ X * (c ^ 2 + H ^ 2 - ((x - 2 * c) ^ 2 + y ^ 2)) :=
    mul_nonneg hX0.le hB
  have hcY : 0 < -4 * c * Y := by
    nlinarith [mul_neg_of_pos_of_neg hc hY]
  have htermY : 0 < (-4 * c * Y) * (H - y) :=
    mul_pos hcY (sub_pos.mpr hyLt)
  have hidentity :
      2 * c *
          (((c - X) ^ 2 + (H - Y) ^ 2) -
            ((x - X) ^ 2 + (y - Y) ^ 2)) =
        (2 * c - X) * (c ^ 2 + H ^ 2 - (x ^ 2 + y ^ 2)) +
        X * (c ^ 2 + H ^ 2 - ((x - 2 * c) ^ 2 + y ^ 2)) +
        (-4 * c * Y) * (H - y) := by
    ring
  have hscaled :
      0 < 2 * c *
          (((c - X) ^ 2 + (H - Y) ^ 2) -
            ((x - X) ^ 2 + (y - Y) ^ 2)) := by
    rw [hidentity]
    nlinarith
  nlinarith

end LeanPool.Erdos132ConvexK3
