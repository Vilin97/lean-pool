/-
Copyright (c) 2026 Boon Suan Ho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boon Suan Ho
-/

import LeanPool.Nivat.Core.Basic
import Mathlib.Data.Int.GCD
import Mathlib.LinearAlgebra.Prod
import Mathlib.Tactic.Ring

/-
Upstream: https://github.com/boonsuan/nivat
Commit: 84fe839635bdebb7d5e80c209b4f578a0c767fcf
Originally released under MIT; the upstream copyright and permission notice follow.

MIT License

Copyright (c) 2026 Boon Suan Ho

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

/-!
# Primitive lattice directions and rational coordinates

This module supplies the primitive-direction coordinates of Section 1.1 of
`paper/nivat.tex`, used in Proposition 3.5 (`prop:tangent-period`) and the proof
of Theorem 5.1. The integer gcd and a Bézout identity extend every primitive
direction to a lattice basis.

The main results are `exists_lattice_basis_for_nonzero`,
`latticeEquivRatLinear_compatible`, and `transverse_coordinate_ne_zero`. The
rational extension permits convex windows to be transported through the same
coordinate change as the lattice configurations.
-/

namespace Nivat

/-- An additive lattice map is determined by its two basis vectors, giving the primitive-direction
coordinate formula used in Section 1.1. -/
theorem lattice_addEquiv_coordinates (e : Lattice ≃+ Lattice) (z : Lattice) :
    e z = z.1 • e (1, 0) + z.2 • e (0, 1) := by
  have hz : z = z.1 • ((1 : ℤ), (0 : ℤ)) + z.2 • ((0 : ℤ), (1 : ℤ)) := by
    apply Prod.ext <;> simp [Prod.smul_mk]
  calc
    e z = e (z.1 • ((1 : ℤ), (0 : ℤ)) + z.2 • ((0 : ℤ), (1 : ℤ))) := congrArg e hz
    _ = _ := by rw [map_add, map_zsmul, map_zsmul]

/-- A Bézout identity constructs an integer lattice basis containing the primitive vector `(x,y)`,
as in Section 1.1. -/
def bezoutLatticeEquiv (x y a b : ℤ) (h : x * a + y * b = 1) : Lattice ≃+ Lattice where
  toFun z := (x * z.1 - b * z.2, y * z.1 + a * z.2)
  invFun z := (a * z.1 + b * z.2, -y * z.1 + x * z.2)
  left_inv z := by
    apply Prod.ext <;> dsimp
    · calc
        a * (x * z.1 - b * z.2) + b * (y * z.1 + a * z.2) =
          (x * a + y * b) * z.1 := by ring
        _ = z.1 := by rw [h, one_mul]
    · calc
        -y * (x * z.1 - b * z.2) + x * (y * z.1 + a * z.2) =
          (x * a + y * b) * z.2 := by ring
        _ = z.2 := by rw [h, one_mul]
  right_inv z := by
    apply Prod.ext <;> dsimp
    · calc
        x * (a * z.1 + b * z.2) - b * (-y * z.1 + x * z.2) =
          (x * a + y * b) * z.1 := by ring
        _ = z.1 := by rw [h, one_mul]
    · calc
        y * (a * z.1 + b * z.2) + a * (-y * z.1 + x * z.2) =
          (x * a + y * b) * z.2 := by ring
        _ = z.2 := by rw [h, one_mul]
  map_add' z w := by apply Prod.ext <;> dsimp <;> ring

/-- Every nonzero integer direction is a positive multiple of the first vector of a lattice basis.
This is the primitive-direction normalization of Section 1.1, used in Proposition 3.5 and
Theorem 5.1. -/
theorem exists_lattice_basis_for_nonzero (h : Lattice) (hh : h ≠ 0) :
    ∃ q : ℕ, 0 < q ∧ ∃ e : Lattice ≃+ Lattice, e ((q : ℤ), 0) = h := by
  have hg : 0 < Int.gcd h.1 h.2 := by
    apply Int.gcd_pos_iff.mpr
    by_contra! hz
    exact hh (Prod.ext hz.1 hz.2)
  obtain ⟨x, y, hgcd, hx, hy⟩ := Int.exists_gcd_one hg
  have hbez : x * Int.gcdA x y + y * Int.gcdB x y = 1 := by
    simpa only [hgcd, Nat.cast_one] using (Int.gcd_eq_gcd_ab x y).symm
  refine ⟨Int.gcd h.1 h.2, hg, bezoutLatticeEquiv x y _ _ hbez, ?_⟩
  apply Prod.ext <;> simp only [bezoutLatticeEquiv, AddEquiv.coe_mk, Equiv.coe_fn_mk,
    mul_zero, sub_zero, add_zero]
  · exact hx.symm
  · exact hy.symm

/-- The coordinate embedding of the integer lattice into the rational plane, used to express
convexity in the coordinate normalization of Theorem 5.1. -/
def latticeRatCast (z : Lattice) : ℚ × ℚ := (z.1, z.2)

/-- The rational linear extension of a lattice equivalence, used to transport convex windows in
the proof of Theorem 5.1. -/
def latticeEquivRatLinear (e : Lattice ≃+ Lattice) : (ℚ × ℚ) →ₗ[ℚ] (ℚ × ℚ) where
  toFun z :=
    (((e (1, 0)).1 : ℚ) * z.1 + ((e (0, 1)).1 : ℚ) * z.2,
     ((e (1, 0)).2 : ℚ) * z.1 + ((e (0, 1)).2 : ℚ) * z.2)
  map_add' z w := by apply Prod.ext <;> dsimp <;> ring
  map_smul' r z := by apply Prod.ext <;> dsimp <;> ring

/-- The rational linear extension agrees with its lattice equivalence at every integer site. This
is the compatibility needed by the convex-window coordinate change in Theorem 5.1. -/
theorem latticeEquivRatLinear_compatible (e : Lattice ≃+ Lattice) (z : Lattice) :
    latticeRatCast (e z) = latticeEquivRatLinear e (latticeRatCast z) := by
  rw [lattice_addEquiv_coordinates]
  apply Prod.ext <;> dsimp [latticeRatCast, latticeEquivRatLinear] <;>
    simp only [Int.cast_add, Int.cast_mul] <;> ring

/-- Two nonparallel directions have a nonzero transverse coordinate after the first is made
horizontal. This is the coordinate normalization in the nonparallel case of Theorem 5.1. -/
theorem transverse_coordinate_ne_zero (e : Lattice ≃+ Lattice) (q : ℕ)
    {h t : Lattice} (he : e ((q : ℤ), 0) = h)
    (hnonparallel : h.1 * t.2 ≠ h.2 * t.1) : (e.symm t).2 ≠ 0 := by
  intro hz
  have hh : h = (q : ℤ) • e (1, 0) := by
    rw [← he, lattice_addEquiv_coordinates]
    simp
  have ht : t = (e.symm t).1 • e (1, 0) := by
    calc
      t = e (e.symm t) := (e.apply_symm_apply t).symm
      _ = _ := by rw [lattice_addEquiv_coordinates, hz]; simp
  apply hnonparallel
  rw [hh, ht]
  change ((q : ℤ) * (e (1, 0)).1) * ((e.symm t).1 * (e (1, 0)).2) =
    ((q : ℤ) * (e (1, 0)).2) * ((e.symm t).1 * (e (1, 0)).1)
  ring

end Nivat
