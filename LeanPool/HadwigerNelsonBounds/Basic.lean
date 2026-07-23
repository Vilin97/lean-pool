/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.ZMod.Basic

/-!
# Plane unit-distance graph and triangular lattice

This module defines the Euclidean plane graph and the lattice geometry used by
the seven-color construction.
-/

namespace HadwigerNelsonBounds

open SimpleGraph

/-- The plane R² as a 2-dimensional Euclidean space. -/
abbrev R2 : Type := EuclideanSpace ℝ (Fin 2)

/-- The unit-distance graph on R²: vertices are points of the plane, with
    an edge between `p` and `q` iff `dist p q = 1`. Built via
    `SimpleGraph.fromRel`, which automatically symmetrizes the relation
    and removes self-loops (`dist p p = 0 ≠ 1`, so this is harmless). -/
def unitDistanceGraph : SimpleGraph R2 :=
  SimpleGraph.fromRel (fun p q => dist p q = 1)

/-- Adjacency unfolds to: distinct points at distance exactly 1. -/
@[simp] lemma unitDistanceGraph_adj (p q : R2) :
    unitDistanceGraph.Adj p q ↔ p ≠ q ∧ (dist p q = 1 ∨ dist q p = 1) := by
  unfold unitDistanceGraph
  exact SimpleGraph.fromRel_adj _ _ _

/-! ### Isbell hexagonal-tiling 7-coloring -/

/-- Lattice basis spacing. Any value in the interval
    `(1/(√7 − 2/√3), √3/2) ≈ (0.671, 0.866)` is geometrically valid;
    we pick the clean rational `3/4`. -/
noncomputable def isbellLatticeStep : ℝ := 3 / 4

/-- The triangular-lattice point at integer coords `(i, j)`:
    `i · (a, 0) + j · (a/2, a·√3/2)`. -/
noncomputable def isbellLatticePoint (i j : ℤ) : R2 :=
  WithLp.toLp 2
    ![(i : ℝ) * isbellLatticeStep + (j : ℝ) * (isbellLatticeStep / 2),
      (j : ℝ) * (isbellLatticeStep * Real.sqrt 3 / 2)]

@[simp] lemma isbellLatticePoint_zero (i j : ℤ) :
    (isbellLatticePoint i j) 0
      = (i : ℝ) * isbellLatticeStep + (j : ℝ) * (isbellLatticeStep / 2) := rfl

@[simp] lemma isbellLatticePoint_one (i j : ℤ) :
    (isbellLatticePoint i j) 1
      = (j : ℝ) * (isbellLatticeStep * Real.sqrt 3 / 2) := rfl

/-- `√3 * √3 = 3`, hoisted to file scope for use in the squared-distance
    computation. -/
lemma sqrt_three_mul_self : Real.sqrt 3 * Real.sqrt 3 = 3 :=
  Real.mul_self_sqrt (by norm_num)

/-- Squared Euclidean distance between two lattice points. -/
lemma isbellLatticePoint_dist_sq (i j i' j' : ℤ) :
    dist (isbellLatticePoint i j) (isbellLatticePoint i' j') ^ 2
      = isbellLatticeStep ^ 2 *
          (((i : ℝ) - i') ^ 2 + ((i : ℝ) - i') * ((j : ℝ) - j') + ((j : ℝ) - j') ^ 2) := by
  rw [PiLp.dist_sq_eq_of_L2]
  simp only [Fin.sum_univ_two, isbellLatticePoint_zero, isbellLatticePoint_one,
    Real.dist_eq, sq_abs]
  have hsq3 : Real.sqrt 3 * Real.sqrt 3 = 3 := sqrt_three_mul_self
  -- Use ring manipulations and the sqrt fact.
  have h0 : ((i : ℝ) * isbellLatticeStep + (j : ℝ) * (isbellLatticeStep / 2)
            - ((i' : ℝ) * isbellLatticeStep + (j' : ℝ) * (isbellLatticeStep / 2)))
          = isbellLatticeStep * (((i : ℝ) - i') + ((j : ℝ) - j') / 2) := by ring
  have h1 : ((j : ℝ) * (isbellLatticeStep * Real.sqrt 3 / 2)
            - (j' : ℝ) * (isbellLatticeStep * Real.sqrt 3 / 2))
          = isbellLatticeStep * Real.sqrt 3 / 2 * ((j : ℝ) - j') := by ring
  rw [h0, h1]
  have h0sq : (isbellLatticeStep * (((i : ℝ) - i') + ((j : ℝ) - j') / 2)) ^ 2
            = isbellLatticeStep ^ 2 *
                (((i : ℝ) - i') ^ 2 + ((i : ℝ) - i') * ((j : ℝ) - j')
                  + ((j : ℝ) - j') ^ 2 / 4) := by ring
  have h1sq : (isbellLatticeStep * Real.sqrt 3 / 2 * ((j : ℝ) - j')) ^ 2
            = isbellLatticeStep ^ 2 * (Real.sqrt 3 * Real.sqrt 3) / 4
                * ((j : ℝ) - j') ^ 2 := by ring
  rw [h0sq, h1sq, hsq3]
  ring

/-
**Voronoi covering radius (the geometric heart of (G1)).** For every
point `p ∈ R²`, some lattice point lies within distance `a/√3` of `p`.

Equivalently: the closed Voronoi cells (regular hexagons of
circumradius `a/√3`) around each lattice point cover the entire
plane.

We prove it constructively below by rounding lattice coordinates and
case-splitting on the four Voronoi cells that cover `[0, 1)²` in
lattice-coordinate parameter space.
-/

/-- Squared Euclidean distance from a point `p : R²` to a lattice point.
    Helper formula expressed directly in terms of `p 0`, `p 1`, `i`, `j`. -/
lemma dist_point_lattice_sq_cart (p : R2) (i j : ℤ) :
    dist p (isbellLatticePoint i j) ^ 2
      = (p 0 - ((i : ℝ) * isbellLatticeStep + (j : ℝ) * (isbellLatticeStep / 2))) ^ 2
        + (p 1 - (j : ℝ) * (isbellLatticeStep * Real.sqrt 3 / 2)) ^ 2 := by
  rw [PiLp.dist_sq_eq_of_L2]
  simp only [Fin.sum_univ_two, isbellLatticePoint_zero, isbellLatticePoint_one,
    Real.dist_eq, sq_abs]

/-- The Voronoi covering bound `Q(u, v) ≤ 1/3` holds in the centroid region
    of the triangle with vertices `(0,0), (1,0), (0,1)`. -/
lemma Q_le_third_origin {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (h1 : 2 * α + β ≤ 1) (h2 : α + 2 * β ≤ 1) :
    α ^ 2 + α * β + β ^ 2 ≤ 1 / 3 := by
  -- Max of α² + αβ + β² over {α,β ≥ 0, 2α+β ≤ 1, α+2β ≤ 1} is 1/3 at (1/3, 1/3).
  -- Use nlinarith with the constraint products.
  nlinarith [sq_nonneg α, sq_nonneg β, sq_nonneg (α + β),
    sq_nonneg (α - β), sq_nonneg (1 - 3*α - 3*β), sq_nonneg (3*α - 1),
    sq_nonneg (3*β - 1), sq_nonneg (3 * α + 3 * β - 2), hα, hβ, h1, h2,
    mul_nonneg hα hβ,
    mul_nonneg hα (sub_nonneg.mpr h1),
    mul_nonneg hβ (sub_nonneg.mpr h2)]

end HadwigerNelsonBounds
