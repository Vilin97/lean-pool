/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import Mathlib.Algebra.Order.Star.Real
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic
import LeanPool.NandakumarRamanaRao.NRR.PowerDiagram.Defs
import LeanPool.NandakumarRamanaRao.NRR.PowerDiagram.CellAlgebra
import LeanPool.NandakumarRamanaRao.NRR.PowerDiagram.CellGeometry
import LeanPool.NandakumarRamanaRao.NRR.HalfSpace

/-!
# `NRR.PowerDiagram.CellOverlap` — null overlap of distinct power cells

Two distinct **nondegenerate** power (Laguerre) cells overlap only on the radical hyperplane
(bisector) of the two sites, and this overlap is Lebesgue‑null; consequently their interiors
are disjoint.

The nondegeneracy hypothesis is `sepNormal s i j ≠ 0`, i.e. `s i ≠ s j` (the two sites are
distinct). Without it the theorem is *false*: if `s i = s j` and `w i = w j` then the two
cells coincide and their overlap has positive volume.

* `cell_inter_subset_bisector` — the overlap of two cells is contained in the bisector
 hyperplane `{x | ⟪sepNormal s i j, x⟫ = sepOffset s w i j}`.
* `cell_inter_null` — the overlap of two distinct nondegenerate cells is Lebesgue‑null.
* `interior_cell_disjoint` — distinct nondegenerate cells have disjoint interiors.

The ambient type is the library alias `E2 = Geometry.Plane = EuclideanSpace ℝ (Fin 2)`
(this is the `Plane` referred to in the design).
-/

open NRR MeasureTheory
open scoped RealInnerProductSpace

namespace NRR.PowerDiagram

variable {n : ℕ}

/-- The overlap of the power cells of `i` and `j` is contained in the radical (bisector)
hyperplane `{x | ⟪sepNormal s i j, x⟫ = sepOffset s w i j}`: on the overlap the two power
distances are equal (each `≤` the other), which is exactly membership in the hyperplane. -/
theorem cell_inter_subset_bisector (s : Fin n → E2) (w : Fin n → ℝ) {i j : Fin n} :
    cell s w i ∩ cell s w j ⊆
      {x : E2 | ⟪sepNormal s i j, x⟫ = sepOffset s w i j} := by
  intro x hx;
  simp_all +decide [ cell, powerDist, sepNormal, sepOffset ];
  have := hx.1 j; have := hx.2 i; norm_num [ EuclideanSpace.norm_eq, Real.sq_sqrt <| add_nonneg ( sq_nonneg _ ) ( sq_nonneg _ ) ] at *;
  norm_num [ two_smul, inner ]; linarith!;

/-- Pairwise overlaps of distinct nondegenerate cells are Lebesgue‑null: the overlap lies in a
hyperplane with nonzero normal, which is null. -/
theorem cell_inter_null (s : Fin n → E2) (w : Fin n → ℝ) {i j : Fin n}
    (hij : sepNormal s i j ≠ 0) :
    volume (cell s w i ∩ cell s w j) = 0 := by
  convert MeasureTheory.measure_mono_null ( cell_inter_subset_bisector s w ) ( NRR.Halfspace.hyperplane_null hij ( sepOffset s w i j ) ) using 1

/-- Distinct nondegenerate power cells have disjoint interiors: their intersection is an open
set contained in a null hyperplane, hence empty. -/
theorem interior_cell_disjoint (s : Fin n → E2) (w : Fin n → ℝ) {i j : Fin n}
    (hij : sepNormal s i j ≠ 0) :
    Disjoint (interior (cell s w i)) (interior (cell s w j)) := by
  have h_interior_subset : interior (cell s w i) ∩ interior (cell s w j) ⊆ {x : E2 | ⟪sepNormal s i j, x⟫ = sepOffset s w i j} := by
    exact Set.Subset.trans ( Set.inter_subset_inter interior_subset interior_subset ) ( cell_inter_subset_bisector s w );
  by_contra h_nonempty_interior;
  obtain ⟨x, hx⟩ : ∃ x, x ∈ interior (cell s w i) ∩ interior (cell s w j) := by
    exact Set.not_disjoint_iff.mp h_nonempty_interior;
  have h_open : IsOpen (interior (cell s w i) ∩ interior (cell s w j)) := by
    exact IsOpen.inter ( isOpen_interior ) ( isOpen_interior );
  have h_measure_zero : MeasureTheory.volume (interior (cell s w i) ∩ interior (cell s w j)) = 0 := by
    exact MeasureTheory.measure_mono_null h_interior_subset ( NRR.Halfspace.hyperplane_null hij _ );
  exact absurd h_measure_zero ( by exact ne_of_gt ( h_open.measure_pos ( MeasureTheory.MeasureSpace.volume ) ⟨ x, hx ⟩ ) )

end NRR.PowerDiagram
