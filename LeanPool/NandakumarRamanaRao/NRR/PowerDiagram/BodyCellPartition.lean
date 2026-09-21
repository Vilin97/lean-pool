/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import Mathlib
import LeanPool.NandakumarRamanaRao.NRR.ConvexBody
import LeanPool.NandakumarRamanaRao.NRR.PowerDiagram.Defs
import LeanPool.NandakumarRamanaRao.NRR.PowerDiagram.CellGeometry
import LeanPool.NandakumarRamanaRao.NRR.PowerDiagram.CellOverlap
import LeanPool.NandakumarRamanaRao.NRR.PowerDiagram.BodyCells

/-!
# `NRR.PowerDiagram.BodyCellPartition` — partition properties of restricted cells

The restricted power (Laguerre) cells `bodyCellSet K s w i = (K : Set Plane) ∩ cell s w i`
form a finite almost‑disjoint cover of a convex body `K`:

* `bodyCellSet_subset` — each restricted cell is contained in `K`.
* `iUnion_bodyCellSet` — the restricted cells cover `K` (needs `[NeZero n]`: with no sites
 the union is empty while a convex body is nonempty, so the covering claim is false for
 `n = 0`).
* `bodyCellSet_inter_null` — for an injective site family, two distinct restricted cells
 overlap on a Lebesgue‑null set.

The nondegeneracy needed for the null‑overlap statement is `sepNormal s i j ≠ 0`. This is
*not* implied by `i ≠ j` alone, but it **is** implied by `Function.Injective s` together with
`i ≠ j`; the bridging lemma `sepNormal_ne_zero_of_injective` records that implication.

No nonemptiness of restricted cells is assumed, no `ConvexPartition` is bundled, and no
equal‑area properties are proved here.
-/

open NRR NRR.Geometry MeasureTheory

namespace NRR.PowerDiagram

variable {n : ℕ}

/-- A restricted power cell is contained in the body `K`. -/
theorem bodyCellSet_subset (K : Geometry.ConvexBody Plane) (s : Fin n → Plane) (w : Fin n → ℝ)
    (i : Fin n) :
    bodyCellSet K s w i ⊆ (K : Set Plane) :=
  bodyCellSet_subset_body K s w i

/-- The restricted power cells cover the body `K`. Requires at least one site (`[NeZero n]`):
the full cells cover the plane by `iUnion_cell`, so intersecting with `K` recovers `K`. -/
theorem iUnion_bodyCellSet [NeZero n] (K : Geometry.ConvexBody Plane) (s : Fin n → Plane)
    (w : Fin n → ℝ) :
    ⋃ i, bodyCellSet K s w i = (K : Set Plane) := by
  simp only [bodyCellSet_def, ← Set.inter_iUnion, iUnion_cell, Set.inter_univ]

/-- For an injective family of sites, distinct indices give a nonzero separating normal:
`sepNormal s i j = 2 • (sⱼ - sᵢ)` is nonzero because `sᵢ ≠ sⱼ`. -/
theorem sepNormal_ne_zero_of_injective (s : Fin n → E2) (hs : Function.Injective s)
    {i j : Fin n} (hij : i ≠ j) :
    sepNormal s i j ≠ 0 :=
  smul_ne_zero (by norm_num) (sub_ne_zero.mpr fun h => hij (hs h).symm)

/-- **Null overlap.** For an injective site family, the overlap of two distinct restricted power
cells is Lebesgue‑null: it embeds into the overlap of the full (nondegenerate) cells, which is
null by `cell_inter_null`. -/
theorem bodyCellSet_inter_null (K : Geometry.ConvexBody Plane) (s : Fin n → Plane) (w : Fin n → ℝ)
    (hs : Function.Injective s) {i j : Fin n} (hij : i ≠ j) :
    volume (bodyCellSet K s w i ∩ bodyCellSet K s w j) = 0 := by
  refine measure_mono_null ?_ (cell_inter_null s w (sepNormal_ne_zero_of_injective s hs hij))
  exact Set.inter_subset_inter Set.inter_subset_right Set.inter_subset_right

end NRR.PowerDiagram
