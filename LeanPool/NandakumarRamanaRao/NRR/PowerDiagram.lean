/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import LeanPool.NandakumarRamanaRao.NRR.PowerDiagram.Defs
public import LeanPool.NandakumarRamanaRao.NRR.PowerDiagram.CellAlgebra
public import LeanPool.NandakumarRamanaRao.NRR.PowerDiagram.CellGeometry
public import LeanPool.NandakumarRamanaRao.NRR.PowerDiagram.CellOverlap
public import LeanPool.NandakumarRamanaRao.NRR.PowerDiagram.BodyCells
public import LeanPool.NandakumarRamanaRao.NRR.PowerDiagram.BodyCellPartition
public import LeanPool.NandakumarRamanaRao.NRR.PowerDiagram.CellAreaContinuityWeights
public import LeanPool.NandakumarRamanaRao.NRR.PowerDiagram.CellAreaVector

/-!
# `NRR.PowerDiagram` — weighted Voronoi / power diagrams

This public aggregator exports power-distance definitions, cell geometry, null-overlap results,
body-restricted cells, partition properties, fixed-site continuity of cell area in the weights,
and the finite area vector.

The proved continuity API is intentionally fixed-site: `continuous_bodyCellArea_weights` and
`continuous_areaVec_weights` vary the weights while the distinct sites remain fixed. General joint
continuity in moving sites and weights is not claimed.
-/

@[expose] public section

open NRR NRR.Geometry NRR.Geometry.ConvexBody MeasureTheory

namespace NRR.PowerDiagram

variable {n : ℕ}

/-- **Fixed-site weight-continuity of the restricted power-cell area** (public wrapper).

For fixed sites `s` that are pairwise distinct from `s i` (`hs`), the restricted cell area
`w ↦ bodyCellArea K s w i` is continuous in the weights. This is a one-line renaming of the
proved theorem `continuous_bodyCellArea_weights`.

Only fixed-site continuity in the weights is exposed. Joint continuity in sites and weights is
not claimed, and the nondegeneracy hypothesis `hs` is necessary. -/
theorem continuous_cell_area_weights
    (K : Geometry.ConvexBody Plane) (s : Fin n → Plane) (i : Fin n)
    (hs : ∀ j, j ≠ i → s j ≠ s i) :
    Continuous fun w : Fin n → ℝ => bodyCellArea K s w i :=
  continuous_bodyCellArea_weights K s i hs

end NRR.PowerDiagram
