/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import Mathlib.Tactic
import LeanPool.NandakumarRamanaRao.NRR.ConvexBody
import LeanPool.NandakumarRamanaRao.NRR.BodySpace.AreaRigidity
import LeanPool.NandakumarRamanaRao.NRR.EMP.EqualAreaWeights
import LeanPool.NandakumarRamanaRao.NRR.EMP.PowerCellPositiveArea
import LeanPool.NandakumarRamanaRao.NRR.PowerDiagram.BodyCells

/-!
# `NRR.EMP.EqualAreaWeightCellRigidity` — maximal weight differences fix a cell

Let `w` and `w'` be two weight vectors and put `d i = w' i - w i`.  If `d i` is maximal,
then the `i`-th power cell for `w` is contained in the `i`-th power cell for `w'`.  If both
weight vectors give the same positive prescribed cell area, compact-convex area rigidity
upgrades this inclusion to equality.

This is the elementary geometric core of uniqueness up to an additive constant.  The remaining
global uniqueness step is to propagate equality of the maximal difference across the cell
adjacency graph.
-/

open NRR NRR.Geometry MeasureTheory

namespace NRR

variable {n : ℕ}

namespace PowerDiagram

/-- If `w' i - w i` is maximal among all coordinate differences, the `i`-th restricted power
cell for `w` is contained in the corresponding cell for `w'`. -/
theorem bodyCellSet_subset_of_weightDifference_max
    (K : Geometry.ConvexBody Plane) (s : Fin n → Plane)
    (w w' : Fin n → ℝ) (i : Fin n)
    (hmax : ∀ j, w' j - w j ≤ w' i - w i) :
    PowerDiagram.bodyCellSet K s w i ⊆ PowerDiagram.bodyCellSet K s w' i := by
  intro x hx
  rcases hx with ⟨hxK, hxcell⟩
  refine ⟨hxK, ?_⟩
  rw [PowerDiagram.mem_cell] at hxcell ⊢
  intro j
  have hij := hxcell j
  have hd := hmax j
  simp only [PowerDiagram.powerDist] at hij ⊢
  linarith

/-- For two equal-area weight vectors, a coordinate at which `w' - w` is maximal has exactly
the same restricted power cell for both vectors. -/
theorem bodyCellSet_eq_of_equalArea_of_weightDifference_max
    (K : Geometry.ConvexBody Plane) (s : Fin n → Plane)
    (hn : 0 < n)
    {w w' : Fin n → ℝ}
    (hw : EMP.IsEqualAreaWeight K s w)
    (hw' : EMP.IsEqualAreaWeight K s w')
    (i : Fin n)
    (hmax : ∀ j, w' j - w j ≤ w' i - w i) :
    PowerDiagram.bodyCellSet K s w i = PowerDiagram.bodyCellSet K s w' i := by
  have hsub := PowerDiagram.bodyCellSet_subset_of_weightDifference_max K s w w' i hmax
  by_contra hne
  have hstrict :
      PowerDiagram.bodyCellSet K s w i ⊂ PowerDiagram.bodyCellSet K s w' i :=
    hsub.ssubset_of_ne hne
  have hK : 0 < K.area :=
    (NRR.SolidConvexBody.ofConvexBody K).area_pos
  have hInt :
      (interior (PowerDiagram.bodyCellSet K s w' i)).Nonempty :=
    PowerDiagram.bodyCellSet_interior_nonempty_of_equalArea K s w' hn hK hw' i
  have hlt := NRR.measure_lt_of_compact_convex_ssubset
    (PowerDiagram.bodyCellSet_isCompact K s w i)
    (PowerDiagram.bodyCellSet_isCompact K s w' i)
    (PowerDiagram.bodyCellSet_convex K s w' i)
    hstrict hInt
  have harea :
      (volume (PowerDiagram.bodyCellSet K s w i)).toReal =
        (volume (PowerDiagram.bodyCellSet K s w' i)).toReal := by
    change PowerDiagram.bodyCellArea K s w i = PowerDiagram.bodyCellArea K s w' i
    calc
      PowerDiagram.bodyCellArea K s w i = K.area / (n : ℝ) := hw i
      _ = PowerDiagram.bodyCellArea K s w' i := (hw' i).symm
  exact (ne_of_lt hlt) harea

end PowerDiagram

end NRR
