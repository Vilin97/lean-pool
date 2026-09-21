/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import Mathlib.Tactic
import LeanPool.NandakumarRamanaRao.NRR.PowerDiagram.BodyCells
import LeanPool.NandakumarRamanaRao.NRR.PowerDiagram.CellAreaVector
import LeanPool.NandakumarRamanaRao.NRR.EMP.EqualAreaWeights
import LeanPool.NandakumarRamanaRao.NRR.Geometry.ConvexBody.PositiveAreaInterior

/-!
# `NRR.EMP.PowerCellPositiveArea` — positive area of equal‑area cells

If the weights `w` are equal‑area for sites `s` in a body `K` with `0 < K.area` and `0 < n`,
then every restricted power cell has strictly positive area, and hence (by the theorem `interior_nonempty_of_convex_compact_positive_area`) nonempty interior.

## Public API

* `bodyCellArea_pos_of_equalArea` — each restricted cell area is strictly positive.
* `bodyCellSet_interior_nonempty_of_equalArea` — each restricted cell has nonempty interior.

Equal area means each cell carries exactly the average area `K.area / n`; the coercion
`n : ℕ ↦ (n : ℝ)` is via `Nat.cast`, so positivity follows from `0 < K.area` and `0 < n`.
-/

open NRR NRR.Geometry MeasureTheory

namespace NRR.PowerDiagram

variable {n : ℕ}

/-- **Positive area of an equal‑area restricted power cell.** With `0 < n` and `0 < K.area`,
if the weights are equal‑area then every restricted cell has strictly positive area, equal to
the average `K.area / n`. -/
theorem bodyCellArea_pos_of_equalArea
    (K : Geometry.ConvexBody Plane) (s : Fin n → Plane) (w : Fin n → ℝ)
    (hn : 0 < n)
    (hK : 0 < K.area)
    (hw : EMP.IsEqualAreaWeight K s w)
    (i : Fin n) :
    0 < PowerDiagram.bodyCellArea K s w i := by
  have hcell : PowerDiagram.bodyCellArea K s w i = K.area / (n : ℝ) := hw i
  rw [hcell]
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  positivity

/-- **Nonempty interior of an equal‑area restricted power cell.** With `0 < n` and
`0 < K.area`, if the weights are equal‑area then every restricted cell has nonempty interior.
Uses the theorem that a compact convex planar set with positive area has nonempty
interior. -/
theorem bodyCellSet_interior_nonempty_of_equalArea
    (K : Geometry.ConvexBody Plane) (s : Fin n → Plane) (w : Fin n → ℝ)
    (hn : 0 < n)
    (hK : 0 < K.area)
    (hw : EMP.IsEqualAreaWeight K s w)
    (i : Fin n) :
    (interior (PowerDiagram.bodyCellSet K s w i)).Nonempty := by
  have harea : 0 < (volume (PowerDiagram.bodyCellSet K s w i)).toReal :=
    bodyCellArea_pos_of_equalArea K s w hn hK hw i
  exact NRR.Geometry.ConvexBody.interior_nonempty_of_convex_compact_positive_area
    (PowerDiagram.bodyCellSet_convex K s w i)
    (PowerDiagram.bodyCellSet_isCompact K s w i)
    harea

end NRR.PowerDiagram
