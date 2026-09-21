/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import Mathlib.Tactic
import LeanPool.NandakumarRamanaRao.NRR.PowerDiagram.BodyCells
import LeanPool.NandakumarRamanaRao.NRR.EMP.NormalizedWeightSelection
import LeanPool.NandakumarRamanaRao.NRR.EMP.PowerCellPositiveArea

/-!
# `NRR.EMP.PowerPartitionPieces` — equal‑area power cells as convex bodies

Given a configuration `s : Config n` of pairwise‑distinct sites in a convex body `K` with
`0 < K.area` and `0 < n`, we bundle each restricted power (Laguerre) cell of the **canonical
normalized equal‑area weight** `EMP.normalizedWeight` as a `Geometry.ConvexBody`.

Nonempty interior — required to form a `ConvexBody` — is supplied by the theorem
`PowerDiagram.bodyCellSet_interior_nonempty_of_equalArea`, using that the normalized weight is
equal‑area (`EMP.normalizedWeight_isEqualArea`).

## Public API

* `EMP.powerPartitionPiece` — the `i`‑th equal‑area restricted power cell bundled as a
 convex body.
* `EMP.powerPartitionPiece_carrier` — its carrier is the restricted cell set.
* `EMP.powerPartitionPiece_area` — its area equals the set‑level `bodyCellArea`.
* `EMP.powerPartitionPiece_area_eq` — each piece has area exactly `K.area / n`.

The full partition (disjointness / covering of `K`) is out of scope here.
-/

open NRR NRR.Geometry MeasureTheory

namespace NRR

variable {n : ℕ}

/-- **Equal‑area power‑cell piece.** The `i`‑th restricted power cell of the canonical
normalized equal‑area weight `EMP.normalizedWeight K s.pts hn s.injective_pts`, bundled as a
`Geometry.ConvexBody`. Nonempty interior is provided by
`PowerDiagram.bodyCellSet_interior_nonempty_of_equalArea` (the existing theorem). -/
noncomputable def EMP.powerPartitionPiece
    (K : Geometry.ConvexBody Plane) (s : Config n) (hn : 0 < n)
    (hK : 0 < K.area) (i : Fin n) : Geometry.ConvexBody Plane :=
  PowerDiagram.bodyCellBody K s.pts
    (EMP.normalizedWeight K s.pts hn s.injective_pts)
    i
    (PowerDiagram.bodyCellSet_interior_nonempty_of_equalArea K s.pts
      (EMP.normalizedWeight K s.pts hn s.injective_pts) hn hK
      (EMP.normalizedWeight_isEqualArea K s.pts hn s.injective_pts) i)

/-- The carrier of the equal‑area power‑cell piece is the restricted cell set of the normalized
weight. -/
@[simp] theorem EMP.powerPartitionPiece_carrier
    (K : Geometry.ConvexBody Plane) (s : Config n) (hn : 0 < n)
    (hK : 0 < K.area) (i : Fin n) :
    (EMP.powerPartitionPiece K s hn hK i : Set Plane) =
      PowerDiagram.bodyCellSet K s.pts
        (EMP.normalizedWeight K s.pts hn s.injective_pts) i := rfl

/-- The area of the equal‑area power‑cell piece equals the set‑level `bodyCellArea` of the
normalized weight. -/
theorem EMP.powerPartitionPiece_area
    (K : Geometry.ConvexBody Plane) (s : Config n) (hn : 0 < n)
    (hK : 0 < K.area) (i : Fin n) :
    (EMP.powerPartitionPiece K s hn hK i).area =
      PowerDiagram.bodyCellArea K s.pts
        (EMP.normalizedWeight K s.pts hn s.injective_pts) i := rfl

/-- **Equal area.** Each equal‑area power‑cell piece has area exactly the average `K.area / n`,
because the normalized weight is an equal‑area weight
(`EMP.normalizedWeight_isEqualArea`). -/
theorem EMP.powerPartitionPiece_area_eq
    (K : Geometry.ConvexBody Plane) (s : Config n) (hn : 0 < n)
    (hK : 0 < K.area) (i : Fin n) :
    (EMP.powerPartitionPiece K s hn hK i).area = K.area / n := by
  rw [EMP.powerPartitionPiece_area]
  exact EMP.normalizedWeight_isEqualArea K s.pts hn s.injective_pts i

end NRR
