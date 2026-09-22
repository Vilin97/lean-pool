/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import Mathlib.Tactic
import LeanPool.NandakumarRamanaRao.NRR.Partition.ConvexPartition
import LeanPool.NandakumarRamanaRao.NRR.PowerDiagram.BodyCellPartition
import LeanPool.NandakumarRamanaRao.NRR.EMP.PowerPartitionPieces

/-!
# `NRR.EMP.PartitionFromPowerDiagram` — the canonical equal‑area power partition

Given a configuration `s : Config n` of pairwise‑distinct sites inside a convex body `K` with
`0 < K.area` and `0 < n`, this module assembles the equal‑area restricted power (Laguerre) cells
`EMP.powerPartitionPiece` into an honest `ConvexPartition K n`.

The three partition obligations are discharged from the set‑level power‑diagram API:

* `subset` — `PowerDiagram.bodyCellSet_subset`;
* `covers` — `PowerDiagram.iUnion_bodyCellSet` (needs `[NeZero n]`, supplied from `hn`);
* `nullOverlap` — `PowerDiagram.bodyCellSet_inter_null`, using site injectivity from `Config`.

## Public API

* `EMP.powerPartition` — the canonical equal‑area power partition of `K`.
* `EMP.powerPartition_piece_carrier` — the carrier of the `i`‑th piece is the restricted cell set
 of the canonical normalized equal‑area weight.
* `EMP.powerPartition_isEqualArea` — every piece has the same area (`= K.area / n`).
* `EMP.powerPartition_covers` — the pieces cover `K`.
* `EMP.powerPartition_nullOverlap` — distinct pieces overlap only on a null set.
-/

open NRR NRR.Geometry MeasureTheory

namespace NRR

variable {n : ℕ}

/-- **Canonical equal‑area power partition.** The restricted power cells of the canonical
normalized equal‑area weight `EMP.normalizedWeight K s.pts hn s.injective_pts`, bundled as a
`ConvexPartition K n`. Covering comes from `PowerDiagram.iUnion_bodyCellSet`; null overlap of
distinct pieces comes from `PowerDiagram.bodyCellSet_inter_null` via `Config` site injectivity. -/
noncomputable def EMP.powerPartition
    (K : Geometry.ConvexBody Plane) (s : Config n) (hn : 0 < n)
    (hK : 0 < K.area) : ConvexPartition K n where
  piece i := EMP.powerPartitionPiece K s hn hK i
  subset i := by
    simpa only [EMP.powerPartitionPiece_carrier] using
      PowerDiagram.bodyCellSet_subset K s.pts
        (EMP.normalizedWeight K s.pts hn s.injective_pts) i
  covers := by
    let : NeZero n := ⟨hn.ne'⟩
    have h := PowerDiagram.iUnion_bodyCellSet K s.pts
      (EMP.normalizedWeight K s.pts hn s.injective_pts)
    exact h.ge.trans_eq' rfl
  nullOverlap i j hij := by
    simpa only [EMP.powerPartitionPiece_carrier] using
      PowerDiagram.bodyCellSet_inter_null K s.pts
        (EMP.normalizedWeight K s.pts hn s.injective_pts) s.injective_pts hij

/-- The carrier of the `i`‑th piece of the canonical equal‑area power partition is the restricted
power cell set of the canonical normalized equal‑area weight. -/
theorem EMP.powerPartition_piece_carrier
    (K : Geometry.ConvexBody Plane) (s : Config n) (hn : 0 < n)
    (hK : 0 < K.area) (i : Fin n) :
    ((EMP.powerPartition K s hn hK).piece i : Set Plane) =
      PowerDiagram.bodyCellSet K s.pts
        (EMP.normalizedWeight K s.pts hn s.injective_pts) i := rfl

/-- **Equal area.** Every piece of the canonical equal‑area power partition has the same area
(each equal to the average `K.area / n`), because the underlying normalized weight is an
equal‑area weight. -/
theorem EMP.powerPartition_isEqualArea
    (K : Geometry.ConvexBody Plane) (s : Config n) (hn : 0 < n) (hK : 0 < K.area) :
    (EMP.powerPartition K s hn hK).IsEqualArea := by
  intro i j
  change (EMP.powerPartitionPiece K s hn hK i).area
    = (EMP.powerPartitionPiece K s hn hK j).area
  rw [EMP.powerPartitionPiece_area_eq K s hn hK i,
    EMP.powerPartitionPiece_area_eq K s hn hK j]

/-- **Cover.** The pieces of the canonical equal‑area power partition cover `K`. -/
theorem EMP.powerPartition_covers
    (K : Geometry.ConvexBody Plane) (s : Config n) (hn : 0 < n) (hK : 0 < K.area) :
    (K : Set Plane) ⊆ ⋃ i, ((EMP.powerPartition K s hn hK).piece i : Set Plane) :=
  (EMP.powerPartition K s hn hK).covers

/-- **Null overlap.** Distinct pieces of the canonical equal‑area power partition overlap only on
a Lebesgue‑null set. -/
theorem EMP.powerPartition_nullOverlap
    (K : Geometry.ConvexBody Plane) (s : Config n) (hn : 0 < n) (hK : 0 < K.area)
    (i j : Fin n) (hij : i ≠ j) :
    volume (((EMP.powerPartition K s hn hK).piece i : Set Plane) ∩
      ((EMP.powerPartition K s hn hK).piece j : Set Plane)) = 0 :=
  (EMP.powerPartition K s hn hK).nullOverlap i j hij

end NRR
