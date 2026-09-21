/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.EMP.VariableBody.Children
import LeanPool.NandakumarRamanaRao.NRR.EMP.PartitionFromPowerDiagram

/-!
# `NRR.EMP.VariableBody.Partition` — the variable-body equal-area power partition

For a compact metric parameter space `X` carrying a continuous site family
`sites : SiteFamily X n`, a positive lower area `A`, and `0 < n`, this module exposes the canonical
equal-area power partition of each variable solid body `solidBody hA z.1` as a thin wrapper around
`EMP.powerPartition`. Its pieces are propositionally identified with the continuously varying child
bodies `child sites hA hn z i` packaged in `Children.lean`.

Continuity of the family is carried entirely by `child` (and its continuity results); the
dependent `partition` field is *not* asserted to be continuous, and no topology is placed on
`ConvexPartition (solidBody hA z.1) n`.

* `partition` — the canonical equal-area power partition of the variable solid body.
* `partition_isEqualArea`, `partition_covers`, `partition_nullOverlap` — the three partition facts,
  reused verbatim from the fixed-body power-partition API.
* `partition_piece_carrier_eq_child` — each piece's carrier is exactly the corresponding child body.
* `partition_piece_area_eq` — each piece has area `z.1.body.area / n`.
* `Witness` / `witness` — the partition packaged together with its children and all partition facts,
  as consumed by the prime-refinement layer.
-/

open NRR NRR.Geometry NRR.Geometry.ConvexBody MeasureTheory

namespace NRR.EMP.VariableBody

variable {X : Type*} [MetricSpace X] [CompactSpace X] {n : ℕ}
variable {K : Geometry.ConvexBody Plane} {A : ℝ}
variable (sites : SiteFamily X n) (hA : 0 < A) (hn : 0 < n)

omit [CompactSpace X]

/-- The **canonical equal-area power partition** of the variable solid body `solidBody hA z.1`,
computed with the site configuration `sites z.2`. A thin wrapper around `EMP.powerPartition`. -/
noncomputable def partition
    (z : BodySpace K A × X) :
    ConvexPartition (solidBody hA z.1) n :=
  EMP.powerPartition (solidBody hA z.1) (sites z.2) hn
    (BodySpace.area_pos hA z.1)

/-- **Equal area.** Every piece of the variable partition has the same area. -/
theorem partition_isEqualArea
    (z : BodySpace K A × X) :
    (partition sites hA hn z).IsEqualArea :=
  EMP.powerPartition_isEqualArea (solidBody hA z.1) (sites z.2) hn
    (BodySpace.area_pos hA z.1)

/-- **Cover.** The pieces of the variable partition cover the variable solid body. -/
theorem partition_covers
    (z : BodySpace K A × X) :
    (solidBody hA z.1 : Set Plane) ⊆
      ⋃ i, ((partition sites hA hn z).piece i : Set Plane) :=
  EMP.powerPartition_covers (solidBody hA z.1) (sites z.2) hn
    (BodySpace.area_pos hA z.1)

/-- **Null overlap.** Distinct pieces of the variable partition overlap only on a Lebesgue-null
set. -/
theorem partition_nullOverlap
    (z : BodySpace K A × X)
    (i j : Fin n) (hij : i ≠ j) :
    volume (((partition sites hA hn z).piece i : Set Plane) ∩
      ((partition sites hA hn z).piece j : Set Plane)) = 0 :=
  EMP.powerPartition_nullOverlap (solidBody hA z.1) (sites z.2) hn
    (BodySpace.area_pos hA z.1) i j hij

variable (z : BodySpace K A × X)

/-- **Piece compatibility.** The carrier of the `i`-th piece of the variable partition is exactly
the carrier of the `i`-th canonical child body, both being the restricted power cell of the
canonical normalized equal-area weight. -/
theorem partition_piece_carrier_eq_child
    (i : Fin n) :
    ((partition sites hA hn z).piece i : Set Plane) =
      ((child sites hA hn z i).body : Set Plane) :=
  rfl

/-- **Piece area.** Each piece of the variable partition has area `z.1.body.area / n`. -/
theorem partition_piece_area_eq
    (i : Fin n) :
    ((partition sites hA hn z).piece i).area =
      z.1.body.area / (n : ℝ) := by
  have h := EMP.powerPartitionPiece_area_eq (solidBody hA z.1) (sites z.2) hn
    (BodySpace.area_pos hA z.1) i
  simpa [partition, EMP.powerPartition, solidBody_area] using h

/-- The **partition witness** at a parameter `z`: the canonical variable-body power partition
together with its continuously varying children and all the partition facts a refinement step
needs. Continuity of the family is carried by the `child` field (see `continuous_child`), not by the
dependent `partition` field. -/
structure Witness
    (sites : SiteFamily X n) (hA : 0 < A) (hn : 0 < n)
    (z : BodySpace K A × X) where
  /-- The canonical equal-area power partition of the variable solid body. -/
  partition : ConvexPartition (solidBody hA z.1) n
  /-- The continuously varying child bodies, one per piece. -/
  child : Fin n → BodySpace K (A / (n : ℝ))
  /-- Each piece agrees, as a set, with the corresponding child body. -/
  piece_eq :
    ∀ i, (partition.piece i : Set Plane) = ((child i).body : Set Plane)
  /-- All pieces have equal area. -/
  equalArea : partition.IsEqualArea
  /-- The pieces cover the variable solid body. -/
  covers :
    ((solidBody hA z.1 : Geometry.ConvexBody Plane) : Set Plane) ⊆
      ⋃ i, (partition.piece i : Set Plane)
  /-- Distinct pieces overlap only on a null set. -/
  nullOverlap :
    ∀ i j, i ≠ j →
      volume ((partition.piece i : Set Plane) ∩
        (partition.piece j : Set Plane)) = 0

/-- The **canonical partition witness** at `z`, built from the existing variable-body partition and
its canonical children. No partition proof is duplicated: every field reuses the corresponding
`partition_*` fact. -/
noncomputable def witness
    (z : BodySpace K A × X) :
    Witness sites hA hn z where
  partition := partition sites hA hn z
  child i := child sites hA hn z i
  piece_eq i := partition_piece_carrier_eq_child sites hA hn z i
  equalArea := partition_isEqualArea sites hA hn z
  covers := partition_covers sites hA hn z
  nullOverlap i j hij := partition_nullOverlap sites hA hn z i j hij

end NRR.EMP.VariableBody
