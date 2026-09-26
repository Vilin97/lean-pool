/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import LeanPool.NandakumarRamanaRao.NRR.ConvexBody

/-!
# `NRR.Partition.ConvexPartition` — the shared convex‑partition structure

This module defines the single, shared `ConvexPartition` structure used by all later
fair‑partition modules, together with the basic cover/subset/area API needed before area
additivity can be developed.

The structure is stated over the **unified public body type** `NRR.Body`, which is a
definitional alias of `NRR.Geometry.ConvexBody NRR.E2 = ConvexBody Plane`
(`E2 = Geometry.Plane`). No independent convex‑body API is introduced here.

## Hypotheses

The partition records exactly the data needed for **finite measure additivity** of the area
functional:

* `subset` — each piece is contained in `K`;
* `covers` — the pieces cover `K`;
* `nullOverlap` — distinct pieces overlap only on a Lebesgue‑null set.

Strict (set‑theoretic) disjointness is deliberately *not* required: null overlaps are exactly
what finite measure additivity needs and what power/Voronoi partitions actually satisfy.

## API

* `ConvexPartition.IsEqualArea` — all pieces have equal area.
* `ConvexPartition.iUnion_piece_eq` — the pieces union to `K` (as sets).
* `ConvexPartition.piece_subset` — each piece is a subset of `K`.
* `ConvexPartition.piece_area_nonneg` — each piece has nonnegative area.

Area additivity itself is intentionally *not* proved here.
-/

@[expose] public section

open MeasureTheory

namespace NRR

/-- A **convex partition** of a body `K` into `n` convex pieces (convex bodies) that cover
`K` and overlap only on null sets.

The body type `Body` is the unified public alias of `ConvexBody Plane`
(`Body = Geometry.ConvexBody E2`, `E2 = Geometry.Plane`). -/
structure ConvexPartition (K : Body) (n : ℕ) where
  /-- The `i`‑th convex piece. -/
  piece : Fin n → Body
  /-- Each piece is contained in `K`. -/
  subset : ∀ i, (piece i : Set E2) ⊆ (K : Set E2)
  /-- The pieces cover `K`. -/
  covers : (K : Set E2) ⊆ ⋃ i, (piece i : Set E2)
  /-- Distinct pieces overlap only on a null set. -/
  nullOverlap : ∀ i j, i ≠ j → volume ((piece i : Set E2) ∩ (piece j : Set E2)) = 0

namespace ConvexPartition

/-- All pieces have equal area. -/
def IsEqualArea {K : Body} {n : ℕ} (P : ConvexPartition K n) : Prop :=
  ∀ i j, (P.piece i).area = (P.piece j).area

/-- The pieces of a convex partition union (as sets) to the whole body `K`. -/
theorem iUnion_piece_eq {K : Body} {n : ℕ} (P : ConvexPartition K n) :
    ⋃ i, (P.piece i : Set E2) = (K : Set E2) :=
  Set.Subset.antisymm (Set.iUnion_subset P.subset) P.covers

/-- Each piece of a convex partition is a subset of the ambient body `K`. -/
theorem piece_subset {K : Body} {n : ℕ} (P : ConvexPartition K n) (i : Fin n) :
    (P.piece i : Set E2) ⊆ (K : Set E2) :=
  P.subset i

/-- Each piece of a convex partition has nonnegative area. -/
theorem piece_area_nonneg {K : Body} {n : ℕ} (P : ConvexPartition K n) (i : Fin n) :
    0 ≤ (P.piece i).area :=
  (P.piece i).area_nonneg

end ConvexPartition

end NRR
