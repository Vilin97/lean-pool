/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import LeanPool.NandakumarRamanaRao.NRR.Partition.ConvexPartition
public import LeanPool.NandakumarRamanaRao.NRR.Partition.PerimeterVector

/-!
# `NRR.FairPartition.Predicates` — the public fair-partition predicate

This module fixes the single, public **fair partition** predicate used by the final
Nandakumar–Ramana Rao assembly. A convex partition is *fair* when

* **all pieces have equal area** (`ConvexPartition.IsEqualArea`), and
* **all pieces have equal perimeter** (`ConvexPartition.HasEqualPerimeter`).

Both underlying predicates already exist and are reused unchanged:

* `ConvexPartition.IsEqualArea` — from `NRR.Partition.ConvexPartition`;
* `ConvexPartition.HasEqualPerimeter` — from `NRR.Partition.PerimeterVector`.

No new partition structure is introduced and `ConvexPartition` is not redefined.

## API

* `ConvexPartition.IsFair` — the fair-partition predicate (a conjunction of the two above).
* `ConvexPartition.IsFair.equalArea` — projection to the equal-area component.
* `ConvexPartition.IsFair.equalPerimeter` — projection to the equal-perimeter component.
* `ConvexPartition.isFair_iff` — unfolding lemma exposing the conjunction.
* `ConvexPartition.IsFair.mk'` — build `IsFair` from the two components.
-/

@[expose] public section

namespace NRR

namespace ConvexPartition

variable {K : Body} {n : ℕ}

/-- A **fair** partition: all pieces have equal area and all pieces have equal perimeter. -/
def IsFair (P : ConvexPartition K n) : Prop :=
  P.IsEqualArea ∧ P.HasEqualPerimeter

/-- Unfolding lemma: `IsFair` is exactly the conjunction of equal area and equal perimeter. -/
theorem isFair_iff {P : ConvexPartition K n} :
    P.IsFair ↔ P.IsEqualArea ∧ P.HasEqualPerimeter := Iff.rfl

/-- A fair partition has all pieces of equal area. -/
theorem IsFair.equalArea {P : ConvexPartition K n} (h : P.IsFair) : P.IsEqualArea := h.1

/-- A fair partition has all pieces of equal perimeter. -/
theorem IsFair.equalPerimeter {P : ConvexPartition K n} (h : P.IsFair) :
    P.HasEqualPerimeter := h.2

/-- Build a fair partition from equal area and equal perimeter. -/
theorem IsFair.mk' {P : ConvexPartition K n}
    (hA : P.IsEqualArea) (hP : P.HasEqualPerimeter) : P.IsFair := ⟨hA, hP⟩

end ConvexPartition

end NRR
