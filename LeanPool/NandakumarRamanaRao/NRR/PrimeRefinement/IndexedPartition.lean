/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.FairPartition.Predicates

/-!
# Finite-indexed convex partitions

The prime-refinement iteration naturally produces nested product index types.  This file provides
an index-polymorphic version of `ConvexPartition` and a canonical conversion back to the public
`Fin n`-indexed structure.
-/

open MeasureTheory

namespace NRR

/-- A convex partition indexed by an arbitrary type. Finiteness is only required when converting
back to the public `ConvexPartition` structure. -/
structure IndexedConvexPartition (K : Body) (ι : Type*) where
  /-- The convex body assigned to each index of the partition. -/
  piece : ι → Body
  subset : ∀ i, (piece i : Set E2) ⊆ (K : Set E2)
  covers : (K : Set E2) ⊆ ⋃ i, (piece i : Set E2)
  nullOverlap :
    ∀ i j, i ≠ j →
      volume ((piece i : Set E2) ∩ (piece j : Set E2)) = 0

namespace IndexedConvexPartition

variable {K L : Body} {ι κ : Type*}

/-- All indexed pieces have equal area. -/
def IsEqualArea (P : IndexedConvexPartition K ι) : Prop :=
  ∀ i j, (P.piece i).area = (P.piece j).area

/-- All indexed pieces have equal perimeter. -/
def HasEqualPerimeter (P : IndexedConvexPartition K ι) : Prop :=
  ∀ i j, (P.piece i).perimeter = (P.piece j).perimeter

/-- Regard an ordinary `Fin n`-indexed partition as an indexed partition. -/
def ofConvexPartition {n : ℕ} (P : ConvexPartition K n) :
    IndexedConvexPartition K (Fin n) where
  piece := P.piece
  subset := P.subset
  covers := P.covers
  nullOverlap := P.nullOverlap

/-- The singleton indexed partition. -/
noncomputable def singleton (K : Body) : IndexedConvexPartition K Unit where
  piece := fun _ => K
  subset := fun _ => subset_rfl
  covers := Set.subset_iUnion_of_subset () subset_rfl
  nullOverlap := by
    intro i j hij
    exact absurd (Subsingleton.elim i j) hij

/-- Change the ambient body along an equality. -/
def castBody (h : K = L) (P : IndexedConvexPartition K ι) :
    IndexedConvexPartition L ι :=
  h ▸ P


/-- Equal area is invariant under changing only the ambient body by equality. -/
theorem castBody_isEqualArea
    (h : K = L) (P : IndexedConvexPartition K ι) :
    (P.castBody h).IsEqualArea ↔ P.IsEqualArea := by
  cases h
  rfl

/-- Equal perimeter is invariant under changing only the ambient body by equality. -/
theorem castBody_hasEqualPerimeter
    (h : K = L) (P : IndexedConvexPartition K ι) :
    (P.castBody h).HasEqualPerimeter ↔ P.HasEqualPerimeter := by
  cases h
  rfl

/-- Reindex a partition along an equivalence. -/
def reindex (P : IndexedConvexPartition K ι) (e : κ ≃ ι) :
    IndexedConvexPartition K κ where
  piece i := P.piece (e i)
  subset i := P.subset (e i)
  covers := by
    intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (P.covers hx)
    exact Set.mem_iUnion.mpr ⟨e.symm i, by simpa using hi⟩
  nullOverlap := by
    intro i j hij
    exact P.nullOverlap (e i) (e j) (fun h => hij (e.injective h))

/-- Convert a finite indexed partition to the public `Fin (card ι)`-indexed partition. -/
noncomputable def toConvexPartition
    [Fintype ι] (P : IndexedConvexPartition K ι) :
    ConvexPartition K (Fintype.card ι) :=
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  { piece := fun i => P.piece (e i)
    subset := fun i => P.subset (e i)
    covers := by
      intro x hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (P.covers hx)
      exact Set.mem_iUnion.mpr ⟨e.symm i, by simpa using hi⟩
    nullOverlap := by
      intro i j hij
      exact P.nullOverlap (e i) (e j) (fun h => hij (e.injective h)) }

/-- Equal area is preserved by reindexing. -/
theorem reindex_isEqualArea
    (P : IndexedConvexPartition K ι) (e : κ ≃ ι)
    (hP : P.IsEqualArea) :
    (P.reindex e).IsEqualArea := by
  intro i j
  exact hP (e i) (e j)

/-- Equal perimeter is preserved by reindexing. -/
theorem reindex_hasEqualPerimeter
    (P : IndexedConvexPartition K ι) (e : κ ≃ ι)
    (hP : P.HasEqualPerimeter) :
    (P.reindex e).HasEqualPerimeter := by
  intro i j
  exact hP (e i) (e j)

/-- Conversion to `ConvexPartition` preserves equal area. -/
theorem toConvexPartition_isEqualArea
    [Fintype ι] (P : IndexedConvexPartition K ι)
    (hP : P.IsEqualArea) :
    P.toConvexPartition.IsEqualArea := by
  intro i j
  exact hP _ _

/-- Conversion to `ConvexPartition` preserves equal perimeter. -/
theorem toConvexPartition_hasEqualPerimeter
    [Fintype ι] (P : IndexedConvexPartition K ι)
    (hP : P.HasEqualPerimeter) :
    P.toConvexPartition.HasEqualPerimeter := by
  intro i j
  exact hP _ _

end IndexedConvexPartition

end NRR
