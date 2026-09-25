/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import Mathlib.Tactic
public import LeanPool.NandakumarRamanaRao.NRR.BodySpace.ConvexClosed

/-!
# Compactness of the fixed-parent convex subbody hyperspace

This module proves that the fixed-parent hyperspace `NRR.ConvexSubbody K` is a compact
space under its inherited Hausdorff metric.

The argument combines two ingredients on the hyperspace `TopologicalSpace.NonemptyCompacts Plane`:

* the set of nonempty compact subsets of the fixed compact parent `K` is compact
  (`NonemptyCompacts.isCompact_subsets_of_isCompact`);
* the locus of convex carriers is closed (`BodySpace.isClosed_convex_nonemptyCompacts`).

Their intersection, `convexSubbodyLocus K`, is therefore compact, and it coincides with the range
of the isometric embedding `ConvexSubbody.toNonemptyCompacts`. Transferring compactness through
that embedding yields compactness of `Set.univ` in `ConvexSubbody K`, hence the canonical
`CompactSpace` instance. No new metric, hyperspace topology, or convex-body type is introduced, and
compactness is grounded in the fixed compact parent rather than in an unproved Blaschke selection.
-/

@[expose] public section

open MeasureTheory Metric TopologicalSpace Filter Topology

open NRR.Geometry

namespace NRR

/-- The **convex subbody locus** of a fixed parent `K`: the nonempty compact planar sets that are
both contained in `K` and convex. This is the image of `ConvexSubbody K` in the Hausdorff
hyperspace. -/
def convexSubbodyLocus (K : Geometry.ConvexBody Plane) :
    Set (TopologicalSpace.NonemptyCompacts Plane) :=
  {C | (C : Set Plane) ⊆ (K : Set Plane) ∧ Convex ℝ (C : Set Plane)}

/-- The convex subbody locus is **compact**: it is the intersection of the compact set of nonempty
compact subsets of the parent `K` with the closed locus of convex carriers. -/
theorem isCompact_convexSubbodyLocus (K : Geometry.ConvexBody Plane) :
    IsCompact (convexSubbodyLocus K) := by
  have hlocus : convexSubbodyLocus K =
      {L : TopologicalSpace.NonemptyCompacts Plane | (L : Set Plane) ⊆ (K : Set Plane)}
        ∩ {C : TopologicalSpace.NonemptyCompacts Plane | Convex ℝ (C : Set Plane)} := by
    ext L; simp [convexSubbodyLocus, Set.mem_inter_iff]
  rw [hlocus]
  exact (TopologicalSpace.NonemptyCompacts.isCompact_subsets_of_isCompact K.isCompact).inter_right
    BodySpace.isClosed_convex_nonemptyCompacts

namespace ConvexSubbody

variable {K : Geometry.ConvexBody Plane}

/-- The range of the forgetful embedding `toNonemptyCompacts` is exactly the convex subbody
locus of `K`. -/
theorem range_toNonemptyCompacts (K : Geometry.ConvexBody Plane) :
    Set.range (ConvexSubbody.toNonemptyCompacts (K := K)) = convexSubbodyLocus K := by
  ext L
  constructor
  · rintro ⟨C, rfl⟩
    exact ⟨C.subset_parent, C.convex⟩
  · rintro ⟨hsub, hconv⟩
    exact ⟨⟨⟨(L : Set Plane), hconv, L.isCompact', L.nonempty'⟩, hsub⟩,
      TopologicalSpace.NonemptyCompacts.ext rfl⟩

/-- **Compactness of the subbody hyperspace.** The whole space `ConvexSubbody K` is compact:
its image under the isometric embedding into `NonemptyCompacts Plane` is the compact locus
`convexSubbodyLocus K`. -/
theorem isCompact_univ (K : Geometry.ConvexBody Plane) :
    IsCompact (Set.univ : Set (ConvexSubbody K)) := by
  rw [ConvexSubbody.embedding_toNonemptyCompacts.isCompact_iff, Set.image_univ,
    ConvexSubbody.range_toNonemptyCompacts]
  exact isCompact_convexSubbodyLocus K

/-- The canonical **compact-space** instance on `ConvexSubbody K`, obtained from compactness of
the whole space. -/
noncomputable instance instCompactSpace : CompactSpace (ConvexSubbody K) :=
  ⟨ConvexSubbody.isCompact_univ K⟩

/-- The image of a compact space under a continuous map into `ConvexSubbody K` has compact range. -/
theorem compact_range
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (f : C(X, ConvexSubbody K)) :
    IsCompact (Set.range f) :=
  isCompact_range f.continuous

end ConvexSubbody

end NRR
