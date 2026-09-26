/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import LeanPool.NandakumarRamanaRao.NRR.Geometry.ConvexBody.Basic

/-!
# `NRR.Geometry.ConvexBody` — topological accessor API

This module packages the topological facts about a `ConvexBody` (compactness, closedness,
boundedness, nonemptiness, interior membership, closure and frontier) into a stable,
namespaced accessor API. Downstream modules should obtain these facts through the wrappers
below and never unfold the `ConvexBody` structure to get them.

Some facts are already provided in `NRR.Geometry.ConvexBody.Basic`
(`ConvexBody.isCompact`, `ConvexBody.nonempty`, `ConvexBody.interior_nonempty`); those are
re-used here rather than duplicated.

## Import policy

Following the library-wide policy, `Basic.lean` already pulls in `import Mathlib`, so no extra
imports are required here; the topological lemmas used
(`IsCompact.isClosed`, `IsCompact.isBounded`, `IsClosed.closure_eq`, `IsClosed.frontier_subset`,
`interior_subset`) are all available transitively.
-/

@[expose] public section

namespace NRR.Geometry

namespace ConvexBody

section Topological

variable {E : Type*} [TopologicalSpace E] [AddCommMonoid E] [Module ℝ E]

/-- The interior of a convex body is contained in the body. -/
theorem interior_subset (K : ConvexBody E) :
    interior (K : Set E) ⊆ (K : Set E) :=
  _root_.interior_subset

/-- A point in the interior of a convex body is a point of the body. -/
theorem mem_of_mem_interior (K : ConvexBody E) {x : E}
    (hx : x ∈ interior (K : Set E)) :
    x ∈ (K : Set E) :=
  K.interior_subset hx

/-- A convex body has an element. -/
theorem exists_mem (K : ConvexBody E) :
    ∃ x : E, x ∈ (K : Set E) :=
  K.nonempty

/-- A convex body has an interior point. -/
theorem exists_mem_interior (K : ConvexBody E) :
    ∃ x : E, x ∈ interior (K : Set E) :=
  K.interior_nonempty

end Topological

section T2

variable {E : Type*} [TopologicalSpace E] [T2Space E] [AddCommMonoid E] [Module ℝ E]

/-- A convex body is closed (compact in a Hausdorff space). -/
theorem isClosed (K : ConvexBody E) :
    IsClosed (K : Set E) :=
  K.isCompact.isClosed

/-- The closure of a convex body is the body itself, since it is closed. -/
@[simp] theorem closure_eq (K : ConvexBody E) :
    closure (K : Set E) = (K : Set E) :=
  K.isClosed.closure_eq

/-- The frontier of a convex body is contained in the body, since it is closed. -/
theorem frontier_subset (K : ConvexBody E) :
    frontier (K : Set E) ⊆ (K : Set E) :=
  K.isClosed.frontier_subset

end T2

section Metric

variable {E : Type*} [PseudoMetricSpace E] [AddCommMonoid E] [Module ℝ E]

/-- A convex body is bounded (compact in a metric space). -/
theorem isBounded (K : ConvexBody E) :
    Bornology.IsBounded (K : Set E) :=
  K.isCompact.isBounded

end Metric

end ConvexBody

end NRR.Geometry
