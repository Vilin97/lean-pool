/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import LeanPool.NandakumarRamanaRao.NRR.Geometry.ConvexBody.Basic
public import LeanPool.NandakumarRamanaRao.NRR.Geometry.ConvexBody.Topology

/-!
# `NRR.Geometry.ConvexBody` — interior lemmas

This module develops focused interior lemmas for `ConvexBody`, especially the ones needed
later for halfspace cuts and affine transformations. It provides:

* basic access to an interior point (`exists_interior_point`, `chooseInteriorPoint`);
* existence of an open (resp. closed) metric ball inside the body
 (`exists_ball_subset`, `exists_closedBall_subset`, `exists_point_strictly_inside_ball`);
* stability of nonempty interior under supersets (`interior_nonempty_of_superset`).

It does **not** treat affine images (deferred to a separate module), and it adds no new fields to
`ConvexBody`.

## Import policy

Following the library-wide policy, `Basic.lean` already pulls in `import Mathlib`, so no extra
imports are required here; the metric lemmas used (`mem_interior_iff_mem_nhds`,
`Metric.isOpen_ball`, `Metric.mem_ball_self`, `Metric.closedBall_subset_ball`,
`interior_mono`) are all available transitively.
-/

@[expose] public section

namespace NRR.Geometry

namespace ConvexBody

section Topological

variable {E : Type*} [TopologicalSpace E] [AddCommMonoid E] [Module ℝ E]

/-- A convex body has an interior point. (Alias of `interior_nonempty` in existential form.) -/
theorem exists_interior_point (K : ConvexBody E) :
    ∃ x, x ∈ interior (K : Set E) :=
  K.interior_nonempty

open Classical in
/-- A chosen interior point of a convex body. -/
noncomputable def chooseInteriorPoint (K : ConvexBody E) : E :=
  K.exists_interior_point.choose

/-- The chosen interior point indeed lies in the interior of the body. -/
theorem choose_interior_point_mem_interior (K : ConvexBody E) :
    K.chooseInteriorPoint ∈ interior (K : Set E) :=
  K.exists_interior_point.choose_spec

/-- If a convex body is contained in a set `s`, then `s` has nonempty interior. -/
theorem interior_nonempty_of_superset (K : ConvexBody E) {s : Set E}
    (hKs : (K : Set E) ⊆ s) :
    (interior s).Nonempty :=
  K.interior_nonempty.mono (interior_mono hKs)

end Topological

section Metric

variable {E : Type*} [PseudoMetricSpace E] [AddCommMonoid E] [Module ℝ E]

/-- A convex body contains an open metric ball of positive radius. -/
theorem exists_ball_subset (K : ConvexBody E) :
    ∃ x : E, ∃ r : ℝ, 0 < r ∧ Metric.ball x r ⊆ (K : Set E) := by
  obtain ⟨x, hx⟩ := K.exists_interior_point
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hx
  obtain ⟨r, hr, hsub⟩ := hx
  exact ⟨x, r, hr, hsub⟩

/-- A convex body contains a closed metric ball of positive radius. -/
theorem exists_closedBall_subset (K : ConvexBody E) :
    ∃ x : E, ∃ r : ℝ, 0 < r ∧ Metric.closedBall x r ⊆ (K : Set E) := by
  obtain ⟨x, r, hr, hsub⟩ := K.exists_ball_subset
  refine ⟨x, r / 2, by positivity, ?_⟩
  exact (Metric.closedBall_subset_ball (by linarith)).trans hsub

/-- A halfspace-friendly restatement of `exists_closedBall_subset`: a convex body contains a
closed metric ball of positive radius. -/
theorem exists_point_strictly_inside_ball (K : ConvexBody E) :
    ∃ x r, 0 < r ∧ Metric.closedBall x r ⊆ (K : Set E) :=
  K.exists_closedBall_subset

end Metric

end ConvexBody

end NRR.Geometry
