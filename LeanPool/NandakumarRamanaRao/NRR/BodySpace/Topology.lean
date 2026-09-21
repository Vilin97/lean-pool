/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Closeds
import LeanPool.NandakumarRamanaRao.NRR.BodySpace.Basic

/-!
# `NRR.ConvexSubbody` — inherited Hausdorff topology and hyperspace embedding

This module exposes the Hausdorff metric/topology that `ConvexSubbody K` inherits, as a subtype,
from Mathlib's root convex body `_root_.ConvexBody Plane`. It provides:

* the inherited `MetricSpace` / `T2Space` structure;
* the forgetful map `ConvexSubbody.toNonemptyCompacts` into the hyperspace of nonempty compact
  sets, shown to be an isometric embedding (`continuous`, `IsInducing`, `IsEmbedding`);
* the identification `dist C D = hausdorffDist C.body D.body`;
* closedness of the fixed-parent containment locus inside `NonemptyCompacts Plane`;
* filter-level convergence lemmas (`tendsto_body`, `tendsto_hausdorffDist_zero`) used by later
  prompts.

No new metric, hyperspace topology, or convex-body type is introduced: everything is inherited
from the root Mathlib body and its Hausdorff metric.
-/

open MeasureTheory Metric TopologicalSpace Filter Topology

open NRR.Geometry

namespace NRR

namespace ConvexSubbody

variable {K : Geometry.ConvexBody Plane}

/-- The inherited **Hausdorff metric** on `ConvexSubbody K`, taken as a subtype of Mathlib's
root convex body `_root_.ConvexBody Plane`. Because `ConvexSubbody` is a `def` over a subtype,
this instance is stated explicitly rather than inferred. -/
noncomputable instance instMetricSpace : MetricSpace (ConvexSubbody K) :=
  inferInstanceAs
    (MetricSpace {C : _root_.ConvexBody Plane // (C : Set Plane) ⊆ (K : Set Plane)})

/-- `ConvexSubbody K` is Hausdorff (inherited from its metric). -/
instance instT2Space : T2Space (ConvexSubbody K) := inferInstance

/-- The forgetful map to the hyperspace of **nonempty compact sets**: a subbody is sent to its
carrier, together with its compactness and nonemptiness witnesses. -/
def toNonemptyCompacts (C : ConvexSubbody K) : TopologicalSpace.NonemptyCompacts Plane :=
  ⟨⟨(C.body : Set Plane), C.isCompact⟩, C.nonempty⟩

@[simp] theorem toNonemptyCompacts_carrier (C : ConvexSubbody K) :
    (C.toNonemptyCompacts : Set Plane) = (C.body : Set Plane) :=
  rfl

/-- The forgetful map to `NonemptyCompacts` is an **isometry**: both sides measure the Hausdorff
extended distance between the same carriers. -/
theorem isometry_toNonemptyCompacts :
    Isometry (ConvexSubbody.toNonemptyCompacts (K := K)) := by
  intro C D
  show Metric.hausdorffEDist (C.body : Set Plane) (D.body : Set Plane) = edist C D
  rw [ConvexBody.hausdorffEDist_coe]
  rfl

theorem continuous_toNonemptyCompacts :
    Continuous (ConvexSubbody.toNonemptyCompacts (K := K)) :=
  isometry_toNonemptyCompacts.continuous

/-- The forgetful map to `NonemptyCompacts` is inducing (the inherited topology is the pullback
of the hyperspace topology). Named `inducing_toNonemptyCompacts`; the current Mathlib predicate
is `Topology.IsInducing`. -/
theorem inducing_toNonemptyCompacts :
    IsInducing (ConvexSubbody.toNonemptyCompacts (K := K)) :=
  isometry_toNonemptyCompacts.isEmbedding.toIsInducing

theorem embedding_toNonemptyCompacts :
    IsEmbedding (ConvexSubbody.toNonemptyCompacts (K := K)) :=
  isometry_toNonemptyCompacts.isEmbedding

/-- The inherited distance on `ConvexSubbody K` is the Hausdorff distance of the carriers. -/
theorem dist_eq_hausdorffDist (C D : ConvexSubbody K) :
    dist C D = Metric.hausdorffDist (C.body : Set Plane) (D.body : Set Plane) := by
  rw [ConvexBody.hausdorffDist_coe]
  rfl

/-- The **fixed-parent containment locus** — nonempty compact sets contained in the parent body
`K` — is closed in the hyperspace `NonemptyCompacts Plane`. -/
theorem isClosed_fixedParent_nonemptyCompacts :
    IsClosed {C : TopologicalSpace.NonemptyCompacts Plane |
      (C : Set Plane) ⊆ (K : Set Plane)} :=
  TopologicalSpace.NonemptyCompacts.isClosed_subsets_of_isClosed K.isCompact.isClosed

/-- Convergence of subbodies pushes forward to convergence of their hyperspace images. -/
theorem tendsto_body
    {α : Type*} {l : Filter α}
    {C : α → ConvexSubbody K} {C₀ : ConvexSubbody K}
    (hC : Tendsto C l (𝓝 C₀)) :
    Tendsto (fun a => (C a).toNonemptyCompacts) l (𝓝 C₀.toNonemptyCompacts) :=
  (continuous_toNonemptyCompacts.tendsto C₀).comp hC

/-- Convergence of subbodies is witnessed by the Hausdorff distances tending to zero. -/
theorem tendsto_hausdorffDist_zero
    {α : Type*} {l : Filter α}
    {C : α → ConvexSubbody K} {C₀ : ConvexSubbody K}
    (hC : Tendsto C l (𝓝 C₀)) :
    Tendsto (fun a => Metric.hausdorffDist ((C a).body : Set Plane) (C₀.body : Set Plane))
      l (𝓝 0) := by
  have h : Tendsto (fun a => dist (C a) C₀) l (𝓝 0) :=
    tendsto_iff_dist_tendsto_zero.mp hC
  refine h.congr ?_
  intro a
  exact (dist_eq_hausdorffDist (C a) C₀).symm

end ConvexSubbody

end NRR
