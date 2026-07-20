/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/

import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Topology.Compactness.Compact

/-!
# `RellichKondrachov.Geometry.Manifold.Sobolev.ChartData`

Chart/partition-of-unity data for defining Sobolev spaces on compact manifolds.

For the Laplace–Beltrami compact-resolvent discharge (`lean-103.5.2.26`), we ultimately need
Sobolev spaces `H¹`, `H²` on a compact smooth manifold `M` together with continuous maps to `L²`
and to suitable “derivative” targets.

At the current Mathlib pin, the most robust starting point is to make the analytic definitions
relative to *explicit finite chart data* and a *smooth partition of unity* subordinate to those
charts; later work can address atlas-independence.

This file provides:

* `RellichKondrachov.Geometry.Manifold.Sobolev.FiniteChartData`: a finite family of chart centers
  together with a subordinate `SmoothPartitionOfUnity`.
* `RellichKondrachov.Geometry.Manifold.Sobolev.exists_finiteChartData_chartAt`: on a compact smooth
  manifold, there exists such data subordinate to `chartAt` sources.
-/

namespace RellichKondrachov
namespace Geometry
namespace Manifold
namespace Sobolev

open Set Topology

universe uE uH uM

section

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners ℝ E H} [IsManifold I (⊤ : WithTop ℕ∞) M]

/-- Finite chart centers with a smooth partition of unity subordinate to `chartAt` sources. -/
structure FiniteChartData (H : Type*) (M : Type*) [TopologicalSpace H] [TopologicalSpace M]
    [ChartedSpace H M] (I : ModelWithCorners ℝ E H) [IsManifold I (⊤ : WithTop ℕ∞) M] where
  /-- An index type for the chart data. -/
  ι : Type*
  /-- The index type is finite. -/
  instFintype : Fintype ι
  /-- The chosen chart centers. -/
  center : ι → M
  /-- A smooth partition of unity indexed by `ι` on `M`. -/
  ρ : SmoothPartitionOfUnity ι I M univ
  /-- Subordination to the chart domains:
  `closure (support (ρ i)) ⊆ (chartAt H (center i)).source`. -/
  subordinate : ρ.IsSubordinate fun i => (chartAt H (center i)).source

attribute [instance] FiniteChartData.instFintype

namespace FiniteChartData

variable (d : FiniteChartData (H := H) (M := M) I)

omit [FiniteDimensional ℝ E] in
@[simp] lemma subordinate_apply (i : d.ι) :
    closure (Function.support (d.ρ i : M → ℝ)) ⊆ (chartAt H (d.center i)).source :=
  d.subordinate i

end FiniteChartData

section Compact

variable [T2Space M] [CompactSpace M]

omit [T2Space M] [CompactSpace M] in
private lemma univ_subset_iUnion_chartAt_source :
    (univ : Set M) ⊆ ⋃ x : M, (chartAt H x).source := by
  intro x hx
  exact mem_iUnion_of_mem x (mem_chart_source H x)

omit [T2Space M] [CompactSpace M] in
private lemma isOpen_chartAt_source (x : M) : IsOpen ((chartAt H x).source : Set M) :=
  (chartAt H x).open_source

/-- On a compact smooth manifold, there exists finite chart data subordinate
to `chartAt` sources. -/
theorem exists_finiteChartData_chartAt :
    Nonempty (FiniteChartData.{uE, uH, uM, uM} (H := H) (M := M) I) := by
  classical
  -- Extract a finite subcover of the open cover by `chartAt` domains.
  have hcover : (univ : Set M) ⊆ ⋃ x : M, (chartAt H x).source :=
    univ_subset_iUnion_chartAt_source (H := H)
  rcases (isCompact_univ.elim_finite_subcover (fun x : M => (chartAt H x).source)
      (fun x => isOpen_chartAt_source (H := H) (x := x)) hcover) with ⟨t, ht⟩
  -- Use the finite subcover as an index type.
  let ι' := {x : M // x ∈ t}
  have hU : (univ : Set M) ⊆ ⋃ i : ι', (chartAt H (i : M)).source := by
    intro x hx
    have : x ∈ ⋃ y ∈ (t : Finset M), (chartAt H y).source := ht hx
    rcases mem_iUnion₂.1 this with ⟨y, hy, hxy⟩
    exact mem_iUnion_of_mem ⟨y, hy⟩ hxy
  -- Build a smooth partition of unity subordinate to this finite family.
  haveI : SigmaCompactSpace M := by infer_instance
  have ho : ∀ i : ι', IsOpen ((chartAt H (i : M)).source : Set M) := fun i =>
    isOpen_chartAt_source (H := H) (x := (i : M))
  rcases SmoothPartitionOfUnity.exists_isSubordinate (ι := ι') (I := I) (M := M)
      (s := (univ : Set M)) isClosed_univ (fun i => (chartAt H (i : M)).source) ho hU with
    ⟨ρ, hρ⟩
  refine ⟨{
    ι := ι',
    instFintype := Finset.Subtype.fintype t,
    center := fun i => (i : M),
    ρ := ρ,
    subordinate := hρ
  }⟩

end Compact

end

end Sobolev
end Manifold
end Geometry
end RellichKondrachov
