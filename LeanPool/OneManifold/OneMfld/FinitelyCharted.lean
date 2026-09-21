/-
Copyright (c) 2026 Jim Fowler, Dennis Sweeney. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jim Fowler, Dennis Sweeney
-/
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Tactic

/-!
# FinitelyCharted

Supporting results for the classification of compact one-dimensional manifolds.
-/

variable {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M]

variable
  {M : Type*}
  [TopologicalSpace M]

/-- Choose a finite subatlas covering a compact charted space. -/
noncomputable def chooseCharts [CompactSpace M] [ht : ChartedSpace H M] : { ht' : ChartedSpace H
    M | Set.Finite ht'.atlas ∧ ht'.atlas ⊆ ht.atlas } := by
  let U : M → Set M := by
    intro x
    exact (ht.chartAt x).source
  let hUo : (i : M) → IsOpen (U i) := by
    intro x
    exact (ChartedSpace.chartAt x).open_source
  let hsU : (Set.univ : Set M) ⊆ ⋃ (i : M), U i := by
    intro x hx
    simp only [Set.mem_iUnion]
    use x
    exact ChartedSpace.mem_chart_source x
  have hc := IsCompact.elim_finite_subcover CompactSpace.isCompact_univ U hUo hsU
  let t := Classical.choose hc
  have t' := Classical.choose_spec hc
  let f (x : M) : { x' : M | x' ∈ t ∧ x ∈ (ht.chartAt x').source } := by
    have : x ∈ ⋃ i ∈ t, U i := by exact t' trivial
    simp only [Set.mem_iUnion, exists_prop] at this
    have hx := Classical.choose_spec this
    use Classical.choose this
    simp only [Set.mem_ofPred_eq]
    apply And.intro
    · exact hx.1
    · dsimp [U] at hx
      exact hx.2
  use { chartAt := by
            intro x
            exact ht.chartAt (f x).1
        , atlas := Set.image ht.chartAt t
        , chart_mem_atlas := by
            intro x
            apply Set.mem_image_of_mem ChartedSpace.chartAt
            refine Finset.mem_coe.mpr ?_
            exact (f x).2.1
        , mem_chart_source := by
            intro x
            exact (f x).2.2
  }
  simp only [Set.mem_ofPred_eq, Set.image_subset_iff]
  apply And.intro
  · exact Set.toFinite (ht.chartAt '' ↑t)
  · intro x hx
    simp only [Set.mem_preimage, chart_mem_atlas]
