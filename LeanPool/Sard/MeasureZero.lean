/-
Copyright (c) 2026 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/

import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.MeasureTheory.Measure.Haar.Basic

namespace LeanPool.Sard

/-!
# Measure zero subsets of a manifold

Defines the notion of measure-zero subsets on a finite-dimensional topological manifold.

While such a manifold has no canonical measure, a subset can be called
measure zero when its image in every preferred chart is null for every additive
Haar measure on the model vector space.

This file preserves the completed closure properties from the upstream Sard
development.

## References
See [Hirsch76], chapter 3.1 for the definition of measure zero subsets in a manifold.
-/

open MeasureTheory Measure Function TopologicalSpace Set

variable
  -- Let `M` be a finite-dimensional topological manifold over `(E, H)`.
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [MeasurableSpace E]
variable {I}

variable (I) in
/-- A measure zero subset of an n-dimensional manifold $M$ is a subset $S ⊆ M$ such that
for all charts $(φ, U)$ of $M$, $φ(U ∩ S) ⊆ ℝ^n$ has measure zero. -/
-- xxx: show that my spelling implies the same for all charts!
def MeasureZero (s : Set M) : Prop :=
  ∀ (μ : Measure E) [IsAddHaarMeasure μ] (x : M),
    μ (I ∘ (chartAt H x) '' ((chartAt H x).source ∩ s)) = 0

namespace MeasureZero
/-- Having measure zero is monotone: a subset of a set with measure zero has measure zero. -/
protected lemma mono {s t : Set M} (hst : s ⊆ t) (ht : MeasureZero I t) :
    (MeasureZero I s) := by
  intro μ _ x
  let e := chartAt H x
  have : I ∘ e '' (e.source ∩ s) ⊆  I ∘ e '' (e.source ∩ t) := by
    exact image_mono (inter_subset_inter_right e.source hst)
  exact measure_mono_null this (ht μ x)

/-- The empty set has measure zero. -/
protected lemma empty : MeasureZero I (∅: Set M) := by
  intro μ _ x
  simp only [comp_apply, inter_empty, image_empty, measure_empty]

/-- The countable index union of measure zero sets has measure zero. -/
protected lemma iUnion {ι : Type*} [Encodable ι] {s : ι → Set M}
    (hs : ∀ n : ι, MeasureZero I (s n)) : MeasureZero I (⋃ (n : ι),  s n) := by
  intro μ _ x
  let e := chartAt H x
  have :
      I ∘ e '' (e.source ∩ (⋃ (n : ι), s n)) =
        ⋃ (n : ι), I ∘ e '' (e.source ∩ s n) := by
    rw [inter_iUnion]
    exact image_iUnion
  -- union of null sets is a null set
  simp_all only [comp_apply, measure_iUnion_null_iff, e]
  intro i
  apply hs

/-- The finite union of measure-zero sets has measure zero. -/
protected lemma union {s t : Set M} (hs : MeasureZero I s) (ht : MeasureZero I t) :
    MeasureZero I (s ∪ t) := by
  let u : Bool → Set M := fun b ↦ cond b s t
  have : ∀ i : Bool, MeasureZero I (u i) := by
    intro i
    cases i
    · exact ht
    · exact hs
  rw [union_eq_iUnion]
  exact MeasureZero.iUnion this
end MeasureZero

end LeanPool.Sard
