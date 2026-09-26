/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
/-!
# Route B, Step 1: avoidance of a finite family of null bad sets

This file isolates the final measure-theoretic selection argument used by the
relative positive-ray perturbation theorem.  It does not mention collars,
simplices, or equivariance.

Once every individual geometric bad set has been proved null, the theorem
`exists_mem_ball_avoiding_finset_of_null` produces a parameter in any
positive-measure perturbation ball which avoids all of them simultaneously.
-/

@[expose] public section

namespace NRR
namespace FoxNeuwirthOrderComplex
namespace RouteBFiniteAvoidance

open MeasureTheory

variable {E ι : Type*} [PseudoMetricSpace E] [MeasurableSpace E]

omit [PseudoMetricSpace E] in
/-- A finite union of sets of `μ`-measure zero has `μ`-measure zero.

The union is written over the subtype determined by the finite index set.  This
form avoids any decidability or enumeration choices in later applications.
-/
theorem measure_iUnion_finset_null
    (μ : Measure E)
    (bad : ι → Set E)
    (indices : Finset ι)
    (hnull : ∀ i ∈ indices, μ (bad i) = 0) :
    μ (⋃ i : {i // i ∈ indices}, bad i.1) = 0 := by
  apply measure_iUnion_null
  intro i
  exact hnull i.1 i.2

omit [PseudoMetricSpace E] in
/-- Every set of positive measure contains a point outside a finite family of
null bad sets.

This is the abstract selection lemma needed by Route B.  In the collar
application, `goodRegion` will be an open ball around the unperturbed movable
assignment, and `bad i` will be the positive-ray incidence set attached to one
mixed face and one choice of distinguished movable vertex.
-/
theorem exists_mem_avoiding_finset_of_null
    (μ : Measure E)
    (bad : ι → Set E)
    (indices : Finset ι)
    (goodRegion : Set E)
    (hgood : μ goodRegion ≠ 0)
    (hnull : ∀ i ∈ indices, μ (bad i) = 0) :
    ∃ x ∈ goodRegion, ∀ i ∈ indices, x ∉ bad i := by
  classical
  let badUnion : Set E := ⋃ i : {i // i ∈ indices}, bad i.1
  have hbadUnion : μ badUnion = 0 := by
    dsimp [badUnion]
    exact measure_iUnion_finset_null μ bad indices hnull
  by_contra h
  push Not at h
  have hsubset : goodRegion ⊆ badUnion := by
    intro x hx
    by_contra hxUnion
    have havoid : ∀ i ∈ indices, x ∉ bad i := by
      intro i hi hxi
      exact hxUnion (Set.mem_iUnion.mpr ⟨⟨i, hi⟩, hxi⟩)
    obtain ⟨i, hi, hxi⟩ := h x hx
    exact havoid i hi hxi
  have hzero : μ goodRegion = 0 :=
    measure_mono_null hsubset hbadUnion
  exact hgood hzero

/-- Ball form of `exists_mem_avoiding_finset_of_null`.

No geometric assumptions are hidden here: positivity of the ball measure is an
explicit hypothesis.  A later finite-dimensional specialization will discharge
it using positivity of Lebesgue measure on nonempty metric balls.
-/
theorem exists_mem_ball_avoiding_finset_of_null
    (μ : Measure E)
    (bad : ι → Set E)
    (indices : Finset ι)
    (center : E)
    (radius : ℝ)
    (hball : μ (Metric.ball center radius) ≠ 0)
    (hnull : ∀ i ∈ indices, μ (bad i) = 0) :
    ∃ x ∈ Metric.ball center radius, ∀ i ∈ indices, x ∉ bad i :=
  exists_mem_avoiding_finset_of_null
    μ bad indices (Metric.ball center radius) hball hnull

end RouteBFiniteAvoidance
end FoxNeuwirthOrderComplex
end NRR
