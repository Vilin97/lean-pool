/-
Copyright (c) 2026 Yoshito Ishiki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoshito Ishiki
-/
import LeanPool.ScottishBook155.Preliminaries
import Mathlib.Topology.MetricSpace.Completion

/-!
# Completion and recovery lemmas for coherent limit stages

The limit-stage proof uses common finite-coordinate truncations.  Abstractly,
these give simultaneous approximants whose mutual distance never exceeds the
limit distance.  This file isolates the two consequences needed later:
short-distance preservation passes to the completion, and a jointly separating
family of recovered coordinates forces injectivity.
-/

namespace ScottishBook155

open Filter UniformSpace

universe u v w

/-- Simultaneous sequential approximants in a dense metric subspace, with no
increase of the distance between the two approximated points. -/
def HasDistanceControlledApproximants (E : Type u) [PseudoMetricSpace E] : Prop :=
  ∀ x y : Completion E, ∃ a b : ℕ → E,
    Tendsto (fun n => (a n : Completion E)) atTop (nhds x) ∧
    Tendsto (fun n => (b n : Completion E)) atTop (nhds y) ∧
    ∀ n, dist (a n) (b n) ≤ dist x y

/-- Simultaneous approximants indexed by an arbitrary nontrivial filter.  This
is the form naturally supplied by finite-coordinate truncations ordered by
inclusion. -/
def HasDistanceControlledNetApproximants (E : Type u) [PseudoMetricSpace E]
    (A : Type w) (l : Filter A) : Prop :=
  ∀ x y : Completion E, ∃ a b : A → E,
    Tendsto (fun i => (a i : Completion E)) l (nhds x) ∧
    Tendsto (fun i => (b i : Completion E)) l (nhds y) ∧
    ∀ i, dist (a i) (b i) ≤ dist x y

/-- Exact preservation below a fixed scale passes to the completion from a
common distance-controlled approximating net. -/
theorem completionExtension_preservesUpTo_of_net
    {E : Type u} {F : Type v} {A : Type w} [PseudoMetricSpace E]
    [MetricSpace F] [CompleteSpace F] {l : Filter A} [NeBot l]
    {f : E → F} {r : ℝ}
    (hf : LipschitzWith 1 f) (hshort : PreservesUpTo r f)
    (happrox : HasDistanceControlledNetApproximants E A l) :
    PreservesUpTo r (Completion.extension f) := by
  intro x y hxy
  obtain ⟨a, b, ha, hb, hab⟩ := happrox x y
  have hfa : Tendsto (Completion.extension f ∘ fun i => (a i : Completion E)) l
      (nhds (Completion.extension f x)) := by
    exact (hf.completion_extension.continuous.tendsto x).comp ha
  have hfb : Tendsto (Completion.extension f ∘ fun i => (b i : Completion E)) l
      (nhds (Completion.extension f y)) := by
    exact (hf.completion_extension.continuous.tendsto y).comp hb
  have himage : Tendsto (fun i =>
      dist (Completion.extension f (a i : Completion E))
        (Completion.extension f (b i : Completion E))) l
      (nhds (dist (Completion.extension f x) (Completion.extension f y))) :=
    hfa.dist hfb
  have hsource : Tendsto (fun i =>
      dist (Completion.extension f (a i : Completion E))
        (Completion.extension f (b i : Completion E))) l
      (nhds (dist x y)) := by
    apply (ha.dist hb).congr'
    filter_upwards [] with i
    rw [Completion.extension_coe hf.uniformContinuous,
      Completion.extension_coe hf.uniformContinuous, Completion.dist_eq]
    exact (hshort ((hab i).trans hxy)).symm
  exact tendsto_nhds_unique himage hsource

/-- Exact preservation below a fixed scale passes to the completion whenever
the dense subspace has common distance-controlled approximants. -/
theorem completionExtension_preservesUpTo
    {E : Type u} {F : Type v} [PseudoMetricSpace E]
    [MetricSpace F] [CompleteSpace F] {f : E → F} {r : ℝ}
    (hf : LipschitzWith 1 f) (hshort : PreservesUpTo r f)
    (happrox : HasDistanceControlledApproximants E) :
    PreservesUpTo r (Completion.extension f) := by
  exact completionExtension_preservesUpTo_of_net hf hshort happrox

/-- Coordinate recovery proves injectivity whenever the recovered coordinates
jointly separate the source. -/
theorem injective_of_jointlySeparating_recovery
    {X : Type u} {Y : Type v} {ι : Type w} {Z : ι → Type*}
    (f : X → Y) (project : ∀ i, X → Z i) (recover : ∀ i, Y → Z i)
    (hrecover : ∀ i x, recover i (f x) = project i x)
    (hseparate : ∀ x y, (∀ i, project i x = project i y) → x = y) :
    Function.Injective f := by
  intro x y hxy
  apply hseparate x y
  intro i
  rw [← hrecover i x, ← hrecover i y, hxy]

/-- Eventual coordinate recovery is enough for injectivity when eventual
equality of the recovered prefixes separates source points.  This is the form
used after all coordinates larger than the flat recovery band have appeared. -/
theorem injective_of_eventuallySeparating_recovery
    {X : Type u} {Y : Type v} {A : Type w} {Z : A → Type*}
    {l : Filter A} [NeBot l]
    (f : X → Y) (project : ∀ i, X → Z i) (recover : ∀ i, Y → Z i)
    (hrecover : ∀ x, ∀ᶠ i in l, recover i (f x) = project i x)
    (hseparate : ∀ x y, (∀ᶠ i in l, project i x = project i y) → x = y) :
    Function.Injective f := by
  intro x y hxy
  apply hseparate x y
  filter_upwards [hrecover x, hrecover y] with i hxi hyi
  rw [← hxi, ← hyi, hxy]

/-- Eventual equality of approximating projections implies equality of their
limits. -/
theorem eq_of_eventually_eq_of_tendsto
    {X : Type u} [TopologicalSpace X] [T2Space X]
    {A : Type v} {l : Filter A} [NeBot l]
    (project : A → X → X)
    (hproject : ∀ x, Tendsto (fun i => project i x) l (nhds x))
    {x y : X} (hxy : ∀ᶠ i in l, project i x = project i y) : x = y := by
  have hyx : ∀ᶠ i in l, project i y = project i x := by
    filter_upwards [hxy] with i hi
    exact hi.symm
  have hlim : Tendsto (fun i => project i x) l (nhds y) :=
    (hproject y).congr' hyx
  exact tendsto_nhds_unique (hproject x) hlim

/-- A completed limit map is injective when its coherent retractions
eventually recover injective earlier-stage maps and the source projections
converge to the identity. -/
theorem injective_of_eventual_stage_recovery
    {X : Type u} [TopologicalSpace X] [T2Space X]
    {Y : Type v} {A : Type w} {l : Filter A} [NeBot l]
    {Xstage : A → Type*} {Ystage : A → Type*}
    (f : X → Y) (stageMap : ∀ i, Xstage i → Ystage i)
    (stageInjective : ∀ i, Function.Injective (stageMap i))
    (project : ∀ i, X → Xstage i) (embed : ∀ i, Xstage i → X)
    (recover : ∀ i, Y → Ystage i)
    (hproject : ∀ x, Tendsto (fun i => embed i (project i x)) l (nhds x))
    (hrecover : ∀ x, ∀ᶠ i in l,
      recover i (f x) = stageMap i (project i x)) :
    Function.Injective f := by
  intro x y hxy
  apply eq_of_eventually_eq_of_tendsto (fun i z => embed i (project i z)) hproject
  filter_upwards [hrecover x, hrecover y] with i hxi hyi
  apply congrArg (embed i)
  apply stageInjective i
  rw [← hxi, ← hyi, hxy]

end ScottishBook155
