/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.AnalyticSet.Hartogs

/-!
# Complex slices and removal in codimension at least two

Following [Scheidemann][Scheidemann2005] §4.1, codimension at least `q` is expressed by an
injective complex linear `q`-plane on which each point of the subset is an isolated
intersection. We retain the pointwise slice witness instead of introducing a general dimension
theory. The empty set satisfies every bound; at a point the bound cannot exceed ambient
dimension.

Hartogs figures around isolated two-dimensional slices give local holomorphic extensions, and
hence automatic local boundedness across the analytic set. The first Riemann extension theorem
then gives the global second Riemann extension theorem. Reference:
[Scheidemann][Scheidemann2005] 4.1.4 and 4.2.3.

## Main definitions

* `HasIsolatedComplexSlice`: An affine complex `q`-plane through `a` meets `A` only at `a` near that
  point.
* `HasComplexSliceCodimensionAtLeast`: The slice formulation of complex codimension at least `q`, at
  every point of `A`.

## Main results

* `IsAnalyticSet.locally_bounded_of_codimension_two`: **Automatic local boundedness in codimension
  at least two.** Hartogs continuation around isolated two-dimensional slices gives a local
  holomorphic extension, whose continuity supplies the bound.
* `IsAnalyticSet.exists_extension_of_codimension_two`: **Second Riemann extension theorem.** No
  boundedness or connectedness assumption is imposed.

## References

* [V. Scheidemann, *Introduction to Complex Analysis in Several Variables*][Scheidemann2005]
-/

public noncomputable section

open Set Filter Metric
open scoped Topology

namespace SeveralComplexVariables

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- An affine complex `q`-plane through `a` meets `A` only at `a` near that point. Membership of `a`
in `A` is separate, so this predicate also applies outside `A`. -/
@[expose] def HasIsolatedComplexSlice (A : Set E) (a : E) (q : ℕ) : Prop :=
  ∃ L : (Fin q → ℂ) →L[ℂ] E, Function.Injective L ∧
    ∀ᶠ z in 𝓝 (0 : Fin q → ℂ), a + L z ∈ A → z = 0

/-- The slice formulation of complex codimension at least `q`, at every point of `A`. Analyticity is
a separate assumption. -/
@[expose] def HasComplexSliceCodimensionAtLeast (A : Set E) (q : ℕ) : Prop :=
  ∀ a ∈ A, HasIsolatedComplexSlice A a q

/-- The empty set satisfies every slice-codimension bound. -/
theorem hasComplexSliceCodimensionAtLeast_empty (q : ℕ) :
    HasComplexSliceCodimensionAtLeast (∅ : Set E) q := by
  simp [HasComplexSliceCodimensionAtLeast]

/-- Every subset has slice codimension at least zero; the zero-dimensional slice is a point. -/
theorem hasComplexSliceCodimensionAtLeast_zero (A : Set E) :
    HasComplexSliceCodimensionAtLeast A 0 := by
  intro a _
  exact ⟨0, fun _ _ _ => Subsingleton.elim _ _,
    Filter.Eventually.of_forall (fun _ _ => Subsingleton.elim _ _)⟩

/-- Isolated slice intersections are preserved on subsets. -/
theorem HasIsolatedComplexSlice.mono {A B : Set E} {a : E} {q : ℕ}
    (h : HasIsolatedComplexSlice A a q) (hBA : B ⊆ A) : HasIsolatedComplexSlice B a q := by
  obtain ⟨L, hi, he⟩ := h
  exact ⟨L, hi, he.mono (fun _ hz hb => hz (hBA hb))⟩

/-- Slice-codimension bounds pass to subsets, in particular to restrictions to open sets. -/
theorem HasComplexSliceCodimensionAtLeast.mono {A B : Set E} {q : ℕ}
    (h : HasComplexSliceCodimensionAtLeast A q) (hBA : B ⊆ A) :
    HasComplexSliceCodimensionAtLeast B q := fun a ha => (h a (hBA ha)).mono hBA

/-- A slice cannot have larger dimension than the ambient finite-dimensional space. -/
theorem HasIsolatedComplexSlice.le_finrank [FiniteDimensional ℂ E]
    {A : Set E} {a : E} {q : ℕ} (h : HasIsolatedComplexSlice A a q) :
    q ≤ Module.finrank ℂ E := by
  obtain ⟨L, hi, _⟩ := h
  simpa using LinearMap.finrank_le_finrank_of_injective (f := L.toLinearMap) hi

/-- A codimension bound exceeding ambient dimension forces the set to be empty. -/
theorem HasComplexSliceCodimensionAtLeast.eq_empty_of_finrank_lt [FiniteDimensional ℂ E]
    {A : Set E} {q : ℕ} (h : HasComplexSliceCodimensionAtLeast A q)
    (hq : Module.finrank ℂ E < q) : A = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro a ha
  exact (not_le_of_gt hq) (h a ha).le_finrank

/-- A positive-dimensional isolated slice excludes an interior point. -/
theorem HasIsolatedComplexSlice.notMem_interior {A : Set E} {a : E} {q : ℕ}
    (h : HasIsolatedComplexSlice A a q) (hq : 0 < q) : a ∉ interior A := by
  let : Nonempty (Fin q) := ⟨⟨0, hq⟩⟩
  obtain ⟨L, _, he⟩ := h
  intro ha
  have hc : ContinuousAt (fun z => a + L z) (0 : Fin q → ℂ) :=
    continuousAt_const.add L.continuous.continuousAt
  have hn : ∀ᶠ z in 𝓝 (0 : Fin q → ℂ), a + L z ∈ A :=
    hc.preimage_mem_nhds (by simpa using mem_interior_iff_mem_nhds.mp ha)
  have hz : ({0} : Set (Fin q → ℂ)) ∈ 𝓝 0 := by
    filter_upwards [he, hn] with z hze hza
    exact hze hza
  have hzero : (0 : Fin q → ℂ) ∈ interior ({0} : Set (Fin q → ℂ)) :=
    mem_interior_iff_mem_nhds.mpr hz
  simp at hzero

/-- Positive slice codimension implies empty interior, also on disconnected domains. -/
theorem HasComplexSliceCodimensionAtLeast.interior_eq_empty {A : Set E} {q : ℕ}
    (h : HasComplexSliceCodimensionAtLeast A q) (hq : 0 < q) : interior A = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro a ha
  exact (h a (interior_subset ha)).notMem_interior hq ha

/-- **Automatic local boundedness in codimension at least two.** Hartogs continuation
around isolated two-dimensional slices gives a local holomorphic extension, whose
continuity supplies the bound. This allows arbitrary complex Banach targets. -/
theorem IsAnalyticSet.locally_bounded_of_codimension_two [FiniteDimensional ℂ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {U A : Set E} (hA : IsAnalyticSet U A) (hcodim : HasComplexSliceCodimensionAtLeast A 2)
    {f : E → F} (hf : AnalyticOnNhd ℂ f (U \ A)) :
    ∀ a ∈ A, ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ,
      ∀ z ∈ ball a r ∩ (U \ A), ‖f z‖ ≤ C := by
  intro a ha
  obtain ⟨L, _, hisol⟩ := hcodim a ha
  let e := (ContinuousLinearEquiv.finTwoArrow ℂ ℂ).symm
  have hisol' : ∀ᶠ p in 𝓝 (0 : ℂ × ℂ), a + (L.comp e.toContinuousLinearMap) p ∈ A → p = 0 := by
    have ht : Tendsto e (𝓝 (0 : ℂ × ℂ)) (𝓝 0) := by
      simpa using e.continuous.tendsto (0 : ℂ × ℂ)
    filter_upwards [ht.eventually hisol] with p hp hpA
    apply e.injective
    simpa using hp hpA
  obtain ⟨r, hr, g, hg, heq⟩ := hA.exists_local_extension_of_isolated_two_slice
    (hA.subset ha) (L.comp e.toContinuousLinearMap) hisol' hf
  have hb : ∀ᶠ z in 𝓝 a, ‖g z‖ < ‖g a‖ + 1 :=
    ((hg a (mem_ball_self hr)).continuousAt.norm).eventually_lt_const (by linarith)
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp (inter_mem (ball_mem_nhds a hr) hb)
  refine ⟨δ, hδ, ‖g a‖ + 1, fun z hz => ?_⟩
  have hz' := hδsub hz.1
  rw [← heq ⟨hz'.1, hz.2.2⟩]
  exact hz'.2.le

/-- **Second Riemann extension theorem.** No boundedness or connectedness assumption
is imposed. The proof depends on automatic local boundedness in codimension two. -/
theorem IsAnalyticSet.exists_extension_of_codimension_two [FiniteDimensional ℂ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {U A : Set E} (hA : IsAnalyticSet U A) (hcodim : HasComplexSliceCodimensionAtLeast A 2)
    {f : E → F} (hf : AnalyticOnNhd ℂ f (U \ A)) :
    ∃ g, AnalyticOnNhd ℂ g U ∧ EqOn g f (U \ A) :=
  hA.exists_extension_of_locally_bounded (hcodim.interior_eq_empty (by decide)) hf
    (hA.locally_bounded_of_codimension_two hcodim hf)

/-- Extensions in the second Riemann theorem are unique on the ambient domain. This uniqueness proof
uses density and does not require the existence argument. -/
theorem IsAnalyticSet.extension_unique_of_codimension_two
    {F : Type*} [TopologicalSpace F] [T2Space F] {U A : Set E}
    (hA : IsAnalyticSet U A) (hcodim : HasComplexSliceCodimensionAtLeast A 2)
    {f g h : E → F} (hg : ContinuousOn g U) (hh : ContinuousOn h U)
    (hgf : EqOn g f (U \ A)) (hhf : EqOn h f (U \ A)) : EqOn g h U :=
  hA.extension_unique (hcodim.interior_eq_empty (by decide)) hg hh hgf hhf

end SeveralComplexVariables

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
