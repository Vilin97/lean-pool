/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.RCLike.Extend
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.Analyticity

/-!
# Common extension domains inside a complex vector space

`IsCommonAnalyticExtension U V` says that `U ⊆ V` and every scalar analytic function on `U`
extends to `V`. It does not impose openness, connectedness, or maximality, and does not define
an abstract envelope. Simultaneous extension cannot introduce new scalar values, by extending
the reciprocal of a nowhere-zero function.

Convex separation also bounds common extension domains by the real convex hull. References:
[Korevaar–Wiegerinck][KorevaarWiegerinck2017] (2017), Proposition 2.9.2 and Corollary 2.9.3,
specialized to domains in a complex normed space.

## Main definitions

* `IsCommonAnalyticExtension`: Every scalar analytic function on `U` extends to the larger set `V`.

## Main results

* `IsCommonAnalyticExtension.trans`: Common extension composes.
* `IsCommonAnalyticExtension.image_eq`: A scalar analytic function on a connected common extension
  domain has exactly its original range.
* `IsCommonAnalyticExtension.subset_convexHull`: A common extension domain lies in the real convex
  hull of the original domain.

## References

* [J. Korevaar and J. Wiegerinck, *Several Complex Variables*][KorevaarWiegerinck2017]
-/

public section

open Filter Set
open scoped Topology

namespace SeveralComplexVariables

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Every scalar analytic function on `U` extends to the larger set `V`. Topological hypotheses and
maximality are separate; no extension outside the ambient space is intended. -/
@[expose] def IsCommonAnalyticExtension (U V : Set E) : Prop :=
  U ⊆ V ∧ ∀ f : E → ℂ, AnalyticOnNhd ℂ f U →
    ∃ g, AnalyticOnNhd ℂ g V ∧ EqOn g f U

/-- Construct a common extension property from containment and extension of each scalar analytic
function. -/
theorem isCommonAnalyticExtension_of_forall {U V : Set E} (hUV : U ⊆ V)
    (he : ∀ f : E → ℂ, AnalyticOnNhd ℂ f U →
      ∃ g, AnalyticOnNhd ℂ g V ∧ EqOn g f U) : IsCommonAnalyticExtension U V :=
  ⟨hUV, he⟩

/-- A common extension pair includes the original set in the extension set. -/
theorem IsCommonAnalyticExtension.subset {U V : Set E} (h : IsCommonAnalyticExtension U V) :
    U ⊆ V := h.1

/-- Apply a common extension property to a scalar analytic function. -/
theorem IsCommonAnalyticExtension.exists_extension {U V : Set E}
    (h : IsCommonAnalyticExtension U V) {f : E → ℂ} (hf : AnalyticOnNhd ℂ f U) :
    ∃ g, AnalyticOnNhd ℂ g V ∧ EqOn g f U := h.2 f hf

/-- Every set is a common extension domain for itself. -/
theorem isCommonAnalyticExtension_refl (U : Set E) : IsCommonAnalyticExtension U U :=
  ⟨Subset.rfl, fun f hf => ⟨f, hf, fun _ _ => rfl⟩⟩

/-- Common extension composes. -/
theorem IsCommonAnalyticExtension.trans {U V W : Set E}
    (hUV : IsCommonAnalyticExtension U V) (hVW : IsCommonAnalyticExtension V W) :
    IsCommonAnalyticExtension U W := by
  refine ⟨hUV.1.trans hVW.1, fun f hf => ?_⟩
  obtain ⟨g, hg, he⟩ := hUV.2 f hf
  obtain ⟨k, hk, he'⟩ := hVW.2 g hg
  exact ⟨k, hk, (he'.mono hUV.1).trans he⟩

/-- An omitted scalar value remains omitted on a connected common extension domain. -/
theorem IsCommonAnalyticExtension.ne_on {U V : Set E} (h : IsCommonAnalyticExtension U V)
    (ho : IsOpen U) (hne : U.Nonempty) (hc : IsPreconnected V)
    {f : E → ℂ} (hf : AnalyticOnNhd ℂ f V) {c : ℂ} (hno : ∀ z ∈ U, f z ≠ c) :
    ∀ z ∈ V, f z ≠ c := by
  have hi : AnalyticOnNhd ℂ (fun z => (f z - c)⁻¹) U :=
    fun z hz => ((hf z (h.1 hz)).sub analyticAt_const).inv (sub_ne_zero.mpr (hno z hz))
  obtain ⟨g, hg, he⟩ := h.2 _ hi
  have hp : AnalyticOnNhd ℂ (fun z => (f z - c) * g z) V :=
    (hf.sub analyticOnNhd_const).mul hg
  obtain ⟨a, ha⟩ := hne
  have he₁ : (fun z => (f z - c) * g z) =ᶠ[𝓝 a] (fun _ => (1 : ℂ)) := by
    filter_upwards [ho.mem_nhds ha] with z hz
    rw [he hz]
    exact mul_inv_cancel₀ (sub_ne_zero.mpr (hno z hz))
  have hp₁ := hp.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const hc (h.1 ha) he₁
  intro z hz heq
  have := hp₁ hz
  simp [heq] at this

/-- A scalar analytic function on a connected common extension domain has exactly its original
range. This is the Euclidean version of Proposition 2.9.2. -/
theorem IsCommonAnalyticExtension.image_eq {U V : Set E} (h : IsCommonAnalyticExtension U V)
    (ho : IsOpen U) (hne : U.Nonempty) (hc : IsPreconnected V)
    {f : E → ℂ} (hf : AnalyticOnNhd ℂ f V) : f '' V = f '' U := by
  classical
  apply Subset.antisymm _ (image_mono h.1)
  rintro c ⟨z, hz, rfl⟩
  by_contra hn
  have hno : ∀ w ∈ U, f w ≠ f z := fun w hw he => hn ⟨w, hw, he⟩
  exact h.ne_on ho hne hc hf hno z hz rfl

/-- A common extension domain lies in the real convex hull of the original domain. The proof uses
real convex separation, complexification of the separating functional, and preservation of
omitted values. This assertion involves no abstract envelopes. -/
theorem IsCommonAnalyticExtension.subset_convexHull
    {U V : Set E} (h : IsCommonAnalyticExtension U V) (ho : IsOpen U)
    (hne : U.Nonempty) (hc : IsPreconnected V) : V ⊆ convexHull ℝ U := by
  intro z hz
  by_contra hn
  obtain ⟨l, hl⟩ := geometric_hahn_banach_open_point (convex_convexHull ℝ U)
    (ho.convexHull (𝕜 := ℝ)) hn
  let L : E →L[ℂ] ℂ := l.extendRCLike
  have hno : ∀ w ∈ U, L w ≠ L z := by
    intro w hw he
    have he' : l w = l z := by
      simpa only [L, StrongDual.re_extendRCLike_apply] using
        congrArg (RCLike.re : ℂ → ℝ) he
    exact (ne_of_lt (hl w (_root_.subset_convexHull ℝ U hw))) he'
  exact h.ne_on ho hne hc (fun w _ => L.analyticAt w) hno z hz rfl

end SeveralComplexVariables

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
