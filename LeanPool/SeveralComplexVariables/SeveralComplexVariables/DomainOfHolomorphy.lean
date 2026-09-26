/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.CommonExtension

/-!
# Local continuation and domains of holomorphy

Common continuation from `U` to `V` requires agreement only on a specified overlap `W`. It does
not require `U ⊆ V`, or agreement on every component of `U ∩ V`. `IsDomainOfHolomorphy` excludes
such a common continuation outside `U`. `IsDomainOfExistence` excludes continuation of one
specified scalar function. Openness and connectedness of `U` are separate; the predicates also
apply to disconnected open sets. The whole space and the empty set are included.

References: [Jakóbczak–Jarnicki][JakobczakJarnicki2021] §2.7; [Scheidemann][Scheidemann2005]
§7.2; [Boas][Boas2013] §4.2.3. These definitions do not construct Riemann domains or envelopes
of holomorphy.

## Main definitions

* `HasCommonAnalyticContinuation`: All scalar analytic functions on `U` continue to `V`, with
  agreement on `W`.
* `IsDomainOfHolomorphy`: No common continuation through a nonempty open overlap reaches outside
  `U`.
* `IsDomainOfExistence`: A scalar function is analytic on `U` and has no continuation beyond it from
  any nonempty open overlap.

## Main results

* `IsDomainOfExistence.isDomainOfHolomorphy`: The domain of existence of one function is a domain of
  holomorphy.
* `IsDomainOfHolomorphy.eq_of_commonExtension`: A domain of holomorphy admits no proper connected
  common extension containing it.
* `isDomainOfHolomorphy_of_entire_separators`: Entire functions vanishing at each exterior point but
  nowhere on `U` obstruct all common continuation outside `U`, by applying the identity theorem to
  their reciprocals.
* `isDomainOfHolomorphy_complex`: Every subset of the complex plane satisfies the analytic
  continuation obstruction; in particular every planar open set is a domain of holomorphy.
* `isDomainOfHolomorphy_pi`: Finite products of planar open sets are domains of holomorphy.
* `isDomainOfHolomorphy_of_convex`: Every real-convex open subset of a finite-dimensional complex
  normed space is a domain of holomorphy.
* `IsDomainOfHolomorphy.image_equiv`: The domain-of-holomorphy property is invariant under
  continuous linear equivalences.

## References

* [H. P. Boas, *Lecture Notes on Several Complex Variables*][Boas2013]
* [P. Jakóbczak and M. Jarnicki, *Lectures on Holomorphic Functions of Several Complex
  Variables*][JakobczakJarnicki2021]
* [V. Scheidemann, *Introduction to Complex Analysis in Several Variables*][Scheidemann2005]
-/

public noncomputable section

open Set Filter
open scoped Topology

namespace SeveralComplexVariables

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- All scalar analytic functions on `U` continue to `V`, with agreement on `W`. Containment and
topological assumptions are supplied separately. -/
@[expose] def HasCommonAnalyticContinuation (U V W : Set E) : Prop :=
  ∀ f : E → ℂ, AnalyticOnNhd ℂ f U →
    ∃ g : E → ℂ, AnalyticOnNhd ℂ g V ∧ EqOn g f W

/-- No common continuation through a nonempty open overlap reaches outside `U`. For open `U`, this
is the domain-of-holomorphy property, without imposing connectedness. -/
@[expose] def IsDomainOfHolomorphy (U : Set E) : Prop :=
  ∀ V W : Set E, IsOpen V → IsConnected V → IsOpen W → W.Nonempty →
    W ⊆ U → W ⊆ V → HasCommonAnalyticContinuation U V W → V ⊆ U

/-- A scalar function is analytic on `U` and has no continuation beyond it from any nonempty open
overlap. This is the strong, local meaning of domain of existence. -/
@[expose] def IsDomainOfExistence (U : Set E) (f : E → ℂ) : Prop :=
  AnalyticOnNhd ℂ f U ∧
    ∀ V W : Set E, IsOpen V → IsConnected V → IsOpen W → W.Nonempty →
      W ⊆ U → W ⊆ V → (∃ g, AnalyticOnNhd ℂ g V ∧ EqOn g f W) → V ⊆ U

/-- The domain-of-holomorphy property is invariant under continuous linear equivalences. -/
theorem IsDomainOfHolomorphy.image_equiv {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {U : Set E} (h : IsDomainOfHolomorphy U) (L : E ≃L[ℂ] F) :
    IsDomainOfHolomorphy (L '' U) := by
  intro V W hV hVc hW hWne hWU hWV hcont
  have himg : ∀ z : F, z ∈ L '' U ↔ L.symm z ∈ U := fun z => by
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa using hx
    · intro hz
      exact ⟨L.symm z, hz, L.apply_symm_apply z⟩
  have hV' : IsOpen (L ⁻¹' V) := hV.preimage L.continuous
  have hVc' : IsConnected (L ⁻¹' V) := by
    rw [← L.image_symm_eq_preimage]
    exact hVc.image _ L.symm.continuous.continuousOn
  have hW' : IsOpen (L ⁻¹' W) := hW.preimage L.continuous
  have hWne' : (L ⁻¹' W).Nonempty := by
    obtain ⟨w, hw⟩ := hWne
    exact ⟨L.symm w, by simpa using hw⟩
  have hWU' : L ⁻¹' W ⊆ U := fun z hz => by
    have := (himg (L z)).mp (hWU hz)
    simpa using this
  have hWV' : L ⁻¹' W ⊆ L ⁻¹' V := fun z hz => hWV hz
  have hcont' : HasCommonAnalyticContinuation U (L ⁻¹' V) (L ⁻¹' W) := by
    intro f hf
    have hf' : AnalyticOnNhd ℂ (f ∘ L.symm) (L '' U) :=
      hf.comp (L.symm.toContinuousLinearMap.analyticOnNhd _) fun z hz => (himg z).mp hz
    obtain ⟨g, hg, hgf⟩ := hcont _ hf'
    refine ⟨g ∘ L, hg.comp (L.toContinuousLinearMap.analyticOnNhd _) fun z hz => hz,
      fun z hz => ?_⟩
    have := hgf hz
    simpa using this
  have hsub : L ⁻¹' V ⊆ U := h _ _ hV' hVc' hW' hWne' hWU' hWV' hcont'
  intro z hz
  rw [himg]
  exact hsub (by simpa using hz)

/-- A common extension to a containing set is a common continuation on any smaller overlap. -/
theorem IsCommonAnalyticExtension.hasCommonAnalyticContinuation {U V W : Set E}
    (h : IsCommonAnalyticExtension U V) (hWU : W ⊆ U) :
    HasCommonAnalyticContinuation U V W := by
  intro f hf
  obtain ⟨g, hg, he⟩ := h.exists_extension hf
  exact ⟨g, hg, he.mono hWU⟩

/-- The domain of existence of one function is a domain of holomorphy. -/
theorem IsDomainOfExistence.isDomainOfHolomorphy {U : Set E} {f : E → ℂ}
    (h : IsDomainOfExistence U f) : IsDomainOfHolomorphy U :=
  fun V W hV hc hW hn hWU hWV he => h.2 V W hV hc hW hn hWU hWV (he f h.1)

/-- The whole ambient space is a domain of holomorphy. -/
theorem isDomainOfHolomorphy_univ : IsDomainOfHolomorphy (univ : Set E) :=
  fun _ _ _ _ _ _ _ _ _ => subset_univ _

/-- The empty open set satisfies the domain-of-holomorphy property vacuously. -/
theorem isDomainOfHolomorphy_empty : IsDomainOfHolomorphy (∅ : Set E) := by
  intro V W _ _ _ hn hWU _ _
  obtain ⟨w, hw⟩ := hn
  exact (hWU hw).elim

/-- A function analytic on the whole space has that space as its domain of existence. -/
theorem isDomainOfExistence_univ {f : E → ℂ} (hf : AnalyticOnNhd ℂ f univ) :
    IsDomainOfExistence univ f := ⟨hf, fun _ _ _ _ _ _ _ _ _ => subset_univ _⟩

/-- A domain of holomorphy admits no proper connected common extension containing it. -/
theorem IsDomainOfHolomorphy.eq_of_commonExtension {U V : Set E}
    (h : IsDomainOfHolomorphy U) (hU : IsOpen U) (hn : U.Nonempty)
    (hV : IsOpen V) (hc : IsConnected V) (he : IsCommonAnalyticExtension U V) : V = U :=
  Subset.antisymm
    (h V U hV hc hU hn Subset.rfl he.subset
      (he.hasCommonAnalyticContinuation Subset.rfl)) he.subset

/-- Entire functions vanishing at each exterior point but nowhere on `U` obstruct all common
continuation outside `U`, by applying the identity theorem to their reciprocals. -/
theorem isDomainOfHolomorphy_of_entire_separators {U : Set E}
    (hsep : ∀ a ∉ U, ∃ q : E → ℂ, AnalyticOnNhd ℂ q univ ∧
      q a = 0 ∧ ∀ z ∈ U, q z ≠ 0) : IsDomainOfHolomorphy U := by
  intro V W _ hc hW hn hWU hWV he a ha
  by_contra hna
  obtain ⟨q, hq, hqa, hqU⟩ := hsep a hna
  have hi : AnalyticOnNhd ℂ (fun z => (q z)⁻¹) U :=
    fun z hz => (hq z (mem_univ z)).inv (hqU z hz)
  obtain ⟨g, hg, hge⟩ := he _ hi
  have hp : AnalyticOnNhd ℂ (fun z => q z * g z) V := (hq.mono (subset_univ V)).mul hg
  obtain ⟨w, hw⟩ := hn
  have hlocal : (fun z => q z * g z) =ᶠ[𝓝 w] (fun _ => (1 : ℂ)) := by
    filter_upwards [hW.mem_nhds hw] with z hz
    rw [hge hz, mul_inv_cancel₀ (hqU z (hWU hz))]
  have heq := hp.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const
    hc.isPreconnected (hWV hw) hlocal
  have hbad := heq ha
  simp [hqa] at hbad

/-- Every subset of the complex plane satisfies the analytic continuation obstruction; in particular
every planar open set is a domain of holomorphy. -/
theorem isDomainOfHolomorphy_complex (U : Set ℂ) : IsDomainOfHolomorphy U := by
  apply isDomainOfHolomorphy_of_entire_separators
  intro a ha
  refine ⟨fun z => z - a, analyticOnNhd_id.sub analyticOnNhd_const, sub_self a, ?_⟩
  intro z hz he
  exact ha (sub_eq_zero.mp he ▸ hz)

/-- Finite products of planar open sets are domains of holomorphy. The continuation obstruction
itself holds for arbitrary planar factors and includes an empty index type. -/
theorem isDomainOfHolomorphy_pi {ι : Type*} [Fintype ι] (S : ι → Set ℂ) :
    IsDomainOfHolomorphy (Set.pi univ S) := by
  apply isDomainOfHolomorphy_of_entire_separators
  intro a ha
  have hnot : ¬ ∀ i, a i ∈ S i := by
    intro h
    exact ha (fun i _ => h i)
  obtain ⟨i, hi⟩ := not_forall.mp hnot
  refine ⟨fun z => z i - a i,
    ((ContinuousLinearMap.proj i : (ι → ℂ) →L[ℂ] ℂ).analyticOnNhd univ).sub
      analyticOnNhd_const, sub_self _, ?_⟩
  intro z hz he
  apply hi
  rw [← sub_eq_zero.mp he]
  exact hz i (mem_univ i)

/-- Every real-convex open subset of a finite-dimensional complex normed space is a domain of
holomorphy. A separating real functional is complexified to give a pole. -/
theorem isDomainOfHolomorphy_of_convex {U : Set E}
    (hU : Convex ℝ U) (ho : IsOpen U) : IsDomainOfHolomorphy U := by
  apply isDomainOfHolomorphy_of_entire_separators
  intro a ha
  obtain ⟨l, hl⟩ := geometric_hahn_banach_open_point hU ho ha
  let L : E →L[ℂ] ℂ := l.extendRCLike
  refine ⟨fun z => L z - L a, (L.analyticOnNhd univ).sub analyticOnNhd_const, sub_self _, ?_⟩
  intro z hz he
  have he' : l z = l a := by
    simpa only [L, StrongDual.re_extendRCLike_apply] using
      congrArg (RCLike.re : ℂ → ℝ) (sub_eq_zero.mp he)
  exact (ne_of_lt (hl z hz)) he'

end SeveralComplexVariables

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
