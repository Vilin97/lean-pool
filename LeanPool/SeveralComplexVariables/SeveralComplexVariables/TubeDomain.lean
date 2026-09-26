/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.Normed.Module.Connected
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.DomainOfHolomorphy
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.TubeDomain.Basic
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.TubeDomain.Bochner

/-!
# Tube domains and Bochner's tube theorem

The tube over a real base consists of complex points whose real parts belong to that base. The
tube theorem extends functions to the tube over the real convex hull, inside the same complex
coordinate space. No abstract envelope is constructed. Connectedness of the base is essential to
the extension theorem. Banach-valued targets and empty coordinate types are retained. A
preconnected empty base is handled separately.

Bochner extension is proved by [Hörmander][Hormander1973]'s argument: the maximal star-convex
extension tube is convex by the parabolic disc hull lemma and Thullen's continuation lemma, and
a path argument handles connected bases (`TubeDomain/Bochner`). The statement for a general
finite index type is obtained by reindexing. Uniqueness of extensions and the convex-base
characterization of tube domains of holomorphy follow.

References: [Scheidemann][Scheidemann2005] §6.3; [Hörmander][Hormander1973] §2.5, Theorem
2.5.10.

## Main results

* `exists_extension_tubeDomain_convexHull`: **Bochner's tube theorem.** Every Banach-valued
  holomorphic function on a tube with preconnected open base extends to the tube over its real
  convex hull.

## References

* [L. Hörmander, *An Introduction to Complex Analysis in Several Variables*][Hormander1973]
* [V. Scheidemann, *Introduction to Complex Analysis in Several Variables*][Scheidemann2005]
-/

public noncomputable section

open Set Filter
open scoped Topology

namespace SeveralComplexVariables

variable {ι : Type*}

variable [Fintype ι]

/-- Bochner extension for a nonempty connected base, obtained by reindexing the coordinate
proof. This is the prerequisite for the empty-inclusive public theorem below. -/
private theorem exists_extension_tubeDomain_convexHull_nonempty {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℂ F] [CompleteSpace F] {Ω : Set (ι → ℝ)}
    (ho : IsOpen Ω) (hc : IsConnected Ω) {f : (ι → ℂ) → F}
    (hf : AnalyticOnNhd ℂ f (tubeDomain Ω)) :
    ∃ g : (ι → ℂ) → F, AnalyticOnNhd ℂ g (tubeDomain (convexHull ℝ Ω)) ∧
      EqOn g f (tubeDomain Ω) := by
  set e := Fintype.equivFin ι with he
  set L : (ι → ℝ) →ₗ[ℝ] (Fin (Fintype.card ι) → ℝ) := LinearMap.funLeft ℝ ℝ e.symm with hL
  have hLapply : ∀ x : ι → ℝ, L x = x ∘ e.symm := fun x => rfl
  have himg : L '' Ω = (fun x' : Fin (Fintype.card ι) → ℝ => x' ∘ e) ⁻¹' Ω := by
    ext x'
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa [hLapply, Function.comp_assoc] using hx
    · intro hx'
      refine ⟨x' ∘ e, hx', ?_⟩
      rw [hLapply, Function.comp_assoc, e.self_comp_symm, Function.comp_id]
  have hΩ'o : IsOpen (L '' Ω) := by
    rw [himg]
    exact ho.preimage (continuous_pi fun i => continuous_apply (e i))
  have hΩ'c : IsConnected (L '' Ω) :=
    hc.image L (continuous_pi fun j => continuous_apply (e.symm j)).continuousOn
  have hre : ∀ (z : ι → ℂ), rePi (z ∘ e.symm) = L (rePi z) := fun z => rfl
  have hre' : ∀ (z' : Fin (Fintype.card ι) → ℂ), rePi (z' ∘ e) = rePi z' ∘ e := fun z' => rfl
  -- the reindexing maps are analytic
  have hM : AnalyticOnNhd ℂ (fun z' : Fin (Fintype.card ι) → ℂ => z' ∘ e) univ :=
    (LinearMap.toContinuousLinearMap (LinearMap.funLeft ℂ ℂ e)).analyticOnNhd univ
  have hM' : AnalyticOnNhd ℂ (fun z : ι → ℂ => z ∘ e.symm) univ :=
    (LinearMap.toContinuousLinearMap (LinearMap.funLeft ℂ ℂ e.symm)).analyticOnNhd univ
  have hmaps : MapsTo (fun z' : Fin (Fintype.card ι) → ℂ => z' ∘ e) (tubeDomain (L '' Ω))
      (tubeDomain Ω) := by
    intro z' hz'
    rw [mem_tubeDomain, himg] at hz'
    rw [mem_tubeDomain, hre']
    exact hz'
  have hf' : AnalyticOnNhd ℂ (fun z' => f (z' ∘ e)) (tubeDomain (L '' Ω)) :=
    hf.comp (hM.mono (subset_univ _)) hmaps
  obtain ⟨g', hg', hg'f⟩ := exists_extension_tubeDomain_convexHull_fin hΩ'o hΩ'c hf'
  have hconv : L '' convexHull ℝ Ω = convexHull ℝ (L '' Ω) := LinearMap.image_convexHull L Ω
  have hmaps' : MapsTo (fun z : ι → ℂ => z ∘ e.symm) (tubeDomain (convexHull ℝ Ω))
      (tubeDomain (convexHull ℝ (L '' Ω))) := by
    intro z hz
    rw [mem_tubeDomain, hre, ← hconv]
    exact mem_image_of_mem L hz
  refine ⟨fun z => g' (z ∘ e.symm), hg'.comp (hM'.mono (subset_univ _)) hmaps', fun z hz => ?_⟩
  have hz' : z ∘ e.symm ∈ tubeDomain (L '' Ω) := by
    rw [mem_tubeDomain, hre]
    exact mem_image_of_mem L hz
  change g' (z ∘ e.symm) = f z
  rw [hg'f hz']
  simp only [Function.comp_assoc, e.symm_comp_self, Function.comp_id]

/-- **Bochner's tube theorem.** Every Banach-valued holomorphic function on a tube with
preconnected open base extends to the tube over its real convex hull. -/
theorem exists_extension_tubeDomain_convexHull {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℂ F] [CompleteSpace F] {Ω : Set (ι → ℝ)}
    (ho : IsOpen Ω) (hc : IsPreconnected Ω) {f : (ι → ℂ) → F}
    (hf : AnalyticOnNhd ℂ f (tubeDomain Ω)) :
    ∃ g : (ι → ℂ) → F, AnalyticOnNhd ℂ g (tubeDomain (convexHull ℝ Ω)) ∧
      EqOn g f (tubeDomain Ω) := by
  by_cases hn : Ω.Nonempty
  · exact exists_extension_tubeDomain_convexHull_nonempty ho ⟨hn, hc⟩ hf
  · have hΩ : Ω = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
    subst Ω
    exact ⟨f, by simp [tubeDomain], by simp [tubeDomain]⟩

/-- Uniqueness of a tube extension to the convexified base, independently of Bochner's existence
theorem. Only a nonempty open original base is needed. -/
theorem eqOn_of_tubeDomain_extension {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℂ F] {Ω : Set (ι → ℝ)}
    (ho : IsOpen Ω) (hn : Ω.Nonempty) {f g : (ι → ℂ) → F}
    (hf : AnalyticOnNhd ℂ f (tubeDomain (convexHull ℝ Ω)))
    (hg : AnalyticOnNhd ℂ g (tubeDomain (convexHull ℝ Ω)))
    (he : EqOn f g (tubeDomain Ω)) : EqOn f g (tubeDomain (convexHull ℝ Ω)) := by
  obtain ⟨a, ha⟩ := nonempty_tubeDomain hn
  apply hf.eqOn_of_preconnected_of_eventuallyEq hg
    (convex_tubeDomain (convex_convexHull ℝ Ω)).isPreconnected
    (tubeDomain_subset_convexHull_base Ω ha)
  filter_upwards [(isOpen_tubeDomain ho).mem_nhds ha] with z hz
  exact he hz

/-- The convexified tube is a common scalar extension domain, by Bochner's extension theorem,
without asserting a universal abstract envelope property. -/
theorem isCommonAnalyticExtension_tubeDomain_convexHull {Ω : Set (ι → ℝ)}
    (ho : IsOpen Ω) (hc : IsPreconnected Ω) :
    IsCommonAnalyticExtension (tubeDomain Ω) (tubeDomain (convexHull ℝ Ω)) :=
  isCommonAnalyticExtension_of_forall (tubeDomain_subset_convexHull_base Ω)
    (fun _ hf => exists_extension_tubeDomain_convexHull ho hc hf)

/-- A tube with preconnected open base is a domain of holomorphy exactly when its base is convex.
The forward implication uses Bochner's extension theorem. -/
theorem isDomainOfHolomorphy_tubeDomain_iff {Ω : Set (ι → ℝ)}
    (ho : IsOpen Ω) (hc : IsPreconnected Ω) :
    IsDomainOfHolomorphy (tubeDomain Ω) ↔ Convex ℝ Ω := by
  by_cases hn : Ω.Nonempty
  swap
  · have hΩ : Ω = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
    subst Ω
    exact ⟨fun _ => convex_empty, fun _ =>
      isDomainOfHolomorphy_of_convex (convex_tubeDomain convex_empty) (isOpen_tubeDomain ho)⟩
  constructor
  · intro h
    have he := h.eq_of_commonExtension (isOpen_tubeDomain ho) (nonempty_tubeDomain hn)
      (isOpen_tubeDomain (ho.convexHull (𝕜 := ℝ)))
      ⟨(nonempty_tubeDomain hn).mono (tubeDomain_subset_convexHull_base Ω),
        (convex_tubeDomain (convex_convexHull ℝ Ω)).isPreconnected⟩
      (isCommonAnalyticExtension_tubeDomain_convexHull ho hc)
    have heq : convexHull ℝ Ω = Ω := by
      apply Subset.antisymm _ (_root_.subset_convexHull ℝ Ω)
      intro x hx
      apply ofReal_mem_tubeDomain.mp
      rw [← he]
      exact ofReal_mem_tubeDomain.mpr hx
    rw [← heq]
    exact convex_convexHull ℝ Ω
  · intro h
    exact isDomainOfHolomorphy_of_convex (convex_tubeDomain h) (isOpen_tubeDomain ho)

end SeveralComplexVariables

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
