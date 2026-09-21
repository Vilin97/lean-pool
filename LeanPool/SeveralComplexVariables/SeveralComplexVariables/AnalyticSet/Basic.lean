/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Complex.Basic

/-!
# Analytic subsets of open complex domains

An analytic subset is locally the common zero set of finitely many scalar analytic functions.
Equations are required near every point of the ambient set, so relative closedness follows. The
local neighborhood requirement also implies that the ambient domain is open. No connectedness,
nonemptiness, or positive dimension is built in. Empty families define the whole domain.

Holomorphic defining equations and biholomorphic transport are treated separately in
`SeveralComplexVariables.AnalyticSet.Holomorphic`. This file uses analytic predicates directly
and does not depend on the SCV holomorphy–analyticity equivalence.

References: [Range][Range1986] I §3.2; [Fritzsche–Grauert][FritzscheGrauert2002] I §8;
[Scheidemann][Scheidemann2005] §4.1. No abstract analytic spaces or sheaf structures are
introduced.

## Main definitions

* `IsAnalyticSet`: `A` is an analytic subset of `U` if it is contained in `U` and is locally cut out
  by finitely many scalar analytic equations.

## Main results

* `isAnalyticSet_zeroSet`: A scalar analytic zero set, restricted to its domain, is analytic.
* `IsAnalyticSet.isOpen_sdiff`: Analytic subsets are relatively closed, expressed by their open
  complement in `U`.
* `IsAnalyticSet.inter`: Finite intersections of analytic subsets are analytic.
* `IsAnalyticSet.union`: Finite unions are defined by pairwise products of the local equations.
* `IsAnalyticSet.preimage`: Holomorphic preimages preserve analytic subsets.
* `IsAnalyticSet.prod`: Products of analytic subsets are analytic.
* `isAnalyticSet_of_local`: Analyticity of a subset can be checked on an open cover of its ambient
  domain.

## References

* [K. Fritzsche and H. Grauert, *From Holomorphic Functions to Complex
  Manifolds*][FritzscheGrauert2002]
* [R. M. Range, *Holomorphic Functions and Integral Representations in Several Complex
  Variables*][Range1986]
* [V. Scheidemann, *Introduction to Complex Analysis in Several Variables*][Scheidemann2005]
-/

public noncomputable section

open Set Filter
open scoped Topology

namespace SeveralComplexVariables

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- `A` is an analytic subset of `U` if it is contained in `U` and is locally cut out by finitely
many scalar analytic equations. The equations need not extend throughout `U`. -/
@[expose] def IsAnalyticSet (U A : Set E) : Prop :=
  A ⊆ U ∧ ∀ a ∈ U, ∃ V : Set E, IsOpen V ∧ a ∈ V ∧ V ⊆ U ∧
    ∃ s : Finset (E → ℂ), (∀ f ∈ s, AnalyticOnNhd ℂ f V) ∧
      ∀ z ∈ V, z ∈ A ↔ ∀ f ∈ s, f z = 0

/-- An analytic subset is contained in its ambient domain. -/
theorem IsAnalyticSet.subset {U A : Set E} (h : IsAnalyticSet U A) : A ⊆ U := h.1

/-- The local open neighborhoods in the definition cover the ambient domain. -/
theorem IsAnalyticSet.isOpen_domain {U A : Set E} (h : IsAnalyticSet U A) : IsOpen U := by
  rw [isOpen_iff_mem_nhds]
  intro a ha
  obtain ⟨V, hV, haV, hVU, _⟩ := h.2 a ha
  exact mem_of_superset (hV.mem_nhds haV) hVU

/-- A finite family of analytic equations defines an analytic subset. -/
theorem isAnalyticSet_commonZeroSet {U : Set E} (hU : IsOpen U)
    (s : Finset (E → ℂ)) (hs : ∀ f ∈ s, AnalyticOnNhd ℂ f U) :
    IsAnalyticSet U {z | z ∈ U ∧ ∀ f ∈ s, f z = 0} := by
  refine ⟨fun _ hz => hz.1, fun a ha => ⟨U, hU, ha, Subset.rfl, s, hs, ?_⟩⟩
  intro z hz
  exact and_iff_right hz

/-- A scalar analytic zero set, restricted to its domain, is analytic. -/
theorem isAnalyticSet_zeroSet {U : Set E} (hU : IsOpen U) {f : E → ℂ}
    (hf : AnalyticOnNhd ℂ f U) : IsAnalyticSet U (U ∩ f ⁻¹' {0}) := by
  classical
  change IsAnalyticSet U {z | z ∈ U ∧ f z = 0}
  simpa using isAnalyticSet_commonZeroSet hU {f} (by simpa using hf)

/-- The zero set of a finite-coordinate analytic map is analytic, including an empty coordinate
index type, when the zero set is the whole domain. -/
theorem isAnalyticSet_zeroSet_pi {ι : Type*} [Fintype ι] {U : Set E} (hU : IsOpen U)
    {f : E → (ι → ℂ)} (hf : AnalyticOnNhd ℂ f U) :
    IsAnalyticSet U (U ∩ f ⁻¹' {0}) := by
  classical
  let s : Finset (E → ℂ) := Finset.univ.image (fun i z => f z i)
  have hs : ∀ g ∈ s, AnalyticOnNhd ℂ g U := by
    intro g hg
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hg
    exact analyticOnNhd_pi_iff.mp hf i
  have h := isAnalyticSet_commonZeroSet hU s hs
  convert h using 1
  ext z
  constructor
  · rintro ⟨hzU, hfz⟩
    refine ⟨hzU, ?_⟩
    intro g hg
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hg
    exact congrFun hfz i
  · rintro ⟨hzU, hsz⟩
    refine ⟨hzU, ?_⟩
    funext i
    exact hsz (fun z => f z i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)

/-- The whole open domain is analytic, using no equations. -/
theorem isAnalyticSet_self {U : Set E} (hU : IsOpen U) : IsAnalyticSet U U := by
  simpa using isAnalyticSet_commonZeroSet hU ∅ (by simp)

/-- The empty set is analytic, using the constant equation `1 = 0`. -/
theorem isAnalyticSet_empty {U : Set E} (hU : IsOpen U) : IsAnalyticSet U ∅ := by
  simpa using isAnalyticSet_zeroSet hU (f := fun _ => 1) analyticOnNhd_const

/-- Analytic subsets restrict to smaller open domains. -/
theorem IsAnalyticSet.restrict {U A W : Set E} (h : IsAnalyticSet U A)
    (hW : IsOpen W) (hWU : W ⊆ U) : IsAnalyticSet W (W ∩ A) := by
  refine ⟨inter_subset_left, ?_⟩
  intro a ha
  obtain ⟨V, hV, haV, hVU, s, hs, he⟩ := h.2 a (hWU ha)
  refine ⟨W ∩ V, hW.inter hV, ⟨ha, haV⟩, inter_subset_left, s,
    fun f hf => (hs f hf).mono inter_subset_right, ?_⟩
  intro z hz
  exact (and_iff_right hz.1).trans (he z hz.2)

/-- Analyticity of a subset can be checked on an open cover of its ambient domain. -/
theorem isAnalyticSet_of_local {U A : Set E} (hAU : A ⊆ U)
    (h : ∀ a ∈ U, ∃ V, IsOpen V ∧ a ∈ V ∧ V ⊆ U ∧ IsAnalyticSet V (V ∩ A)) :
    IsAnalyticSet U A := by
  refine ⟨hAU, ?_⟩
  intro a ha
  obtain ⟨V, _, haV, hVU, hAV⟩ := h a ha
  obtain ⟨W, hW, haW, hWV, s, hs, he⟩ := hAV.2 a haV
  refine ⟨W, hW, haW, hWV.trans hVU, s, hs, ?_⟩
  intro z hz
  exact (and_iff_right (hWV hz)).symm.trans (he z hz)

/-- Analytic subsets are relatively closed, expressed by their open complement in `U`. -/
theorem IsAnalyticSet.isOpen_sdiff {U A : Set E} (h : IsAnalyticSet U A) :
    IsOpen (U \ A) := by
  classical
  rw [isOpen_iff_mem_nhds]
  rintro a ⟨haU, haA⟩
  obtain ⟨V, hV, haV, hVU, s, hs, he⟩ := h.2 a haU
  have hn : ¬ ∀ f ∈ s, f a = 0 := fun hall => haA ((he a haV).mpr hall)
  push Not at hn
  obtain ⟨f, hfs, hfa⟩ := hn
  filter_upwards [hV.mem_nhds haV, (hs f hfs a haV).continuousAt.eventually_ne hfa] with z hz hnz
  exact ⟨hVU hz, fun hzA => hnz ((he z hz).mp hzA f hfs)⟩

/-- Finite intersections of analytic subsets are analytic. -/
theorem IsAnalyticSet.inter {U A B : Set E} (hA : IsAnalyticSet U A)
    (hB : IsAnalyticSet U B) : IsAnalyticSet U (A ∩ B) := by
  classical
  refine ⟨inter_subset_left.trans hA.subset, ?_⟩
  intro a ha
  obtain ⟨V, hV, haV, hVU, s, hs, he⟩ := hA.2 a ha
  obtain ⟨W, hW, haW, _, t, ht, hk⟩ := hB.2 a ha
  refine ⟨V ∩ W, hV.inter hW, ⟨haV, haW⟩, inter_subset_left.trans hVU,
    s ∪ t, ?_, ?_⟩
  · intro f hf
    rcases Finset.mem_union.mp hf with hf | hf
    · exact (hs f hf).mono inter_subset_left
    · exact (ht f hf).mono inter_subset_right
  · intro z hz
    simp only [mem_inter_iff, he z hz.1, hk z hz.2, Finset.mem_union]
    exact ⟨fun h f hf => hf.elim (h.1 f) (h.2 f),
      fun h => ⟨fun f hf => h f (Or.inl hf), fun f hf => h f (Or.inr hf)⟩⟩

/-- Finite unions are defined by pairwise products of the local equations. -/
theorem IsAnalyticSet.union {U A B : Set E} (hA : IsAnalyticSet U A)
    (hB : IsAnalyticSet U B) : IsAnalyticSet U (A ∪ B) := by
  classical
  refine ⟨union_subset hA.subset hB.subset, ?_⟩
  intro a ha
  obtain ⟨V, hV, haV, hVU, s, hs, he⟩ := hA.2 a ha
  obtain ⟨W, hW, haW, _, t, ht, hk⟩ := hB.2 a ha
  refine ⟨V ∩ W, hV.inter hW, ⟨haV, haW⟩, inter_subset_left.trans hVU,
    (s ×ˢ t).image (fun p => p.1 * p.2), ?_, ?_⟩
  · intro f hf
    obtain ⟨⟨g, k⟩, hp, rfl⟩ := Finset.mem_image.mp hf
    exact ((hs g (Finset.mem_product.mp hp).1).mono inter_subset_left).mul
      ((ht k (Finset.mem_product.mp hp).2).mono inter_subset_right)
  · intro z hz
    constructor
    · intro hzAB f hf
      obtain ⟨⟨g, k⟩, hp, rfl⟩ := Finset.mem_image.mp hf
      rcases hzAB with hzA | hzB
      · exact mul_eq_zero.mpr (Or.inl ((he z hz.1).mp hzA g (Finset.mem_product.mp hp).1))
      · exact mul_eq_zero.mpr (Or.inr ((hk z hz.2).mp hzB k (Finset.mem_product.mp hp).2))
    · intro h
      by_cases hzA : z ∈ A
      · exact Or.inl hzA
      · right
        apply (hk z hz.2).mpr
        have hn : ¬ ∀ g ∈ s, g z = 0 := fun hall => hzA ((he z hz.1).mpr hall)
        push Not at hn
        obtain ⟨g, hg, hgz⟩ := hn
        intro k hkt
        exact (mul_eq_zero.mp (h (g * k)
          (Finset.mem_image.mpr ⟨(g, k), Finset.mem_product.mpr ⟨hg, hkt⟩, rfl⟩))).resolve_left hgz

/-- Holomorphic preimages preserve analytic subsets. -/
theorem IsAnalyticSet.preimage {U : Set E} {V B : Set F} (hB : IsAnalyticSet V B)
    (hU : IsOpen U) {f : E → F} (hf : AnalyticOnNhd ℂ f U) (hm : MapsTo f U V) :
    IsAnalyticSet U (U ∩ f ⁻¹' B) := by
  classical
  refine ⟨inter_subset_left, ?_⟩
  intro a ha
  obtain ⟨W, hW, hfaW, hWV, s, hs, he⟩ := hB.2 (f a) (hm ha)
  refine ⟨U ∩ f ⁻¹' W, hf.continuousOn.isOpen_inter_preimage hU hW,
    ⟨ha, hfaW⟩, inter_subset_left, s.image (fun g => g ∘ f), ?_, ?_⟩
  · intro g hg
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hg
    exact (hs k hk).comp (hf.mono inter_subset_left) (fun _ hz => hz.2)
  · intro z hz
    simpa [hz.1] using he (f z) hz.2

/-- Products of analytic subsets are analytic. -/
theorem IsAnalyticSet.prod {U A : Set E} {V B : Set F} (hA : IsAnalyticSet U A)
    (hB : IsAnalyticSet V B) : IsAnalyticSet (U ×ˢ V) (A ×ˢ B) := by
  have ho := hA.isOpen_domain.prod hB.isOpen_domain
  have h₁ := hA.preimage ho (f := Prod.fst) (fun _ _ => analyticAt_fst) (fun _ hz => hz.1)
  have h₂ := hB.preimage ho (f := Prod.snd) (fun _ _ => analyticAt_snd) (fun _ hz => hz.2)
  convert h₁.inter h₂ using 1
  ext z
  constructor
  · rintro ⟨hzA, hzB⟩
    exact ⟨⟨⟨hA.subset hzA, hB.subset hzB⟩, hzA⟩,
      ⟨⟨hA.subset hzA, hB.subset hzB⟩, hzB⟩⟩
  · rintro ⟨⟨_, hzA⟩, ⟨_, hzB⟩⟩
    exact ⟨hzA, hzB⟩

end SeveralComplexVariables

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
