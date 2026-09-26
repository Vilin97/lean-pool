/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.AnalyticSet.Basic
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.ZeroSets.Connected

/-!
# Proper analytic subsets and the first Riemann extension theorem

An analytic subset with empty interior is locally contained in proper scalar zero sets. In a
preconnected domain, properness suffices. This connects local finite equations with the existing
Banach-valued removability and connected-complement theory. For disconnected domains we retain
the empty-interior condition explicitly.

References: [Range][Range1986] I, Theorem 3.8; [Fritzsche–Grauert][FritzscheGrauert2002] I,
8.1–8.2; [Scheidemann][Scheidemann2005] 4.1.6, 4.2.1–4.2.2.

## Main results

`IsAnalyticSet.interior_eq_empty` is emptiness of the interior of a proper analytic subset of a
preconnected domain. `IsAnalyticSet.locallyContainedInAnalyticZeroSet` places a proper analytic
subset in proper scalar zero sets. `IsAnalyticSet.exists_extension_of_locally_bounded` is the
first Riemann extension theorem for locally bounded Banach-valued maps.

## References

* [K. Fritzsche and H. Grauert, *From Holomorphic Functions to Complex
  Manifolds*][FritzscheGrauert2002]
* [R. M. Range, *Holomorphic Functions and Integral Representations in Several Complex
  Variables*][Range1986]
* [V. Scheidemann, *Introduction to Complex Analysis in Several Variables*][Scheidemann2005]
-/

public section

open Set Filter Metric
open scoped Topology

namespace SeveralComplexVariables

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- An analytic subset with interior in a preconnected ambient domain is the whole domain. -/
theorem IsAnalyticSet.eq_domain_of_interior_nonempty {U A : Set E}
    (hA : IsAnalyticSet U A) (hc : IsPreconnected U) (hne : (interior A).Nonempty) :
    A = U := by
  let : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ ℂ E
  apply Subset.antisymm hA.subset
  apply Subset.trans _ interior_subset
  apply hc.subset_of_closure_inter_subset isOpen_interior
  · obtain ⟨a, ha⟩ := hne
    exact ⟨a, hA.subset (interior_subset ha), ha⟩
  · rintro a ⟨haC, haU⟩
    obtain ⟨V, hV, haV, _, s, hs, he⟩ := hA.2 a haU
    obtain ⟨r, hr, hBV⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds haV)
    obtain ⟨b, hbI, hbr⟩ := Metric.mem_closure_iff.mp haC r hr
    have hbB : b ∈ ball a r := by simpa [dist_comm] using hbr
    have hzero : ∀ f ∈ s, EqOn f 0 (ball a r) := by
      intro f hfs
      apply ((hs f hfs).mono hBV).eqOn_zero_of_preconnected_of_eventuallyEq_zero
        isPreconnected_ball hbB
      filter_upwards [isOpen_interior.mem_nhds hbI, isOpen_ball.mem_nhds hbB] with z hzI hzB
      exact (he z (hBV hzB)).mp (interior_subset hzI) f hfs
    apply mem_interior_iff_mem_nhds.mpr
    filter_upwards [ball_mem_nhds a hr] with z hz
    exact (he z (hBV hz)).mpr (fun f hf => hzero f hf hz)

/-- A proper analytic subset of a preconnected domain has empty interior. -/
theorem IsAnalyticSet.interior_eq_empty {U A : Set E} (hA : IsAnalyticSet U A)
    (hc : IsPreconnected U) (hp : A ≠ U) : interior A = ∅ := by
  by_contra hn
  exact hp (hA.eq_domain_of_interior_nonempty hc (Set.nonempty_iff_ne_empty.mpr hn))

/-- An analytic subset with empty interior is locally contained in a proper scalar zero set. -/
theorem IsAnalyticSet.locallyContainedInAnalyticZeroSet {U A : Set E}
    (hA : IsAnalyticSet U A) (hi : interior A = ∅) : LocallyContainedInAnalyticZeroSet U A := by
  classical
  unfold LocallyContainedInAnalyticZeroSet
  intro a ha
  obtain ⟨V, hV, haV, hVU, s, hs, he⟩ := hA.2 a ha
  have hn : ∃ f ∈ s, ¬ f =ᶠ[𝓝 a] 0 := by
    by_contra! hall
    have hz : ∀ᶠ z in 𝓝 a, ∀ f ∈ s, f z = 0 := (eventually_all_finset s).mpr hall
    have haI : a ∈ interior A := by
      apply mem_interior_iff_mem_nhds.mpr
      filter_upwards [hV.mem_nhds haV, hz] with z hzV hzall
      exact (he z hzV).mpr hzall
    simp [hi] at haI
  obtain ⟨f, hfs, hfn⟩ := hn
  exact ⟨V, f, hV, haV, hVU, hs f hfs, hfn,
    fun z hz => (he z hz.1).mp hz.2 f hfs⟩

/-- The complement of an analytic subset with empty interior is dense in the ambient domain. -/
theorem IsAnalyticSet.subset_closure_sdiff {U A : Set E} (hA : IsAnalyticSet U A)
    (hi : interior A = ∅) : U ⊆ closure (U \ A) :=
  (hA.locallyContainedInAnalyticZeroSet hi).subset_closure

/-- Continuous extensions across a proper analytic exceptional set are unique on the domain. -/
theorem IsAnalyticSet.extension_unique {F : Type*} [TopologicalSpace F] [T2Space F]
    {U A : Set E} (hA : IsAnalyticSet U A) (hi : interior A = ∅)
    {f g h : E → F} (hg : ContinuousOn g U) (hh : ContinuousOn h U)
    (hgf : EqOn g f (U \ A)) (hhf : EqOn h f (U \ A)) : EqOn g h U :=
  (hA.locallyContainedInAnalyticZeroSet hi).extension_unique hg hh hgf hhf

/-- A proper analytic subset cannot disconnect a connected open domain. -/
theorem IsAnalyticSet.isConnected_sdiff [FiniteDimensional ℂ E]
    {U A : Set E} (hA : IsAnalyticSet U A) (hc : IsConnected U) (hp : A ≠ U) :
    IsConnected (U \ A) :=
  isConnected_sdiff_of_locallyContainedInAnalyticZeroSet hc hA.isOpen_sdiff
    (hA.locallyContainedInAnalyticZeroSet (hA.interior_eq_empty hc.isPreconnected hp))

/-- **First Riemann extension theorem.** Local boundedness is required only near the
exceptional set. Empty interior replaces componentwise properness on a disconnected domain.
The extension is unique on `U` by `IsAnalyticSet.extension_unique`. -/
theorem IsAnalyticSet.exists_extension_of_locally_bounded [FiniteDimensional ℂ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {U A : Set E} (hA : IsAnalyticSet U A) (hi : interior A = ∅) {f : E → F}
    (hf : AnalyticOnNhd ℂ f (U \ A))
    (hb : ∀ a ∈ A, ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ,
      ∀ z ∈ ball a r ∩ (U \ A), ‖f z‖ ≤ C) :
    ∃ g, AnalyticOnNhd ℂ g U ∧ EqOn g f (U \ A) := by
  apply exists_analyticOnNhd_extension_across_locallyContainedZeroSet hA.isOpen_sdiff
    (hA.locallyContainedInAnalyticZeroSet hi) hf
  intro a ha
  by_cases haA : a ∈ A
  · exact hb a haA
  · have hn : ∀ᶠ z in 𝓝 a, ‖f z‖ < ‖f a‖ + 1 :=
      ((hf a ⟨ha, haA⟩).continuousAt.norm).eventually_lt_const (by linarith)
    obtain ⟨r, hr, hbound⟩ := Metric.mem_nhds_iff.mp hn
    exact ⟨r, hr, ‖f a‖ + 1, fun z hz => (hbound hz.1).le⟩

end SeveralComplexVariables

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
