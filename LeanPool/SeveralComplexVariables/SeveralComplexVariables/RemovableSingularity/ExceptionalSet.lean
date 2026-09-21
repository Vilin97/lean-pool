/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.RemovableSingularity

/-!
# Riemann extension across locally contained exceptional sets

An exceptional set is locally contained in analytic zero sets if near each point of the open
domain it lies in the zero set of a nonzero scalar analytic germ. This is the condition called
“thin” in [Jakóbczak–Jarnicki][JakobczakJarnicki2021] §2.1. Closedness is a separate assumption,
expressed by openness of the complement within the open domain. Subsets and finite unions
satisfy the local containment condition.

Locally bounded Banach-valued analytic functions extend uniquely across such sets. The proof
restricts to a locally containing zero set, applies Riemann extension, then recovers agreement
on the larger original domain by density and continuity.

## Main results

`LocallyContainedInAnalyticZeroSet` is the thinness predicate: near every point of the open domain,
the set lies in a proper scalar analytic zero set.
`exists_analyticOnNhd_extension_across_locallyContainedZeroSet` is Riemann extension across such a
set for locally bounded Banach-valued maps.

## References

* [P. Jakóbczak and M. Jarnicki, *Lectures on Holomorphic Functions of Several Complex
  Variables*][JakobczakJarnicki2021]
-/

public section

open Filter Metric Set
open scoped Topology

namespace SeveralComplexVariables

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Near every point of `U`, the set `S` lies in the zero set of a nonzero scalar analytic germ. The
local neighborhoods imply openness of `U`; relative closedness of `S` and connectedness are not
imposed. -/
@[expose] def LocallyContainedInAnalyticZeroSet (U S : Set E) : Prop :=
  ∀ a ∈ U, ∃ (V : Set E) (g : E → ℂ), IsOpen V ∧ a ∈ V ∧ V ⊆ U ∧
    AnalyticOnNhd ℂ g V ∧ (¬ g =ᶠ[𝓝 a] 0) ∧ V ∩ S ⊆ g ⁻¹' {0}

/-- Local containment provides an open neighborhood inside the ambient domain at every point. -/
theorem LocallyContainedInAnalyticZeroSet.isOpen {U S : Set E}
    (h : LocallyContainedInAnalyticZeroSet U S) : IsOpen U := by
  rw [isOpen_iff_mem_nhds]
  intro a ha
  obtain ⟨V, g, hV, haV, hVU, _⟩ := h a ha
  exact Filter.mem_of_superset (hV.mem_nhds haV) hVU

/-- A subset inherits local containment in analytic zero sets. -/
theorem LocallyContainedInAnalyticZeroSet.mono {U S T : Set E}
    (h : LocallyContainedInAnalyticZeroSet U S) (hTS : T ⊆ S) :
    LocallyContainedInAnalyticZeroSet U T := by
  intro a ha
  obtain ⟨V, g, hV, haV, hVU, hg, hne, hS⟩ := h a ha
  exact ⟨V, g, hV, haV, hVU, hg, hne, fun z hz => hS ⟨hz.1, hTS hz.2⟩⟩

/-- The empty set is locally contained in analytic zero sets on any open domain. -/
theorem locallyContainedInAnalyticZeroSet_empty {U : Set E} (hU : IsOpen U) :
    LocallyContainedInAnalyticZeroSet U ∅ := by
  intro a ha
  refine ⟨U, fun _ => 1, hU, ha, Subset.rfl, analyticOnNhd_const, ?_, by simp⟩
  intro h
  have he := h.self_of_nhds
  simp at he

/-- The union of two locally contained exceptional sets is locally contained, using the product of
their local defining functions. -/
theorem LocallyContainedInAnalyticZeroSet.union {U S T : Set E}
    (hS : LocallyContainedInAnalyticZeroSet U S) (hT : LocallyContainedInAnalyticZeroSet U T) :
    LocallyContainedInAnalyticZeroSet U (S ∪ T) := by
  intro a ha
  obtain ⟨V, g, hV, haV, hVU, hg, hgn, hSg⟩ := hS a ha
  obtain ⟨W, k, hW, haW, _, hk, hkn, hTk⟩ := hT a ha
  refine ⟨V ∩ W, fun z => g z * k z, hV.inter hW, ⟨haV, haW⟩,
    fun z hz => hVU hz.1, (hg.mono inter_subset_left).mul (hk.mono inter_subset_right), ?_, ?_⟩
  · intro hzero
    exact (eventuallyEq_zero_or_eventuallyEq_zero_of_mul (hg a haV) (hk a haW) hzero).elim hgn hkn
  · rintro z ⟨⟨hzV, hzW⟩, hzS | hzT⟩
    · exact mul_eq_zero.mpr (Or.inl (hSg ⟨hzV, hzS⟩))
    · exact mul_eq_zero.mpr (Or.inr (hTk ⟨hzW, hzT⟩))

/-- A scalar zero set has the local containment property when all defining germs are nonzero. -/
theorem locallyContainedInAnalyticZeroSet_zeroSet {U : Set E} (hU : IsOpen U)
    {g : E → ℂ} (hg : AnalyticOnNhd ℂ g U) (hne : ∀ a ∈ U, ¬ g =ᶠ[𝓝 a] 0) :
    LocallyContainedInAnalyticZeroSet U (g ⁻¹' {0}) :=
  fun a ha => ⟨U, g, hU, ha, Subset.rfl, hg, hne a ha, inter_subset_right⟩

/-- The complement of a locally contained exceptional set is dense in the domain. -/
theorem LocallyContainedInAnalyticZeroSet.subset_closure {U S : Set E}
    (h : LocallyContainedInAnalyticZeroSet U S) : U ⊆ closure (U \ S) := by
  intro a ha
  obtain ⟨V, g, hV, haV, hVU, _, hne, hS⟩ := h a ha
  rw [Metric.mem_closure_iff]
  intro r hr
  by_contra! hnone
  apply hne
  filter_upwards [hV.mem_nhds haV, ball_mem_nhds a hr] with z hz hzr
  by_cases hzs : z ∈ S
  · exact hS ⟨hz, hzs⟩
  · exact False.elim (not_lt_of_ge (hnone z ⟨hVU hz, hzs⟩)
      (by simpa [dist_comm] using hzr))

/-- Extensions across a locally contained exceptional set are unique on the domain, with no
assumptions on their values outside the domain. -/
theorem LocallyContainedInAnalyticZeroSet.extension_unique
    {F : Type*} [TopologicalSpace F] [T2Space F] {U S : Set E}
    (h : LocallyContainedInAnalyticZeroSet U S) {f f₁ f₂ : E → F}
    (h₁ : ContinuousOn f₁ U) (h₂ : ContinuousOn f₂ U)
    (he₁ : EqOn f₁ f (U \ S)) (he₂ : EqOn f₂ f (U \ S)) : EqOn f₁ f₂ U :=
  (he₁.trans he₂.symm).of_subset_closure h₁ h₂ sdiff_subset h.subset_closure

/-- **Riemann extension for locally contained exceptional sets.** Relative closedness
is expressed by `IsOpen (U \ S)`. Local bounds control values on the complement.
The domain may be disconnected and the target may be any complex Banach space. -/
theorem exists_analyticOnNhd_extension_across_locallyContainedZeroSet
    [FiniteDimensional ℂ E] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [CompleteSpace F] {U S : Set E} (hUS : IsOpen (U \ S))
    (hS : LocallyContainedInAnalyticZeroSet U S) {f : E → F}
    (hf : AnalyticOnNhd ℂ f (U \ S))
    (hb : ∀ a ∈ U, ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ,
      ∀ z ∈ ball a r ∩ (U \ S), ‖f z‖ ≤ C) :
    ∃ H : E → F, AnalyticOnNhd ℂ H U ∧ EqOn H f (U \ S) := by
  apply exists_analyticOnNhd_extension_of_local sdiff_subset hS.subset_closure
  intro a ha
  obtain ⟨V, g, hV, haV, hVU, hg, hne, hSg⟩ := hS a ha
  obtain ⟨r, hr, hBV⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds haV)
  let B := ball a r
  have hBU : B ⊆ U := hBV.trans hVU
  have hgB : AnalyticOnNhd ℂ g B := hg.mono hBV
  have hnB : ∃ b ∈ B, g b ≠ 0 := by
    by_contra! h
    exact hne (Filter.mem_of_superset (ball_mem_nhds a hr) (fun z hz => h z hz))
  have hcomp : B \ g ⁻¹' {0} ⊆ U \ S := by
    intro z hz
    exact ⟨hBU hz.1, fun hzs => hz.2 (hSg ⟨hBV hz.1, hzs⟩)⟩
  obtain ⟨H, hH, he⟩ := exists_analyticOnNhd_extension_across_zeroSet
    isOpen_ball isPreconnected_ball hgB hnB (hf.mono hcomp) (by
      intro b hbB _
      obtain ⟨s, hs, C, hC⟩ := hb b (hBU hbB)
      exact ⟨s, hs, C, fun z hz => hC z ⟨hz.1, hcomp hz.2⟩⟩)
  have hng : ∀ b ∈ B, ¬ g =ᶠ[𝓝 b] 0 := by
    intro b hbB hz
    obtain ⟨c, hcB, hgc⟩ := hnB
    exact hgc (hgB.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_ball hbB hz hcB)
  refine ⟨B, H, isOpen_ball, mem_ball_self hr, hBU, hH, ?_⟩
  apply eqOn_of_extension_across_zeroSet (g := g) (isOpen_ball.inter hUS)
    (fun b hbO => hng b hbO.1) (hH.continuousOn.mono inter_subset_left)
    (hf.continuousOn.mono inter_subset_right)
    (fun z hz => he ⟨hz.1.1, hz.2⟩) (fun _ _ => rfl)

end SeveralComplexVariables

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
