/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.Analyticity
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.RemovableSingularity.Gluing
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.RemovableSingularity.Local
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.ZeroSets.Basic

/-!
# Removable singularities and Riemann extension

A continuous function analytic away from a countable set is analytic everywhere on its open
domain. The proof applies the one-variable Cauchy theorem off countable sets to coordinate
slices, then uses Osgood. The exceptional set need not be closed or discrete.

This supplies a proved continuous-removal step toward the classical Riemann extension theory in
[Scheidemann][Scheidemann2005] (2005), Section 4.2, and [Jakóbczak–Jarnicki][JakobczakJarnicki2021]
(2021), Section 2.1. The codomain is a complex Banach space.

Locally bounded removal across a proper holomorphic zero set is proved by a local Cauchy
construction and gluing. It includes singular zero sets and does not require Weierstrass
preparation, division, or any algebraic regularity of the zero set.

## Main results

`analyticOnNhd_of_continuousOn_off_countable` (and `_pi`, `_finiteDimensional`) remove a countable
exceptional set from a continuous function. `exists_analyticOnNhd_extension_across_zeroSet` is
Riemann extension across a proper holomorphic zero set, for locally bounded Banach-valued maps.

## References

* [P. Jakóbczak and M. Jarnicki, *Lectures on Holomorphic Functions of Several Complex
  Variables*][JakobczakJarnicki2021]
* [J. Lebl, *Tasty Bits of Several Complex Variables: A Whirlwind Tour of the Subject*][Lebl2026]
* [V. Scheidemann, *Introduction to Complex Analysis in Several Variables*][Scheidemann2005]
* [T. Suwa, *Complex Analytic Geometry: From the Localization Viewpoint*][Suwa2024]
-/

public section

open Filter Function Metric Set
open scoped Topology

namespace SeveralComplexVariables

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- A continuous one-variable function analytic off a countable set is analytic on the whole open
domain, by Mathlib's Cauchy power-series theorem off countable sets. -/
theorem analyticOnNhd_of_continuousOn_off_countable {U S : Set ℂ} {f : ℂ → F}
    (hU : IsOpen U) (hS : S.Countable) (hc : ContinuousOn f U)
    (hf : AnalyticOnNhd ℂ f (U \ S)) : AnalyticOnNhd ℂ f U := by
  intro x hx
  obtain ⟨r, hr, hball⟩ := nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hx)
  exact (Complex.hasFPowerSeriesOnBall_of_differentiable_off_countable
    (R := ⟨r, hr.le⟩) hS (hc.mono hball)
    (fun z hz => (hf z ⟨hball (ball_subset_closedBall hz.1), hz.2⟩).differentiableAt)
    hr).analyticAt

/-- Continuous removal of a countable exceptional set in any finite complex coordinate space. Empty
coordinate types are allowed; no closedness of the exceptional set is required. -/
theorem analyticOnNhd_of_continuousOn_off_countable_pi
    {ι : Type*} [Fintype ι] {U S : Set (ι → ℂ)} {f : (ι → ℂ) → F}
    (hU : IsOpen U) (hS : S.Countable) (hc : ContinuousOn f U)
    (hf : AnalyticOnNhd ℂ f (U \ S)) : AnalyticOnNhd ℂ f U := by
  classical
  apply analyticOnNhd_pi_of_analyticOnNhd_update hU hc
  intro z hz i
  let L : ℂ → (ι → ℂ) := fun w => update z i w
  have hL : Continuous L := by fun_prop
  have hLd : Differentiable ℂ L := fun w => (hasDerivAt_update z i w).differentiableAt
  have hslice : AnalyticOnNhd ℂ (f ∘ L) ((L ⁻¹' U) \ (L ⁻¹' S)) := by
    intro w hw
    exact (hf (L w) ⟨hw.1, hw.2⟩).comp (hLd.analyticAt w)
  have hinj : Injective L := by
    intro v w heq
    simpa [L] using congrFun heq i
  exact analyticOnNhd_of_continuousOn_off_countable (hU.preimage hL)
    (hS.preimage hinj) (hc.comp hL.continuousOn (fun _ hw => hw)) hslice
    (z i) (by simpa [L] using hz)

/-- Continuous removal across a countable set in a finite-dimensional complex normed space.
Coordinates occur only in the proof. -/
theorem analyticOnNhd_of_continuousOn_off_countable_of_finiteDimensional
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {U S : Set E} {f : E → F} (hU : IsOpen U) (hS : S.Countable)
    (hc : ContinuousOn f U) (hf : AnalyticOnNhd ℂ f (U \ S)) :
    AnalyticOnNhd ℂ f U := by
  let e := (Module.finBasis ℂ E).equivFunL
  have ha : AnalyticOnNhd ℂ (f ∘ e.symm) (e.symm ⁻¹' U) := by
    apply analyticOnNhd_of_continuousOn_off_countable_pi
      (S := e.symm ⁻¹' S) (hU.preimage e.symm.continuous)
      (hS.preimage e.symm.injective)
      (hc.comp e.symm.continuous.continuousOn (fun _ hx => hx))
    intro z hz
    exact (hf _ ⟨hz.1, hz.2⟩).comp (e.symm.toContinuousLinearMap.analyticAt z)
  intro x hx
  simpa [Function.comp_def] using
    (ha (e x) (by simpa using hx)).comp (e.toContinuousLinearMap.analyticAt x)

/-- Local Riemann extension at a point where the defining scalar germ is nonzero. A bound near this
point suffices; no connectedness assumption is needed. -/
theorem exists_local_extension_across_zeroSet
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {U : Set E} (hU : IsOpen U) {g : E → ℂ} (hg : AnalyticOnNhd ℂ g U)
    {a : E} (ha : a ∈ U) (hne : ¬ g =ᶠ[𝓝 a] 0)
    {f : E → F} (hf : AnalyticOnNhd ℂ f (U \ g ⁻¹' {0}))
    (hb : ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ,
      ∀ z ∈ ball a r ∩ (U \ g ⁻¹' {0}), ‖f z‖ ≤ C) :
    ∃ (V : Set E) (f' : E → F), IsOpen V ∧ a ∈ V ∧ V ⊆ U ∧
      AnalyticOnNhd ℂ f' V ∧ EqOn f' f (V \ g ⁻¹' {0}) := by
  obtain ⟨r, hr, C, hC⟩ := hb
  obtain ⟨V, H, hV, haV, hVU, hH, he⟩ := exists_local_extension_zeroSet_of_bounded
    (hU.inter isOpen_ball) (hg.mono inter_subset_left) ⟨ha, mem_ball_self hr⟩ hne
    (hf.mono (by intro z hz; exact ⟨hz.1.1, hz.2⟩))
    (C := C) (by intro z hz; exact hC z ⟨hz.1.2, hz.1.1, hz.2⟩)
  exact ⟨V, H, hV, haV, fun z hz => (hVU hz).1, hH, he⟩

/-- Riemann extension on an arbitrary open set: it is enough that the defining scalar function has a
nonzero germ at every point. No connectedness assumption is needed. -/
theorem exists_analyticOnNhd_extension_across_zeroSet_of_nonzero_germs
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {U : Set E} (hU : IsOpen U) {g : E → ℂ} (hg : AnalyticOnNhd ℂ g U)
    (hne : ∀ a ∈ U, ¬ g =ᶠ[𝓝 a] 0)
    {f : E → F} (hf : AnalyticOnNhd ℂ f (U \ g ⁻¹' {0}))
    (hb : ∀ a ∈ U, g a = 0 → ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ,
      ∀ z ∈ ball a r ∩ (U \ g ⁻¹' {0}), ‖f z‖ ≤ C) :
    ∃ f' : E → F, AnalyticOnNhd ℂ f' U ∧ EqOn f' f (U \ g ⁻¹' {0}) := by
  apply exists_analyticOnNhd_extension_of_local sdiff_subset
    (subset_closure_nonzero_of_nonzero_germs hU hne)
  intro a ha
  by_cases hga : g a = 0
  · obtain ⟨V, H, hV, haV, hVU, hH, he⟩ :=
      exists_local_extension_across_zeroSet hU hg ha (hne a ha) hf (hb a ha hga)
    exact ⟨V, H, hV, haV, hVU, hH, fun z hz => he ⟨hz.1, hz.2.2⟩⟩
  · refine ⟨U \ g ⁻¹' {0}, f, ?_, ⟨ha, hga⟩, sdiff_subset, hf, fun _ _ => rfl⟩
    exact hg.continuousOn.isOpen_inter_preimage hU isClosed_singleton.isOpen_compl

omit [NormedSpace ℂ F] [CompleteSpace F] in
/-- Extensions across a scalar zero set are unique on the domain. The defining germs are assumed
nonzero locally, so the domain may have several connected components. -/
theorem eqOn_of_extension_across_zeroSet
    {E : Type*} [NormedAddCommGroup E]
    {U : Set E} (hU : IsOpen U) {g : E → ℂ} (hne : ∀ a ∈ U, ¬ g =ᶠ[𝓝 a] 0)
    {f f₁ f₂ : E → F} (h₁ : ContinuousOn f₁ U) (h₂ : ContinuousOn f₂ U)
    (he₁ : EqOn f₁ f (U \ g ⁻¹' {0})) (he₂ : EqOn f₂ f (U \ g ⁻¹' {0})) :
    EqOn f₁ f₂ U :=
  (he₁.trans he₂.symm).of_subset_closure h₁ h₂ sdiff_subset
    (subset_closure_nonzero_of_nonzero_germs hU hne)

/-- **Riemann extension across a holomorphic zero set.** A holomorphic function locally
bounded near the zero set of a nonzero scalar holomorphic function extends across that set.
See [Suwa][Suwa2024] Theorem 1.13, [Lebl][Lebl2026] Theorem 1.6.1, and
[Jakóbczak–Jarnicki][JakobczakJarnicki2021] Theorem 2.1.6.
The proof uses one-variable removability and parameter-dependent Cauchy integration.

The local bound controls only values outside the removed set. The given function may have
arbitrary values on that set. Extension uniqueness on `U` follows from the independently proved
density and continuous-uniqueness theorems in `ZeroSets.Basic`. -/
theorem exists_analyticOnNhd_extension_across_zeroSet
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {U : Set E} (hU : IsOpen U) (hconn : IsPreconnected U)
    {g : E → ℂ} (hg : AnalyticOnNhd ℂ g U) (hne : ∃ z ∈ U, g z ≠ 0)
    {f : E → F} (hf : AnalyticOnNhd ℂ f (U \ g ⁻¹' {0}))
    (hb : ∀ a ∈ U, g a = 0 → ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ,
      ∀ z ∈ ball a r ∩ (U \ g ⁻¹' {0}), ‖f z‖ ≤ C) :
    ∃ f' : E → F, AnalyticOnNhd ℂ f' U ∧ EqOn f' f (U \ g ⁻¹' {0}) := by
  apply exists_analyticOnNhd_extension_across_zeroSet_of_nonzero_germs hU hg ?_ hf hb
  intro a ha hzero
  obtain ⟨b, hbU, hgb⟩ := hne
  exact hgb (hg.eqOn_zero_of_preconnected_of_eventuallyEq_zero hconn ha hzero hbU)

end SeveralComplexVariables

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
