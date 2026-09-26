/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Module.Connected

/-!
# Identity-principle consequences for zero sets

The nonvanishing locus of a nonzero analytic function is dense in its connected open domain,
which gives uniqueness of continuous extensions across its zero set. A product of two scalar
analytic functions vanishes near a point only if one factor does. These results support
removability and analytic germs without depending on Hartogs extension or local-ring theory.

References: [Scheidemann][Scheidemann2005] (2005), Sections 4.1--4.2;
[Korevaar–Wiegerinck][KorevaarWiegerinck2017] (2017), Sections 4.6--4.7. The density and
extension-uniqueness results allow normed vector targets.

## Main results

`subset_closure_nonzero_of_analyticOnNhd` is density of the nonvanishing locus.
`eqOn_of_eqOn_nonzero_of_analyticOnNhd` is uniqueness of continuous extensions across a zero
set. `eventuallyEq_zero_or_eventuallyEq_zero_of_mul` is the product rule for vanishing germs.

## References

* [J. Korevaar and J. Wiegerinck, *Several Complex Variables*][KorevaarWiegerinck2017]
* [V. Scheidemann, *Introduction to Complex Analysis in Several Variables*][Scheidemann2005]
-/

public section

open Filter Metric Set
open scoped Topology

namespace SeveralComplexVariables

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- A nonzero analytic function on a connected open set is nonzero arbitrarily near each point of
that set. No completeness or finite-dimensionality assumption is needed. -/
theorem exists_ne_zero_mem_ball_of_analyticOnNhd {U : Set E} {f : E → F}
    (hU : IsOpen U) (hconn : IsPreconnected U) (hf : AnalyticOnNhd ℂ f U)
    (hne : ∃ z ∈ U, f z ≠ 0) {x : E} (hx : x ∈ U) {r : ℝ} (hr : 0 < r) :
    ∃ y ∈ U, y ∈ ball x r ∧ f y ≠ 0 := by
  by_contra! h
  have hzero : f =ᶠ[𝓝 x] 0 := by
    filter_upwards [hU.mem_nhds hx, ball_mem_nhds x hr] with y hy hyr
    exact h y hy hyr
  obtain ⟨z, hz, hnz⟩ := hne
  exact hnz (hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero hconn hx hzero hz)

/-- The nonvanishing locus of a nonzero analytic function is dense in its connected open domain. The
closure is taken in the ambient normed space. -/
theorem subset_closure_nonzero_of_analyticOnNhd {U : Set E} {f : E → F}
    (hU : IsOpen U) (hconn : IsPreconnected U) (hf : AnalyticOnNhd ℂ f U)
    (hne : ∃ z ∈ U, f z ≠ 0) : U ⊆ closure {z | z ∈ U ∧ f z ≠ 0} := by
  intro x hx
  rw [Metric.mem_closure_iff]
  intro r hr
  obtain ⟨y, hy, hyr, hny⟩ :=
    exists_ne_zero_mem_ball_of_analyticOnNhd hU hconn hf hne hx hr
  exact ⟨y, ⟨hy, hny⟩, by simpa [dist_comm] using hyr⟩

/-- Continuous extensions across the zero set of a nonzero analytic function are unique on the
domain. Their values outside the domain are unrestricted. -/
theorem eqOn_of_eqOn_nonzero_of_analyticOnNhd
    {G : Type*} [TopologicalSpace G] [T2Space G]
    {U : Set E} {f : E → F} {g h : E → G}
    (hU : IsOpen U) (hconn : IsPreconnected U) (hf : AnalyticOnNhd ℂ f U)
    (hne : ∃ z ∈ U, f z ≠ 0) (hg : ContinuousOn g U) (hh : ContinuousOn h U)
    (heq : EqOn g h {z | z ∈ U ∧ f z ≠ 0}) : EqOn g h U :=
  heq.of_subset_closure hg hh (fun _ hz => hz.1)
    (subset_closure_nonzero_of_analyticOnNhd hU hconn hf hne)

/-- If a product of two analytic functions vanishes near a point, one factor vanishes near that
point. This is the identity principle on a sufficiently small connected ball. -/
theorem eventuallyEq_zero_or_eventuallyEq_zero_of_mul {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {f g : E → 𝕜} {x : E} (hf : AnalyticAt 𝕜 f x) (hg : AnalyticAt 𝕜 g x)
    (hfg : (fun y => f y * g y) =ᶠ[𝓝 x] 0) :
    f =ᶠ[𝓝 x] 0 ∨ g =ᶠ[𝓝 x] 0 := by
  let : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
    (hf.eventually_analyticAt.and (hg.eventually_analyticAt.and hfg))
  by_cases hzero : ∀ y ∈ ball x r, f y = 0
  · exact Or.inl (Filter.mem_of_superset (ball_mem_nhds x hr) hzero)
  · push Not at hzero
    obtain ⟨y, hy, hfy⟩ := hzero
    have hgzero : g =ᶠ[𝓝 y] 0 := by
      filter_upwards [isOpen_ball.mem_nhds hy,
        (hball hy).1.continuousAt.eventually_ne hfy] with z hz hfz
      exact (mul_eq_zero.mp (hball hz).2.2).resolve_left hfz
    have hgon : AnalyticOnNhd 𝕜 g (ball x r) := fun z hz => (hball hz).2.1
    exact Or.inr (Filter.mem_of_superset (ball_mem_nhds x hr)
      (hgon.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_ball hy hgzero))

end SeveralComplexVariables

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
