/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# One-variable extension across analytic zero sets

Mathlib's Banach-valued isolated-singularity theorem applies at every zero of a nonzero scalar
analytic function. Redefining the function by its punctured limit at each zero gives one
extension on the whole open set. This is the slice theorem used in the several-variable Riemann
extension argument.

## Main results

`exists_analyticOnNhd_extension_zeroSet_oneVariable` extends a Banach-valued holomorphic
function across the zeros of a nonzero scalar analytic function of one variable.
-/

public noncomputable section

open Filter Function Metric Set
open scoped Topology

namespace SeveralComplexVariables

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- A bounded Banach-valued function analytic off the zeros of a nonzero one-variable analytic
function extends across all of those zeros. Bounds are needed only near zeros. -/
theorem exists_analyticOnNhd_extension_zeroSet_oneVariable
    {U : Set ℂ} (hU : IsOpen U) (hc : IsPreconnected U)
    {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g U) (hne : ∃ z ∈ U, g z ≠ 0)
    {f : ℂ → F} (hf : AnalyticOnNhd ℂ f (U \ g ⁻¹' {0}))
    (hb : ∀ a ∈ U, g a = 0 → ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ,
      ∀ z ∈ ball a r ∩ (U \ g ⁻¹' {0}), ‖f z‖ ≤ C) :
    ∃ f' : ℂ → F, AnalyticOnNhd ℂ f' U ∧ EqOn f' f (U \ g ⁻¹' {0}) := by
  classical
  let f' : ℂ → F := fun z => if g z = 0 then limUnder (𝓝[≠] z) f else f z
  refine ⟨f', ?_, fun z hz => by simp [f', show g z ≠ 0 from hz.2]⟩
  intro a ha
  by_cases hga : g a = 0
  · have hnloc : ¬ g =ᶠ[𝓝 a] 0 := by
      intro h
      obtain ⟨b, hb, hgb⟩ := hne
      exact hgb (hg.eqOn_zero_of_preconnected_of_eventuallyEq_zero hc ha h hb)
    have hisol := ((hg a ha).eventually_eq_zero_or_eventually_ne_zero).resolve_left hnloc
    obtain ⟨r, hr, C, hC⟩ := hb a ha hga
    have he : ∀ᶠ z in 𝓝 a, z ≠ a → g z ≠ 0 := eventually_nhdsWithin_iff.mp hisol
    obtain ⟨s, hs, hsa⟩ := Metric.mem_nhds_iff.mp
      (inter_mem (hU.mem_nhds ha) (inter_mem (ball_mem_nhds a hr) he))
    have hdiff : DifferentiableOn ℂ f (ball a s \ {a}) := by
      intro z hz
      exact (hf z ⟨(hsa hz.1).1, (hsa hz.1).2.2 hz.2⟩).differentiableAt.differentiableWithinAt
    have hbound : BddAbove ((norm ∘ f) '' (ball a s \ {a})) := by
      refine ⟨C, ?_⟩
      rintro _ ⟨z, hz, rfl⟩
      exact hC z ⟨(hsa hz.1).2.1, (hsa hz.1).1, (hsa hz.1).2.2 hz.2⟩
    have hd := Complex.differentiableOn_update_limUnder_of_bddAbove
      (ball_mem_nhds a hs) hdiff hbound
    have han : AnalyticAt ℂ (update f a (limUnder (𝓝[≠] a) f)) a :=
      hd.analyticAt (ball_mem_nhds a hs)
    apply (analyticAt_congr (g := update f a (limUnder (𝓝[≠] a) f)) ?_).mpr han
    filter_upwards [he] with z hz
    by_cases hza : z = a
    · subst z
      simp [f', hga]
    · simp [f', hz hza, hza]
  · have he : f' =ᶠ[𝓝 a] f := by
      filter_upwards [(hg a ha).continuousAt.eventually_ne hga] with z hz
      simp [f', hz]
    exact (analyticAt_congr he).mpr (hf a ⟨ha, hga⟩)

end SeveralComplexVariables

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
