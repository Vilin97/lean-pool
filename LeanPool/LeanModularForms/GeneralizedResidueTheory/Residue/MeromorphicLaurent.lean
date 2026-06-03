/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import LeanPool.LeanModularForms.GeneralizedResidueTheory.Residue.MeromorphicPrincipalPart
import LeanPool.LeanModularForms.GeneralizedResidueTheory.HomologicalCauchy

/-!
# Convex-Domain Contour Vanishing for Meromorphic Functions

Thin corollaries of the null-homologous theorems in `HomologicalCauchy.lean`,
specialized to convex domains via `isNullHomologous_of_convex`.

## Main Results

* `contourIntegral_eq_zero_of_meromorphic_residue_zero` -- single-pole vanishing on convex domain
* `contourIntegral_eq_zero_of_meromorphic_residue_zero_finset` -- multi-pole vanishing on convex
  domain

These are now thin wrappers around:
* `contourIntegral_eq_zero_of_meromorphic_residue_zero_nh`
* `contourIntegral_eq_zero_of_meromorphic_residue_zero_finset_nh`

## References

* Hungerbuhler-Wasem, arXiv:1808.00997v2, Theorem 3.3
* Mathlib `MeromorphicAt`, `meromorphicOrderAt`
-/

open Complex MeasureTheory Set Filter Topology Metric
open scoped Real Interval

attribute [local instance] Classical.propDecidable

noncomputable section

namespace GeneralizedResidueTheory

/-! ### Single-point vanishing theorem (convex corollary)

For a meromorphic function with zero residue at the unique singularity in a convex
domain, the contour integral vanishes. -/

/-- If `f` is meromorphic at `s` with `Res(f, s) = 0`, and `f` is differentiable on
`U \ {s}` for a convex open `U` containing `s`, then the contour integral of `f`
vanishes for any closed curve in `U` avoiding `s`.

This is a corollary of `contourIntegral_eq_zero_of_meromorphic_residue_zero_nh`
via `isNullHomologous_of_convex`. -/
theorem contourIntegral_eq_zero_of_meromorphic_residue_zero
    (f : ℂ → ℂ) (s : ℂ) (hf : MeromorphicAt f s) (hres : residueAt f s = 0)
    (U : Set ℂ) (hU : IsOpen U) (hU_convex : Convex ℝ U)
    (hf_diff : DifferentiableOn ℂ f (U \ {s})) (hs_in_U : s ∈ U)
    (γ : PiecewiseC1Immersion) (hγ_closed : γ.toPiecewiseC1Curve.IsClosed)
    (hγ_in_U : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ U)
    (hγ_avoids : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ s) :
    ∫ t in γ.a..γ.b, f (γ.toFun t) * deriv γ.toFun t = 0 := by
  exact contourIntegral_eq_zero_of_meromorphic_residue_zero_nh
    f s hf hres U hU hf_diff hs_in_U γ
    (isNullHomologous_of_convex U hU hU_convex ⟨s, hs_in_U⟩ γ hγ_closed hγ_in_U) hγ_avoids

/-! ### Multi-point vanishing theorem (convex corollary)

For finitely many meromorphic singularities, all with zero residue, the contour
integral vanishes on closed curves in a convex domain. -/

/-- Multi-point version: if `f` is meromorphic at each `s` in `S` with `Res(f, s) = 0`,
`f` is differentiable on `U \ S`, and `U` is convex open, then the contour integral
of `f` vanishes for any closed curve in `U` avoiding all of `S`.

This is a corollary of `contourIntegral_eq_zero_of_meromorphic_residue_zero_finset_nh`
via `isNullHomologous_of_convex`. -/
theorem contourIntegral_eq_zero_of_meromorphic_residue_zero_finset
    (S : Finset ℂ) (f : ℂ → ℂ) (hf_mero : ∀ s ∈ S, MeromorphicAt f s)
    (hres : ∀ s ∈ S, residueAt f s = 0) (U : Set ℂ) (hU : IsOpen U)
    (hU_convex : Convex ℝ U) (hf_diff : DifferentiableOn ℂ f (U \ ↑S))
    (hS_in_U : ∀ s ∈ S, s ∈ U)
    (γ : PiecewiseC1Immersion) (hγ_closed : γ.toPiecewiseC1Curve.IsClosed)
    (hγ_in_U : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ U)
    (hγ_avoids : ∀ s ∈ S, ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ s) :
    ∫ t in γ.a..γ.b, f (γ.toFun t) * deriv γ.toFun t = 0 := by
  have hU_ne : U.Nonempty := by
    rcases S.eq_empty_or_nonempty with rfl | ⟨s, hs⟩
    · exact ⟨γ.toFun γ.a, hγ_in_U γ.a (left_mem_Icc.mpr (le_of_lt γ.hab))⟩
    · exact ⟨s, hS_in_U s hs⟩
  exact contourIntegral_eq_zero_of_meromorphic_residue_zero_finset_nh
    S f hf_mero hres U hU hf_diff γ
    (isNullHomologous_of_convex U hU hU_convex hU_ne γ hγ_closed hγ_in_U) hγ_avoids

end GeneralizedResidueTheory

end
