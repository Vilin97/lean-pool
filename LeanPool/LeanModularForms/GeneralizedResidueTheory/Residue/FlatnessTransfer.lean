/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import LeanPool.LeanModularForms.GeneralizedResidueTheory.HomologicalCauchy

/-!
# Generalized Residue Theorem (Theorem 3.3) -- Convex Domain Corollary

Convex-domain specialization of the generalized residue theorem
(Hungerbuhler-Wasem, arXiv:1808.00997v2, Theorem 3.3). Constructs the
`IsNullHomologous` witness from convexity, then delegates to
`generalizedResidueTheorem_higher_order_tendsto` with the two Tendsto inputs
built from `conditionsAB_imply_higherOrderCancel_nh` and
`pv_res_tendsto_of_immersion_nullHomologous`.

## Main results

* `generalizedResidueTheorem_3_3`: the generalized residue theorem with
  conditions (A')+(B), convex domain.
-/

open Complex MeasureTheory Set Filter Topology Finset Real
open scoped Interval

noncomputable section

namespace GeneralizedResidueTheory

/-- **Theorem 3.3 (Hungerbuhler-Wasem)**: Generalized residue theorem with the paper's
actual conditions (A') and (B), matching arXiv:1808.00997v2 Theorem 3.3.

Uses `Tendsto` formulation and does not require C2 regularity at crossings.

- **Condition (A')**: At each crossing point where `f` has a pole of order `n`,
  the curve is flat of order `n` (Definition 3.2). Uses `SatisfiesConditionA'`
  with `poleOrderAt f` to capture the variable-order flatness requirement.
- **Condition (B)**: At each crossing point, the angle `alpha` is a rational multiple
  of `pi`, and each nonzero Laurent coefficient `a_{-k}` with `k >= 2` satisfies
  `(k-1)*alpha in 2*pi*Z`.

These conditions ensure that the PV contributions from higher-order polar terms
vanish, so the full PV integral reduces to the simple-pole case.

For simple poles, `poleOrderAt f s = 1` and `IsFlatOfOrder gamma t_0 1` is automatic
(see `isFlatOfOrder_one`), so condition (A') reduces to condition (A).

Constructs `IsNullHomologous` from convexity, then combines
`conditionsAB_imply_higherOrderCancel_nh` and
`pv_res_tendsto_of_immersion_nullHomologous` via
`generalizedResidueTheorem_higher_order_tendsto`. -/
theorem generalizedResidueTheorem_3_3
    (U : Set ℂ) (hU : IsOpen U) (hU_convex : Convex ℝ U)
    (S : Set ℂ) (hS_in_U : ∀ s ∈ S, s ∈ U)
    (hS_discrete : ∀ s ∈ S, ∃ ε > 0, ∀ s' ∈ S, s' ≠ s → ε ≤ ‖s' - s‖)
    (hS_closed : IsClosed S)
    (S0 : Finset ℂ) (hS0_subset : ∀ s ∈ S0, s ∈ S)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (U \ S0))
    (γ : PiecewiseC1Immersion)
    (hγ_closed : γ.toPiecewiseC1Curve.IsClosed)
    (hγ_in_U : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ U)
    (hS_on_curve : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ S → γ.toFun t ∈ S0)
    (hMero : ∀ s ∈ S0, MeromorphicAt f s)
    (hCondA : SatisfiesConditionA' γ S0 (fun s => poleOrderAt f s))
    (hCondB : SatisfiesConditionB γ f S0)
    (hγ_meas : Measurable γ.toFun)
    (h_no_endpt_cross : ∀ s ∈ S0, γ.toFun γ.a ≠ s ∧ γ.toFun γ.b ≠ s)
    (h_unique_cross : ∀ s ∈ S0, ∀ t₁ ∈ Icc γ.a γ.b, ∀ t₂ ∈ Icc γ.a γ.b,
      γ.toFun t₁ = s → γ.toFun t₂ = s → t₁ = t₂) :
    Tendsto (fun ε => ∫ t in γ.a..γ.b,
        cauchyPrincipalValueIntegrandOn S0 f γ.toFun ε t)
      (𝓝[>] 0) (𝓝 (2 * Real.pi * I * ∑ s ∈ S0,
        generalizedWindingNumber' γ.toFun γ.a γ.b s * residueAt f s)) :=
  have h_null : IsNullHomologous γ U :=
    isNullHomologous_of_convex U hU hU_convex
      ⟨γ.toFun γ.a, hγ_in_U γ.a (left_mem_Icc.mpr γ.hab.le)⟩
      γ hγ_closed hγ_in_U
  generalizedResidueTheorem_higher_order_tendsto S0 f γ
    (conditionsAB_imply_higherOrderCancel_nh U hU S0 f hf γ
      h_null hMero hCondA hCondB hγ_meas h_no_endpt_cross
      h_unique_cross (fun s hs => hS_in_U s (hS0_subset s hs)))
    (pv_res_tendsto_of_immersion_nullHomologous U S hS_discrete
      hS_closed S0 hS0_subset f γ h_null hS_on_curve hγ_meas
      h_no_endpt_cross h_unique_cross)

end GeneralizedResidueTheory
