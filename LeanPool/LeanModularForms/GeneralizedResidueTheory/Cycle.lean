/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import LeanPool.LeanModularForms.GeneralizedResidueTheory.GeneralizedResidueTheorem
import Mathlib.Data.Finsupp.Defs

/-!
# Contour Cycles

Formal Z-linear combinations of piecewise C^1 immersions ("cycles"), with
contour integration and winding numbers extended by linearity.

## Main definitions

* `ContourCycle` -- formal Z-linear combination of `PiecewiseC1Immersion`s.
* `contourIntegralCycle f Gamma` -- contour integral of `f` over a cycle.
* `windingNumberCycle Gamma z` -- winding number of a cycle around `z`.
* `IsNullHomologousCycle Gamma U` -- each component is null-homologous in `U`.
* `cpvCycle S0 f Gamma` -- CPV integral of `f` over a cycle.

## Main results

* `contourIntegralCycle_single` -- single curve with multiplicity 1.
* `windingNumberCycle_single` -- same for winding numbers.
* `contourIntegralCycle_eq_zero_of_nullHomologous` -- Cauchy theorem for cycles.
* `generalizedResidueTheorem_simplePoles_cycle` -- residue theorem for cycles
  (simple poles).
* `generalizedResidueTheorem_cycle` -- residue theorem for cycles (higher-order,
  Tendsto).
* `windingNumberCycle_isInt` -- winding number integrality.
-/

open Complex MeasureTheory Set Filter Topology
open scoped Interval

noncomputable section

/-! ### Definitions -/

/-- A contour cycle is a formal Z-linear combination of piecewise C^1 immersions. -/
abbrev ContourCycle := PiecewiseC1Immersion →₀ ℤ

/-- Contour integral of `f` over a cycle `Gamma`, extended by linearity:
`sum_gamma n_gamma * integral_gamma f(z) dz`. -/
def contourIntegralCycle (f : ℂ → ℂ) (Γ : ContourCycle) : ℂ :=
  Γ.sum fun γ n =>
    (n : ℂ) * ∫ t in γ.a..γ.b, f (γ.toFun t) * deriv γ.toFun t

/-- Winding number of a cycle around `z`, extended by linearity:
`sum_gamma n_gamma * n(gamma, z)`. -/
def windingNumberCycle (Γ : ContourCycle) (z : ℂ) : ℂ :=
  Γ.sum fun γ n =>
    (n : ℂ) * generalizedWindingNumber' γ.toFun γ.a γ.b z

/-- A cycle is null-homologous in `U` when every component curve is
null-homologous in `U`. -/
def IsNullHomologousCycle (Γ : ContourCycle) (U : Set ℂ) : Prop :=
  ∀ γ ∈ Γ.support, IsNullHomologous γ U

/-- Cauchy principal value integral of `f` over a cycle `Gamma`, extended by
linearity: `sum_gamma n_gamma * CPV(gamma, f)`. -/
def cpvCycle (S0 : Finset ℂ) (f : ℂ → ℂ) (Γ : ContourCycle) : ℂ :=
  Γ.sum fun γ n => (n : ℂ) * cauchyPrincipalValueOn S0 f γ.toFun γ.a γ.b

/-! ### Bridge lemmas for single curves -/

/-- Contour integral of a single curve with multiplicity 1. -/
theorem contourIntegralCycle_single (f : ℂ → ℂ) (γ : PiecewiseC1Immersion) :
    contourIntegralCycle f (Finsupp.single γ 1) =
      ∫ t in γ.a..γ.b, f (γ.toFun t) * deriv γ.toFun t := by
  unfold contourIntegralCycle; rw [Finsupp.sum_single_index] <;> simp

/-- Winding number of a single curve with multiplicity 1. -/
theorem windingNumberCycle_single (γ : PiecewiseC1Immersion) (z : ℂ) :
    windingNumberCycle (Finsupp.single γ 1) z =
      generalizedWindingNumber' γ.toFun γ.a γ.b z := by
  unfold windingNumberCycle; rw [Finsupp.sum_single_index] <;> simp

/-- A null-homologous single curve gives a null-homologous cycle. -/
theorem isNullHomologousCycle_single (γ : PiecewiseC1Immersion) (U : Set ℂ)
    (h : IsNullHomologous γ U) :
    IsNullHomologousCycle (Finsupp.single γ 1) U := fun γ' hγ' => by
  rw [Finsupp.support_single _ one_ne_zero, Finset.mem_singleton] at hγ'; rwa [hγ']

/-- CPV integral of a single curve with multiplicity 1. -/
theorem cpvCycle_single (S0 : Finset ℂ) (f : ℂ → ℂ) (γ : PiecewiseC1Immersion) :
    cpvCycle S0 f (Finsupp.single γ 1) =
      cauchyPrincipalValueOn S0 f γ.toFun γ.a γ.b := by
  unfold cpvCycle; rw [Finsupp.sum_single_index] <;> simp

/-! ### Main theorems -/

/-- **Cauchy theorem for cycles**: if `f` is holomorphic on `U` and `Gamma` is
null-homologous in `U`, then the contour integral of `f` over `Gamma` is zero. -/
theorem contourIntegralCycle_eq_zero_of_nullHomologous
    {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U)
    (Γ : ContourCycle) (h_null : IsNullHomologousCycle Γ U) :
    contourIntegralCycle f Γ = 0 := by
  simpa only [contourIntegralCycle, Finsupp.sum] using Finset.sum_eq_zero fun γ hγ => by
    rw [contourIntegral_eq_zero_of_nullHomologous hU hf γ (h_null γ hγ), mul_zero]

/-- Winding number of a null-homologous cycle is zero outside `U`. -/
theorem windingNumberCycle_eq_zero_outside
    {U : Set ℂ} (Γ : ContourCycle) (h_null : IsNullHomologousCycle Γ U)
    {z : ℂ} (hz : z ∉ U) :
    windingNumberCycle Γ z = 0 := by
  simp only [windingNumberCycle, Finsupp.sum]
  exact Finset.sum_eq_zero fun γ hγ => by rw [(h_null γ hγ).winding_zero z hz, mul_zero]

/-! ### Residue theorem for cycles (simple poles) -/

/-- Algebraic core: rewrite the weighted sum of per-component residue formulas as
the cycle-level residue sum. -/
private theorem sum_swap_winding_residue (Γ : ContourCycle) (S0 : Finset ℂ)
    (f : ℂ → ℂ) :
    ∑ γ ∈ Γ.support, (↑(Γ γ) : ℂ) *
      (2 * ↑Real.pi * I * ∑ s ∈ S0,
        generalizedWindingNumber' γ.toFun γ.a γ.b s * residueAt f s) =
    2 * ↑Real.pi * I * ∑ s ∈ S0,
      windingNumberCycle Γ s * residueAt f s := by
  simp_rw [Finset.mul_sum]
  rw [← Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [windingNumberCycle, Finsupp.sum]
  rw [Finset.sum_congr rfl (fun γ _ => show (↑(Γ γ) : ℂ) *
      (2 * ↑Real.pi * I * (generalizedWindingNumber' γ.toFun γ.a γ.b s *
        residueAt f s)) =
      2 * ↑Real.pi * I *
        (↑(Γ γ) * generalizedWindingNumber' γ.toFun γ.a γ.b s *
          residueAt f s)
    from by ring), ← Finset.mul_sum, ← Finset.sum_mul]

/-- **Generalized Residue Theorem for simple poles on a cycle.**

Extends `generalizedResidueTheorem_simplePoles` from a single curve to a formal
Z-linear combination of curves. -/
theorem generalizedResidueTheorem_simplePoles_cycle
    (U : Set ℂ) (hU : IsOpen U) (S : Set ℂ) (hS_in_U : ∀ s ∈ S, s ∈ U)
    (hS_discrete : ∀ s ∈ S, ∃ ε > 0, ∀ s' ∈ S, s' ≠ s → ε ≤ ‖s' - s‖)
    (hS_closed : IsClosed S) (S0 : Finset ℂ) (hS0_subset : ∀ s ∈ S0, s ∈ S)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (U \ S0))
    (Γ : ContourCycle) (h_null : IsNullHomologousCycle Γ U)
    (hS_on_curve : ∀ γ ∈ Γ.support, ∀ t ∈ Icc γ.a γ.b,
      γ.toFun t ∈ S → γ.toFun t ∈ S0)
    (hSimplePoles : ∀ s ∈ S0, HasSimplePoleAt f s)
    (hf_ext : ∀ s ∈ S0,
      ContinuousAt (fun z => f z - residueSimplePole f s / (z - s)) s)
    (hγ_meas : ∀ γ ∈ Γ.support, Measurable γ.toFun)
    (h_no_endpt : ∀ γ ∈ Γ.support, ∀ s ∈ S0,
      γ.toFun γ.a ≠ s ∧ γ.toFun γ.b ≠ s)
    (h_unique : ∀ γ ∈ Γ.support, ∀ s ∈ S0,
      ∀ t₁ ∈ Icc γ.a γ.b, ∀ t₂ ∈ Icc γ.a γ.b,
      γ.toFun t₁ = s → γ.toFun t₂ = s → t₁ = t₂) :
    cpvCycle S0 f Γ = 2 * Real.pi * I * ∑ s ∈ S0,
      windingNumberCycle Γ s * residueAt f s := by
  have h_comp : ∀ γ ∈ Γ.support,
      cauchyPrincipalValueOn S0 f γ.toFun γ.a γ.b =
        2 * Real.pi * I * ∑ s ∈ S0,
          generalizedWindingNumber' γ.toFun γ.a γ.b s * residueAt f s :=
    fun γ hγ => generalizedResidueTheorem_simplePoles U hU S hS_in_U hS_discrete
      hS_closed S0 hS0_subset f hf γ (h_null γ hγ)
      (hS_on_curve γ hγ) hSimplePoles hf_ext (hγ_meas γ hγ)
      (h_no_endpt γ hγ) (h_unique γ hγ)
  change Γ.sum (fun γ n => (n : ℂ) *
      cauchyPrincipalValueOn S0 f γ.toFun γ.a γ.b) =
    2 * ↑Real.pi * I * ∑ s ∈ S0, windingNumberCycle Γ s * residueAt f s
  simp_rw [Finsupp.sum]
  rw [Finset.sum_congr rfl fun γ hγ => show (↑(Γ γ) : ℂ) *
      cauchyPrincipalValueOn S0 f γ.toFun γ.a γ.b = (↑(Γ γ) : ℂ) *
      (2 * ↑Real.pi * I * ∑ s ∈ S0,
        generalizedWindingNumber' γ.toFun γ.a γ.b s * residueAt f s)
    from congr_arg _ (h_comp γ hγ)]
  exact sum_swap_winding_residue Γ S0 f

/-! ### Higher-order residue theorem for cycles (Tendsto version) -/

/-- **Generalized Residue Theorem for cycles** (higher-order poles, Tendsto).

Extends `generalizedResidueTheorem` from a single curve to a formal Z-linear
combination of curves. Each component must satisfy conditions (A') and (B). -/
theorem generalizedResidueTheorem_cycle
    (U : Set ℂ) (hU : IsOpen U) (S : Set ℂ) (hS_in_U : ∀ s ∈ S, s ∈ U)
    (hS_discrete : ∀ s ∈ S, ∃ ε > 0, ∀ s' ∈ S, s' ≠ s → ε ≤ ‖s' - s‖)
    (hS_closed : IsClosed S) (S0 : Finset ℂ) (hS0_subset : ∀ s ∈ S0, s ∈ S)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (U \ S0))
    (Γ : ContourCycle) (h_null : IsNullHomologousCycle Γ U)
    (hS_on_curve : ∀ γ ∈ Γ.support, ∀ t ∈ Icc γ.a γ.b,
      γ.toFun t ∈ S → γ.toFun t ∈ S0)
    (hMero : ∀ s ∈ S0, MeromorphicAt f s)
    (hCondA : ∀ γ ∈ Γ.support,
      SatisfiesConditionA' γ S0 (fun s => poleOrderAt f s))
    (hCondB : ∀ γ ∈ Γ.support, SatisfiesConditionB γ f S0)
    (hγ_meas : ∀ γ ∈ Γ.support, Measurable γ.toFun)
    (h_no_endpt : ∀ γ ∈ Γ.support, ∀ s ∈ S0,
      γ.toFun γ.a ≠ s ∧ γ.toFun γ.b ≠ s)
    (h_unique : ∀ γ ∈ Γ.support, ∀ s ∈ S0,
      ∀ t₁ ∈ Icc γ.a γ.b, ∀ t₂ ∈ Icc γ.a γ.b,
      γ.toFun t₁ = s → γ.toFun t₂ = s → t₁ = t₂) :
    Tendsto (fun ε => Γ.sum fun γ n =>
        (n : ℂ) * ∫ t in γ.a..γ.b,
          cauchyPrincipalValueIntegrandOn S0 f γ.toFun ε t)
      (𝓝[>] 0)
      (𝓝 (2 * Real.pi * I * ∑ s ∈ S0,
        windingNumberCycle Γ s * residueAt f s)) := by
  have h_comp : ∀ γ ∈ Γ.support,
      Tendsto (fun ε => ∫ t in γ.a..γ.b,
        cauchyPrincipalValueIntegrandOn S0 f γ.toFun ε t)
        (𝓝[>] 0)
        (𝓝 (2 * Real.pi * I * ∑ s ∈ S0,
          generalizedWindingNumber' γ.toFun γ.a γ.b s * residueAt f s)) :=
    fun γ hγ => generalizedResidueTheorem U hU S hS_in_U hS_discrete
      hS_closed S0 hS0_subset f hf γ (h_null γ hγ) (hS_on_curve γ hγ)
      hMero (hCondA γ hγ) (hCondB γ hγ) (hγ_meas γ hγ)
      (h_no_endpt γ hγ) (h_unique γ hγ)
  simp_rw [Finsupp.sum]
  rw [show 2 * ↑Real.pi * I * ∑ s ∈ S0,
      windingNumberCycle Γ s * residueAt f s =
    ∑ γ ∈ Γ.support, (↑(Γ γ) : ℂ) *
      (2 * ↑Real.pi * I * ∑ s ∈ S0,
        generalizedWindingNumber' γ.toFun γ.a γ.b s * residueAt f s)
    from (sum_swap_winding_residue Γ S0 f).symm]
  exact tendsto_finsetSum _ fun γ hγ => (h_comp γ hγ).const_mul _

/-! ### Winding number integrality -/

/-- The generalized winding number of a closed piecewise C^1 immersion around a
point it avoids is an integer. -/
theorem windingNumber_isInt_of_immersion_closed_avoiding
    (γ : PiecewiseC1Immersion) (z : ℂ)
    (hγ_closed : γ.toPiecewiseC1Curve.IsClosed)
    (h_avoids : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ z) :
    ∃ n : ℤ, generalizedWindingNumber' γ.toFun γ.a γ.b z = ↑n :=
  windingNumber_integer_of_piecewise_closed_avoiding γ.toFun γ.a γ.b z
    γ.partition γ.hab hγ_closed γ.continuous_toFun
    (fun t ht hP => γ.smooth_off_partition t (Ioo_subset_Icc_self ht) hP)
    (fun _p1 _p2 _h12 hnoP hsub t ht =>
      (γ.deriv_continuous_off_partition t (hsub ht) (hnoP t ht)).continuousWithinAt)
    h_avoids ⟨_, fun t ht => (piecewiseC1Immersion_deriv_bounded γ).choose_spec t ht⟩

/-- Winding number of a cycle around a point avoided by all component curves is
an integer, provided each component curve is closed. -/
theorem windingNumberCycle_isInt (Γ : ContourCycle)
    (h_closed : ∀ γ ∈ Γ.support, γ.toPiecewiseC1Curve.IsClosed)
    (z : ℂ) (h_avoids : ∀ γ ∈ Γ.support,
      ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ z) :
    ∃ n : ℤ, windingNumberCycle Γ z = ↑n := by
  simp only [windingNumberCycle, Finsupp.sum]
  apply Finset.sum_induction _ (fun x : ℂ => ∃ n : ℤ, x = ↑n)
  · rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩; exact ⟨a + b, by push_cast; ring⟩
  · exact ⟨0, Int.cast_zero.symm⟩
  · intro γ hγ
    obtain ⟨m, hm⟩ := windingNumber_isInt_of_immersion_closed_avoiding γ z
      (h_closed γ hγ) (h_avoids γ hγ)
    exact ⟨Γ γ * m, by rw [hm]; push_cast; ring⟩

end
