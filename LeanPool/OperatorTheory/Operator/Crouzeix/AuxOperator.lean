/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
module


public import Mathlib.Topology.Algebra.Polynomial
public import LeanPool.OperatorTheory.Operator.Crouzeix.ContourIntegral
public import LeanPool.OperatorTheory.Operator.Crouzeix.SmoothApprox
public import LeanPool.OperatorTheory.Operator.NumericalRange.Bounded
public import LeanPool.OperatorTheory.Operator.SpectralSet.SpectrumInNR
public import Mathlib.Analysis.Normed.Algebra.GelfandFormula

/-!
# The Crouzeix--Palencia auxiliary operator (L4.2c)

This file supplies the kernel-checked contour-integral part of the auxiliary
operator construction.  If a smooth Jordan domain `Omega` strictly contains
`closure (numericalRange A)`, every point of its boundary lies in the
resolvent set of `A`.  Consequently, any continuous scalar boundary datum
`h` gives an integrable operator-valued kernel
`z ↦ h z • resolvent A z` and hence the bounded operator

`G = (2 * pi * i)⁻¹ • contourIntegral (h • resolvent A) Omega.boundaryParam`.

The sharp L4.2d/e estimates are intentionally not asserted here: they require
identifying the resulting contour expressions through boundary
Cauchy-transform identities.  Mathlib has no located Plemelj boundary-value
theorem from which those identities follow directly.

## Main declarations

* `SmoothJordanDomain.boundaryParam_mem_resolventSet` -- the boundary of a
  domain containing `closure (numericalRange A)` lies in the resolvent set.
* `exists_smoothJordanDomain_for_numericalRange` -- such a containing smooth
  Jordan domain exists for every bounded operator.
* `crouzeixAuxiliaryIntegrand_contourIntegrable` -- continuity of the scalar
  boundary datum implies integrability of the operator-valued kernel.
* `crouzeixAuxiliaryOperator` -- the normalized contour-integral operator.
* `crouzeixPolynomialAuxiliaryIntegrand_contourIntegrable` -- integrability
  for conjugate polynomial boundary values.
* `crouzeixPolynomialAuxiliaryOperator` -- its specialization to the
  conjugate boundary values of a polynomial.
* `exists_bound_crouzeixPolynomialAuxiliaryIntegrand` -- the polynomial
  resolvent kernel is uniformly bounded along the compact parameter interval.
* `norm_crouzeixAuxiliaryOperator_le` -- its explicit contour-length bound.
* `exists_smoothJordanDomain_norm_bound_crouzeixPolynomialAuxiliaryOperator` --
  the packaged bounded auxiliary-operator construction.
-/

@[expose] public section

open Complex Set spectrum
open scoped InnerProductSpace Real Interval

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The closure of the numerical range of every bounded operator is contained
in a smooth strictly convex Jordan domain. -/
theorem exists_smoothJordanDomain_for_numericalRange (A : E →L[ℂ] E) :
    ∃ Omega : SmoothJordanDomain, closure (numericalRange A) ⊆ Omega.carrier := by
  have hbounded : Bornology.IsBounded (numericalRange A) :=
    Metric.isBounded_closedBall.subset (fun z hz => by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact norm_le_of_mem_numericalRange A hz)
  exact exists_smoothJordanDomain_superset_of_isCompact _ hbounded.isCompact_closure

namespace SmoothJordanDomain

private theorem boundaryParam_mem_frontier (Omega : SmoothJordanDomain) (t : ℝ) :
    Omega.boundaryParam t ∈ frontier Omega.carrier := by
  rw [← Omega.boundaryParam_range]
  exact ⟨t, rfl⟩

/-- Every boundary point of a smooth Jordan domain that contains
`closure (numericalRange A)` belongs to the resolvent set of `A`. -/
theorem boundaryParam_mem_resolventSet [CompleteSpace E]
    (Omega : SmoothJordanDomain) (A : E →L[ℂ] E)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier) (t : ℝ) :
    Omega.boundaryParam t ∈ resolventSet ℂ A := by
  by_contra hrho
  have hsigma : Omega.boundaryParam t ∈ spectrum ℂ A := hrho
  have hcarrier := hOmega (spectrum_subset_closure_numericalRange A hsigma)
  have hfrontier := boundaryParam_mem_frontier Omega t
  have hempty : Omega.boundaryParam t ∈ (∅ : Set ℂ) := by
    rw [← Omega.isOpen_carrier.inter_frontier_eq]
    exact ⟨hcarrier, hfrontier⟩
  exact hempty

end SmoothJordanDomain

/-- A continuous scalar boundary datum gives a contour-integrable
operator-valued resolvent kernel. -/
theorem crouzeixAuxiliaryIntegrand_contourIntegrable [CompleteSpace E] (A : E →L[ℂ] E)
    (Omega : SmoothJordanDomain) (h : ℂ → ℂ)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier)
    (hh : ContinuousOn h (Omega.boundaryParam '' Icc (0 : ℝ) (2 * Real.pi))) :
    ContourIntegrable (fun z => h z • resolvent A z) Omega.boundaryParam := by
  apply ContourIntegrable.of_continuousOn
  · exact Omega.boundaryParam_contDiff.continuous.continuousOn
  · exact (Omega.boundaryParam_contDiff.continuous_deriv (by norm_num)).continuousOn
  · refine hh.smul ?_
    rintro z ⟨t, ht, rfl⟩
    exact (spectrum.hasDerivAt_resolvent_const_left
      (Omega.boundaryParam_mem_resolventSet A hOmega t)).continuousAt.continuousWithinAt

/-- The normalized Crouzeix--Palencia auxiliary operator associated to a
scalar boundary datum `h` on a smooth Jordan domain. -/
noncomputable def crouzeixAuxiliaryOperator (A : E →L[ℂ] E)
    (Omega : SmoothJordanDomain) (h : ℂ → ℂ) : E →L[ℂ] E :=
  (2 * (Real.pi : ℂ) * I)⁻¹ •
    contourIntegral (fun z => h z • resolvent A z) Omega.boundaryParam

/-- The conjugate polynomial boundary datum produces an integrable
operator-valued resolvent kernel.  This is the specialization used in the
Crouzeix--Palencia symmetrized and product estimates. -/
theorem crouzeixPolynomialAuxiliaryIntegrand_contourIntegrable [CompleteSpace E]
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier) :
    ContourIntegrable (fun z => star (Polynomial.eval z p) • resolvent A z)
      Omega.boundaryParam := by
  exact crouzeixAuxiliaryIntegrand_contourIntegrable A Omega
    (fun z => star (Polynomial.eval z p)) hOmega p.continuous.star.continuousOn

/-- The parameterized conjugate-polynomial resolvent kernel is uniformly
bounded on `[0, 2 * pi]`. -/
theorem exists_bound_crouzeixPolynomialAuxiliaryIntegrand [CompleteSpace E]
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier) :
    ∃ C : ℝ, ∀ t ∈ Icc (0 : ℝ) (2 * Real.pi),
      ‖deriv Omega.boundaryParam t •
        (star (Polynomial.eval (Omega.boundaryParam t) p) •
          resolvent A (Omega.boundaryParam t))‖ ≤ C := by
  have hgamma : ContinuousOn Omega.boundaryParam (Icc (0 : ℝ) (2 * Real.pi)) :=
    Omega.boundaryParam_contDiff.continuous.continuousOn
  have hresolvent : ContinuousOn (resolvent A)
      (Omega.boundaryParam '' Icc (0 : ℝ) (2 * Real.pi)) := by
    rintro z ⟨t, ht, rfl⟩
    exact (spectrum.hasDerivAt_resolvent_const_left
      (Omega.boundaryParam_mem_resolventSet A hOmega t)).continuousAt.continuousWithinAt
  have hkernel : ContinuousOn
      (fun t => star (Polynomial.eval (Omega.boundaryParam t) p) •
        resolvent A (Omega.boundaryParam t)) (Icc (0 : ℝ) (2 * Real.pi)) :=
    (p.continuous.star.continuousOn.smul hresolvent).comp hgamma (mapsTo_image _ _)
  have hintegrand : ContinuousOn
      (fun t => deriv Omega.boundaryParam t •
        (star (Polynomial.eval (Omega.boundaryParam t) p) •
          resolvent A (Omega.boundaryParam t))) (Icc (0 : ℝ) (2 * Real.pi)) :=
    (Omega.boundaryParam_contDiff.continuous_deriv (by norm_num)).continuousOn.smul hkernel
  have himage : IsCompact ((fun t => deriv Omega.boundaryParam t •
      (star (Polynomial.eval (Omega.boundaryParam t) p) •
        resolvent A (Omega.boundaryParam t))) '' Icc (0 : ℝ) (2 * Real.pi)) :=
    isCompact_Icc.image_of_continuousOn hintegrand
  obtain ⟨C, hC⟩ := (Metric.isBounded_iff_subset_closedBall
    (0 : E →L[ℂ] E)).mp himage.isBounded
  refine ⟨C, fun t ht => ?_⟩
  have hmem := hC ⟨t, ht, rfl⟩
  rw [Metric.mem_closedBall, dist_zero_right] at hmem
  exact hmem

/-- The normalized auxiliary operator associated to the conjugate boundary
values of a polynomial `p`. -/
noncomputable def crouzeixPolynomialAuxiliaryOperator (A : E →L[ℂ] E)
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) : E →L[ℂ] E :=
  crouzeixAuxiliaryOperator A Omega (fun z => star (Polynomial.eval z p))

/-- A pointwise bound `C` on the parameterized resolvent kernel gives the
corresponding explicit operator-norm bound for the normalized auxiliary
operator. -/
theorem norm_crouzeixAuxiliaryOperator_le (A : E →L[ℂ] E)
    (Omega : SmoothJordanDomain) (h : ℂ → ℂ) {C : ℝ}
    (hbound : ∀ t ∈ Icc (0 : ℝ) (2 * Real.pi),
      ‖deriv Omega.boundaryParam t •
        (h (Omega.boundaryParam t) • resolvent A (Omega.boundaryParam t))‖ ≤ C) :
    ‖crouzeixAuxiliaryOperator A Omega h‖ ≤
      ‖(2 * (Real.pi : ℂ) * I)⁻¹‖ * (2 * Real.pi * C) := by
  unfold crouzeixAuxiliaryOperator
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left
    (norm_contourIntegral_le_of_norm_le_const hbound) (norm_nonneg _)

/-- The explicit contour-length bound specialized to the conjugate boundary
values of a polynomial. -/
theorem norm_crouzeixPolynomialAuxiliaryOperator_le (A : E →L[ℂ] E)
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) {C : ℝ}
    (hbound : ∀ t ∈ Icc (0 : ℝ) (2 * Real.pi),
      ‖deriv Omega.boundaryParam t •
        (star (Polynomial.eval (Omega.boundaryParam t) p) •
          resolvent A (Omega.boundaryParam t))‖ ≤ C) :
    ‖crouzeixPolynomialAuxiliaryOperator A Omega p‖ ≤
      ‖(2 * (Real.pi : ℂ) * I)⁻¹‖ * (2 * Real.pi * C) := by
  unfold crouzeixPolynomialAuxiliaryOperator
  exact norm_crouzeixAuxiliaryOperator_le A Omega
    (fun z => star (Polynomial.eval z p)) hbound

/-- For every containing smooth Jordan domain, the polynomial auxiliary
operator admits a finite explicit contour-length bound. -/
theorem exists_norm_bound_crouzeixPolynomialAuxiliaryOperator [CompleteSpace E]
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier) :
    ∃ C : ℝ, ‖crouzeixPolynomialAuxiliaryOperator A Omega p‖ ≤
      ‖(2 * (Real.pi : ℂ) * I)⁻¹‖ * (2 * Real.pi * C) := by
  obtain ⟨C, hC⟩ := exists_bound_crouzeixPolynomialAuxiliaryIntegrand A Omega p hOmega
  exact ⟨C, norm_crouzeixPolynomialAuxiliaryOperator_le A Omega p hC⟩

/-- Every polynomial admits a normalized auxiliary operator on some smooth
Jordan domain containing `closure (numericalRange A)`, together with a finite
contour-length norm bound. -/
theorem exists_smoothJordanDomain_norm_bound_crouzeixPolynomialAuxiliaryOperator
    [CompleteSpace E] (A : E →L[ℂ] E) (p : Polynomial ℂ) :
    ∃ (Omega : SmoothJordanDomain) (C : ℝ),
      closure (numericalRange A) ⊆ Omega.carrier ∧
      ‖crouzeixPolynomialAuxiliaryOperator A Omega p‖ ≤
        ‖(2 * (Real.pi : ℂ) * I)⁻¹‖ * (2 * Real.pi * C) := by
  obtain ⟨Omega, hOmega⟩ := exists_smoothJordanDomain_for_numericalRange A
  obtain ⟨C, hC⟩ := exists_norm_bound_crouzeixPolynomialAuxiliaryOperator A Omega p hOmega
  exact ⟨Omega, C, hOmega, hC⟩

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
