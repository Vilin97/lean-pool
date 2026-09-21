/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

import LeanPool.OperatorTheory.Operator.Crouzeix.SmoothSupportCurveRange
import LeanPool.OperatorTheory.Operator.Crouzeix.SmoothSupportEnvelopeTight

/-!
# Smooth Jordan domains from rounded finite support functions

The rounded log-sum-exp support curve and its open halfspace envelope provide
all fields of `SmoothJordanDomain`.  This file packages that construction and
uses arbitrarily tight scale choices to discharge the remaining planar outer
approximation problem, culminating in the exact polynomial
Crouzeix--Palencia theorem.
-/

open Complex Metric Set
open scoped ContDiff InnerProductSpace

/-- Package a rounded support envelope as a smooth Jordan domain once its
support curve has been identified with the envelope frontier. -/
noncomputable def polytopeRoundedSupportDomainOfRange
    {u : Finset ℂ} (hu : u.Nonempty) {delta rho : ℝ}
    (hdelta : 0 < delta) (hrho : 0 < rho)
    (hrange : Set.range (polytopeRoundedSupportCurve u delta rho) =
      frontier (smoothSupportOpenEnvelope
        (polytopeRoundedSupport u delta rho))) :
    SmoothJordanDomain where
  carrier := smoothSupportOpenEnvelope
    (polytopeRoundedSupport u delta rho)
  isOpen_carrier := isOpen_smoothSupportOpenEnvelope _
  strictConvex_carrier := strictConvex_smoothSupportOpenEnvelope _
  boundaryParam := polytopeRoundedSupportCurve u delta rho
  boundaryParam_periodic :=
    periodic_polytopeRoundedSupportCurve u delta rho
  boundaryParam_contDiff :=
    contDiff_polytopeRoundedSupportCurve hu delta rho
  boundaryParam_range := hrange
  boundaryParam_injOn := by
    unfold polytopeRoundedSupportCurve
    simpa only [zero_add] using
      injOn_smoothSupportCurve_Ico
        (contDiff_polytopeRoundedSupport hu delta rho)
        (periodic_polytopeRoundedSupport u delta rho)
        (fun theta => by
          unfold smoothSupportCurvatureRadius
          exact polytopeRoundedSupport_add_deriv_deriv_pos
            hu hdelta hrho theta)
        0
  boundaryParam_regular :=
    polytopeRoundedSupportCurve_regular hu hdelta hrho

@[simp] theorem polytopeRoundedSupportDomainOfRange_carrier
    {u : Finset ℂ} (hu : u.Nonempty) {delta rho : ℝ}
    (hdelta : 0 < delta) (hrho : 0 < rho)
    (hrange : Set.range (polytopeRoundedSupportCurve u delta rho) =
      frontier (smoothSupportOpenEnvelope
        (polytopeRoundedSupport u delta rho))) :
    (polytopeRoundedSupportDomainOfRange
      hu hdelta hrho hrange).carrier =
      smoothSupportOpenEnvelope
        (polytopeRoundedSupport u delta rho) := rfl

/-- A finite point set whose convex hull has nonempty interior is nonempty. -/
theorem Finset.nonempty_of_interior_convexHull_nonempty
    {u : Finset ℂ}
    (hinterior :
      (interior (convexHull ℝ (u : Set ℂ))).Nonempty) :
    u.Nonempty := by
  by_contra hnot
  have hu : u = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnot
  subst u
  obtain ⟨z, hz⟩ := hinterior
  simp only [Finset.coe_empty, convexHull_empty, interior_empty] at hz
  exact hz

/-- The full-dimensional finite-polytope approximation problem follows from
frontier surjectivity of every positive rounded support curve. -/
theorem hasSmoothJordanOuterApproximationForPolytopes_of_supportCurve_range
    (hrange : ∀ {u : Finset ℂ} (_hu : u.Nonempty) {delta rho : ℝ},
      0 < delta → 0 < rho →
      Set.range (polytopeRoundedSupportCurve u delta rho) =
        frontier (smoothSupportOpenEnvelope
          (polytopeRoundedSupport u delta rho))) :
    HasSmoothJordanOuterApproximationForPolytopes := by
  intro u hinterior
  have hu : u.Nonempty :=
    Finset.nonempty_of_interior_convexHull_nonempty hinterior
  intro epsilon hepsilon
  obtain ⟨delta, rho, hdelta, hrho, hin, hout⟩ :=
    exists_tight_polytopeRoundedSupportEnvelope hu hepsilon
  let Omega : SmoothJordanDomain :=
    polytopeRoundedSupportDomainOfRange hu hdelta hrho
      (hrange hu hdelta hrho)
  refine ⟨Omega, ?_, ?_⟩
  · simpa only [Omega, polytopeRoundedSupportDomainOfRange_carrier] using hin
  · simpa only [Omega, polytopeRoundedSupportDomainOfRange_carrier] using hout

/-- The smooth Jordan domain canonically associated with a nonempty rounded
finite support function. -/
noncomputable def polytopeRoundedSupportDomain
    {u : Finset ℂ} (hu : u.Nonempty) {delta rho : ℝ}
    (hdelta : 0 < delta) (hrho : 0 < rho) :
    SmoothJordanDomain :=
  polytopeRoundedSupportDomainOfRange hu hdelta hrho
    (range_polytopeRoundedSupportCurve_eq_frontier hu hdelta hrho)

@[simp] theorem polytopeRoundedSupportDomain_carrier
    {u : Finset ℂ} (hu : u.Nonempty) {delta rho : ℝ}
    (hdelta : 0 < delta) (hrho : 0 < rho) :
    (polytopeRoundedSupportDomain hu hdelta hrho).carrier =
      smoothSupportOpenEnvelope
        (polytopeRoundedSupport u delta rho) := rfl

@[simp] theorem polytopeRoundedSupportDomain_boundaryParam
    {u : Finset ℂ} (hu : u.Nonempty) {delta rho : ℝ}
    (hdelta : 0 < delta) (hrho : 0 < rho) :
    (polytopeRoundedSupportDomain hu hdelta hrho).boundaryParam =
      polytopeRoundedSupportCurve u delta rho := rfl

/-- Every full-dimensional finite convex hull has arbitrarily tight smooth
Jordan outer approximations. -/
theorem hasSmoothJordanOuterApproximationForPolytopes :
    HasSmoothJordanOuterApproximationForPolytopes := by
  apply
    hasSmoothJordanOuterApproximationForPolytopes_of_supportCurve_range
  intro u hu delta rho hdelta hrho
  exact range_polytopeRoundedSupportCurve_eq_frontier hu hdelta hrho

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

/-- The exact Crouzeix--Palencia theorem: the closed numerical range is a
`1 + sqrt 2` polynomial spectral set for every bounded operator on a complex
Hilbert space. -/
theorem crouzeix_palencia (A : E →L[ℂ] E) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · let _ := hE
    constructor
    · exact spectrum_subset_closure_numericalRange A
    · intro p
      have hzero : Polynomial.aeval A p = 0 := Subsingleton.elim _ _
      rw [hzero, norm_zero]
      exact mul_nonneg
        (add_nonneg zero_le_one (Real.sqrt_nonneg 2))
        (polynomialSupNorm_nonneg p (closure (numericalRange A)))
  · let _ := hE
    exact
      crouzeix_palencia_of_smoothJordanOuterApproximation_polytope_case
        A hasSmoothJordanOuterApproximationForPolytopes

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
