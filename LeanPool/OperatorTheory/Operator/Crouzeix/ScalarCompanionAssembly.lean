/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
module


public import LeanPool.OperatorTheory.Operator.Crouzeix.BoundaryApproximation
public import LeanPool.OperatorTheory.Operator.Crouzeix.PalenciaSmoothApproximation
public import LeanPool.OperatorTheory.Operator.Crouzeix.ScalarCompanionPlemeljBound

/-!
# Assembly from the scalar Plemelj companion

The published fourth-power route to the Crouzeix--Palencia estimate consumes
a continuous scalar companion which is contractive on each compact stage,
uniformly approximable there by polynomials, and whose auxiliary contour is
the conjugate-polynomial auxiliary operator.  This file supplies the bridge
from the canonical Plemelj construction to that interface.

The remaining analytic inputs stay explicit: convergence of the regularized
transform, the sharp lower-degree boundary-phase inequality, uniform
polynomial approximation of the resulting closed extension, and reproduction
of the original auxiliary contour.

## Main declarations

* `exists_continuous_scalarCompanion_approximation_of_boundaryPhaseTransform`
  packages the canonical closed extension for one smooth domain;
* `crouzeix_palencia_of_convexThickening_cauchy_support_boundaryPhase_approximation`
  feeds those packages through the smooth-thickening fourth-power capstone.
-/

@[expose] public section

open Complex Filter Set
open scoped InnerProductSpace Interval Real

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

omit [CompleteSpace E] in
/-- Regularized Plemelj convergence and the sharp boundary-phase inequality
turn the canonical closed scalar companion into the exact continuous and
contractive datum used by the polynomial-approximation route.  Approximation
and reproduction of its auxiliary contour remain explicit analytic inputs. -/
theorem
    exists_continuous_scalarCompanion_approximation_of_boundaryPhaseTransform
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (hbounded : Bornology.IsBounded Omega.carrier)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1)
    (hreg : ∀ xi ∈ frontier Omega.carrier,
      Tendsto
        (crouzeixPolynomialScalarCompanionRegularized Omega p xi)
        (nhdsWithin xi Omega.carrier)
        (nhds
          (crouzeixPolynomialScalarCompanionRegularized Omega p xi xi)))
    (hphase : ∀ xi ∈ frontier Omega.carrier,
      ‖star (Polynomial.eval xi p) +
          crouzeixPolynomialBoundaryPhaseTransform Omega xi
            (p /ₘ (Polynomial.X - Polynomial.C xi))‖ ≤
        polynomialSupNorm p (frontier Omega.carrier))
    (r : ℕ → Polynomial ℂ)
    (happrox : ∀ (j : ℕ) (z : ℂ), z ∈ closure Omega.carrier →
      ‖Polynomial.eval z (r j) -
          crouzeixPolynomialScalarCompanionClosedExtension Omega p z‖ ≤
        1 / ((j : ℝ) + 1))
    (hPlemelj :
      crouzeixAuxiliaryOperator A Omega
          (crouzeixPolynomialScalarCompanionClosedExtension Omega p) =
        crouzeixPolynomialAuxiliaryOperator A Omega p) :
    ∃ (g : ℂ → ℂ) (q : ℕ → Polynomial ℂ),
      ContinuousOn g
          (Omega.boundaryParam '' Icc (0 : ℝ) (2 * Real.pi)) ∧
      (∀ z ∈ closure Omega.carrier,
        ‖g z‖ ≤ polynomialSupNorm p (closure Omega.carrier)) ∧
      (∀ (j : ℕ) (z : ℂ), z ∈ closure Omega.carrier →
        ‖Polynomial.eval z (q j) - g z‖ ≤ 1 / ((j : ℝ) + 1)) ∧
      crouzeixAuxiliaryOperator A Omega g =
        crouzeixPolynomialAuxiliaryOperator A Omega p := by
  refine ⟨
    crouzeixPolynomialScalarCompanionClosedExtension Omega p,
    r, ?_, ?_, happrox, hPlemelj⟩
  · apply
      (continuousOn_crouzeixPolynomialScalarCompanionClosedExtension_of_regularized
        Omega p hkernel hreg).mono
    rintro z ⟨t, _ht, rfl⟩
    apply frontier_subset_closure
    rw [← Omega.boundaryParam_range]
    exact mem_range_self t
  · intro z hz
    calc
      ‖crouzeixPolynomialScalarCompanionClosedExtension Omega p z‖ ≤
          polynomialSupNorm p (frontier Omega.carrier) :=
        norm_crouzeixPolynomialScalarCompanionClosedExtension_le_of_boundaryPhaseTransform
          Omega p hbounded hkernel hreg hphase hz
      _ = polynomialSupNorm p (closure Omega.carrier) :=
        (polynomialSupNorm_closure_carrier_eq_frontier
          Omega p hbounded).symm

/-- On the explicit smooth thickening exhaustion, the boundary-phase
contraction, regularized convergence, polynomial approximation, and contour
reproduction together imply the exact Crouzeix--Palencia spectral-set bound.

This is the direct capstone connector for the scalar-companion route.  The
geometric Cauchy and support hypotheses provide the symmetrized estimate and
the finite stagewise calculus bound; the canonical scalar companions provide
the cancellation-preserving fourth-power input. -/
theorem
    crouzeix_palencia_of_convexThickening_cauchy_support_boundaryPhase_approximation
    (A : E →L[ℂ] E) (Omega : ℕ → SmoothJordanDomain)
    (hcarrier : ∀ n, (Omega n).carrier =
      convexThickeningApprox (closure (numericalRange A)) n)
    (hCauchyP : ∀ (p : Polynomial ℂ) (n : ℕ),
      Polynomial.aeval A p =
        (2 * (Real.pi : ℂ) * I)⁻¹ •
          contourIntegral
            (fun z => Polynomial.eval z p • resolvent A z)
            (Omega n).boundaryParam)
    (hsupport : ∀ (n : ℕ) (t : ℝ),
      t ∈ Ioc (0 : ℝ) (2 * Real.pi) →
      ∀ w ∈ numericalRange A,
        ((starRingEnd ℂ) (-I * deriv (Omega n).boundaryParam t) *
          (w - (Omega n).boundaryParam t)).re ≤ 0)
    (hkernel : ∀ (n : ℕ) (z : ℂ), z ∈ (Omega n).carrier →
      crouzeixScalarCauchyKernel (Omega n) z = 1)
    (hreg : ∀ (p : Polynomial ℂ) (n : ℕ)
      (xi : ℂ), xi ∈ frontier (Omega n).carrier →
      Tendsto
        (crouzeixPolynomialScalarCompanionRegularized (Omega n) p xi)
        (nhdsWithin xi (Omega n).carrier)
        (nhds
          (crouzeixPolynomialScalarCompanionRegularized
            (Omega n) p xi xi)))
    (hphase : ∀ (p : Polynomial ℂ) (n : ℕ)
      (xi : ℂ), xi ∈ frontier (Omega n).carrier →
      ‖star (Polynomial.eval xi p) +
          crouzeixPolynomialBoundaryPhaseTransform (Omega n) xi
            (p /ₘ (Polynomial.X - Polynomial.C xi))‖ ≤
        polynomialSupNorm p (frontier (Omega n).carrier))
    (happrox : ∀ (p : Polynomial ℂ) (n : ℕ),
      ∃ r : ℕ → Polynomial ℂ,
        ∀ (j : ℕ) (z : ℂ),
          z ∈ compactThickeningApprox (closure (numericalRange A)) n →
          ‖Polynomial.eval z (r j) -
              crouzeixPolynomialScalarCompanionClosedExtension
                (Omega n) p z‖ ≤
            1 / ((j : ℝ) + 1))
    (hPlemelj : ∀ (p : Polynomial ℂ) (n : ℕ),
      crouzeixAuxiliaryOperator A (Omega n)
          (crouzeixPolynomialScalarCompanionClosedExtension (Omega n) p) =
        crouzeixPolynomialAuxiliaryOperator A (Omega n) p) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by
  let K : Set ℂ := closure (numericalRange A)
  have hKcompact : IsCompact K := by
    have hbounded : Bornology.IsBounded (numericalRange A) :=
      Metric.isBounded_closedBall.subset (fun z hz ↦ by
        rw [Metric.mem_closedBall, dist_zero_right]
        exact norm_le_of_mem_numericalRange A hz)
    simpa only [K] using hbounded.isCompact_closure
  have hstageBounded : ∀ n, Bornology.IsBounded (Omega n).carrier := by
    intro n
    rw [hcarrier n]
    exact hKcompact.isBounded.thickening
  have hclosure : ∀ n,
      closure (Omega n).carrier = compactThickeningApprox K n := by
    intro n
    rw [hcarrier n]
    unfold convexThickeningApprox compactThickeningApprox
    exact closure_thickening (by
      unfold smoothApproxRadius
      positivity) K
  apply
    crouzeixPalencia_of_thickening_cauchy_support_continuous_companion_approximation
      A Omega hcarrier hCauchyP hsupport
  intro p n
  obtain ⟨r, hr⟩ := happrox p n
  have hr' : ∀ (j : ℕ) (z : ℂ), z ∈ closure (Omega n).carrier →
      ‖Polynomial.eval z (r j) -
          crouzeixPolynomialScalarCompanionClosedExtension (Omega n) p z‖ ≤
        1 / ((j : ℝ) + 1) := by
    intro j z hz
    apply hr j z
    simpa only [K, ← hclosure n] using hz
  obtain ⟨g, q, hgcont, hgbound, hqapprox, hgaux⟩ :=
    exists_continuous_scalarCompanion_approximation_of_boundaryPhaseTransform
      A (Omega n) p (hstageBounded n) (hkernel n)
        (hreg p n) (hphase p n) r hr' (hPlemelj p n)
  refine ⟨g, q, hgcont, ?_, ?_, hgaux⟩
  · intro z hz
    change z ∈ compactThickeningApprox K n at hz
    rw [← hclosure n] at hz
    have hg := hgbound z hz
    rw [hclosure n] at hg
    simpa only [K] using hg
  · intro j z hz
    change z ∈ compactThickeningApprox K n at hz
    rw [← hclosure n] at hz
    exact hqapprox j z hz

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
