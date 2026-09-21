/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
/-
# Symmetrized polynomial auxiliary operator

The L4.2d estimate identifies `p(A) + G†` with a polynomial-weighted
double-layer integral.  This file proves that identification from the
explicit Cauchy representation of `p(A)`.  The remaining analytic input is
kept as a named hypothesis, so a circle or general contour Cauchy theorem can
supply it without changing the algebraic interface.

## Main declaration

* `aeval_add_star_crouzeixPolynomialAuxiliaryOperator_eq_doubleLayerIntegral_of_cauchy`
  -- the normalized symmetrized auxiliary operator is the polynomial-weighted
  integral of the resolvent double-layer kernel.
-/
import LeanPool.OperatorTheory.Operator.Crouzeix.AdjointIntegral
import LeanPool.OperatorTheory.Operator.Crouzeix.AuxOperator

open Complex MeasureTheory Set
open scoped InnerProductSpace Interval Real

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

/-- Assuming the normalized contour Cauchy representation of `p(A)`, the
symmetrized operator `p(A) + G†` is `(2π)⁻¹` times the integral of the
boundary values of `p` against the double-layer resolvent kernel. -/
theorem aeval_add_star_crouzeixPolynomialAuxiliaryOperator_eq_doubleLayerIntegral_of_cauchy
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier)
    (hCauchy : Polynomial.aeval A p =
      (2 * (Real.pi : ℂ) * I)⁻¹ •
        contourIntegral (fun z => Polynomial.eval z p • resolvent A z)
          Omega.boundaryParam) :
    Polynomial.aeval A p + star (crouzeixPolynomialAuxiliaryOperator A Omega p) =
      (2 * Real.pi)⁻¹ •
        (∫ t in (0 : ℝ)..(2 * Real.pi),
          Polynomial.eval (Omega.boundaryParam t) p •
            (((-I * deriv Omega.boundaryParam t) •
                resolvent A (Omega.boundaryParam t)) +
              ContinuousLinearMap.adjoint
                ((-I * deriv Omega.boundaryParam t) •
                  resolvent A (Omega.boundaryParam t)))) := by
  let gamma := Omega.boundaryParam
  let f : ℝ → ℂ := fun t => Polynomial.eval (gamma t) p
  let B : ℝ → E →L[ℂ] E := fun t =>
    (-I * deriv gamma t) • resolvent A (gamma t)
  have hpContour : ContourIntegrable
      (fun z => Polynomial.eval z p • resolvent A z) gamma :=
    crouzeixAuxiliaryIntegrand_contourIntegrable A Omega
      (fun z => Polynomial.eval z p) hOmega p.continuous.continuousOn
  have hstarContour : ContourIntegrable
      (fun z => star (Polynomial.eval z p) • resolvent A z) gamma :=
    crouzeixPolynomialAuxiliaryIntegrand_contourIntegrable A Omega p hOmega
  have hfBfun : (fun t => f t • B t) = fun t =>
      (-I) • (deriv gamma t • (f t • resolvent A (gamma t))) := by
    funext t
    simp only [B, smul_smul]
    congr 1
    ring
  have hstarfBfun : (fun t => star (f t) • B t) = fun t =>
      (-I) • (deriv gamma t • (star (f t) • resolvent A (gamma t))) := by
    funext t
    simp only [B, smul_smul]
    congr 1
    ring
  change IntervalIntegrable
    (fun t => deriv gamma t •
      (Polynomial.eval (gamma t) p • resolvent A (gamma t)))
      volume 0 (2 * Real.pi) at hpContour
  change IntervalIntegrable
    (fun t => deriv gamma t •
      (star (Polynomial.eval (gamma t) p) • resolvent A (gamma t)))
      volume 0 (2 * Real.pi) at hstarContour
  have hfB : IntervalIntegrable (fun t => f t • B t)
      volume 0 (2 * Real.pi) := by
    rw [hfBfun]
    exact ⟨hpContour.1.smul_enorm (-I), hpContour.2.smul_enorm (-I)⟩
  have hstarfB : IntervalIntegrable (fun t => star (f t) • B t)
      volume 0 (2 * Real.pi) := by
    rw [hstarfBfun]
    exact ⟨hstarContour.1.smul_enorm (-I), hstarContour.2.smul_enorm (-I)⟩
  have hsymm := ContinuousLinearMap.intervalIntegral_smul_add_adjoint
    B f hfB hstarfB
  have hP : (∫ t in (0 : ℝ)..(2 * Real.pi), f t • B t) =
      (-I) • contourIntegral
        (fun z => Polynomial.eval z p • resolvent A z) gamma := by
    rw [hfBfun, intervalIntegral.integral_smul]
    rfl
  have hQ : (∫ t in (0 : ℝ)..(2 * Real.pi), star (f t) • B t) =
      (-I) • contourIntegral
        (fun z => star (Polynomial.eval z p) • resolvent A z) gamma := by
    rw [hstarfBfun, intervalIntegral.integral_smul]
    rfl
  have hcoeff : ((((2 * Real.pi)⁻¹ : ℝ) : ℂ) * (-I)) =
      (2 * (Real.pi : ℂ) * I)⁻¹ := by
    symm
    calc
      (2 * (Real.pi : ℂ) * I)⁻¹ = I⁻¹ * (2 * (Real.pi : ℂ))⁻¹ :=
        mul_inv_rev _ _
      _ = (-I) * (2 * (Real.pi : ℂ))⁻¹ := by rw [inv_I]
      _ = (-I) * ((((2 * Real.pi)⁻¹ : ℝ) : ℂ)) := by
        rw [Complex.ofReal_inv]
        push_cast
        rfl
      _ = ((((2 * Real.pi)⁻¹ : ℝ) : ℂ) * (-I)) := mul_comm _ _
  have hcoeffStar : star ((2 * (Real.pi : ℂ) * I)⁻¹) =
      (((2 * Real.pi)⁻¹ : ℝ) : ℂ) * star (-I) := by
    have h := congrArg star hcoeff
    rw [star_mul, mul_comm] at h
    have hreal : star ((((2 * Real.pi)⁻¹ : ℝ) : ℂ)) =
        (((2 * Real.pi)⁻¹ : ℝ) : ℂ) := Complex.conj_ofReal _
    rw [hreal] at h
    exact h.symm
  have hF : Polynomial.aeval A p =
      (2 * Real.pi)⁻¹ • (∫ t in (0 : ℝ)..(2 * Real.pi), f t • B t) := by
    rw [hCauchy, hP, RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul]
    congr 1
    exact hcoeff.symm
  have hG : star (crouzeixPolynomialAuxiliaryOperator A Omega p) =
      (2 * Real.pi)⁻¹ • ContinuousLinearMap.adjoint
        (∫ t in (0 : ℝ)..(2 * Real.pi), star (f t) • B t) := by
    rw [ContinuousLinearMap.star_eq_adjoint]
    unfold crouzeixPolynomialAuxiliaryOperator crouzeixAuxiliaryOperator
    rw [hQ, map_smulₛₗ, map_smulₛₗ,
      RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul]
    congr 1
  rw [hF, hG, ← smul_add]
  simpa only [f, B, gamma] using
    congrArg (fun T : E →L[ℂ] E => (2 * Real.pi)⁻¹ • T) hsymm

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
