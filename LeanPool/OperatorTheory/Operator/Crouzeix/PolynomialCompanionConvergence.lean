/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
/-
# Boundary approximation implies polynomial-companion convergence

For any continuous scalar boundary datum, if polynomials approximate that
datum uniformly and satisfy the polynomial Cauchy representation, their
evaluations at the operator converge in norm to the associated normalized
resolvent contour integral.  The canonical Crouzeix auxiliary operator is the
specialization to the conjugate boundary values of a polynomial.

This file makes the passage quantitative.  Compactness of the parameter
interval bounds `deriv γ(t) • resolvent A (γ(t))` by a fixed constant, so a
boundary error of `1 / (j + 1)` gives an operator error bounded by a fixed
multiple of the same null sequence.

## Main declaration

* `tendsto_aeval_to_crouzeixAuxiliaryOperator_of_boundary_approximation`
  -- the generic continuous-boundary-datum convergence theorem.
* `tendsto_aeval_to_crouzeixPolynomialAuxiliaryOperator_of_boundary_approximation`
  -- its conjugate-polynomial specialization.
-/
import LeanPool.OperatorTheory.Operator.Crouzeix.AuxOperator

open Complex Filter MeasureTheory Set
open scoped InnerProductSpace Interval Real

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

/-- Uniform approximation of a continuous scalar boundary datum at rate
`1 / (j + 1)` implies operator-norm convergence of the polynomial evaluations
to its normalized resolvent contour integral. -/
theorem
    tendsto_aeval_to_crouzeixAuxiliaryOperator_of_boundary_approximation
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain) (g : ℂ → ℂ)
    (q : ℕ → Polynomial ℂ)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier)
    (hg : ContinuousOn g
      (Omega.boundaryParam '' Icc (0 : ℝ) (2 * Real.pi)))
    (hCauchy : ∀ j, Polynomial.aeval A (q j) =
      (2 * (Real.pi : ℂ) * I)⁻¹ •
        contourIntegral
          (fun z ↦ Polynomial.eval z (q j) • resolvent A z)
          Omega.boundaryParam)
    (happrox : ∀ (j : ℕ) (t : ℝ),
      t ∈ Icc (0 : ℝ) (2 * Real.pi) →
      ‖Polynomial.eval (Omega.boundaryParam t) (q j) -
        g (Omega.boundaryParam t)‖ ≤
          1 / ((j : ℝ) + 1)) :
    Tendsto (fun j ↦ Polynomial.aeval A (q j)) atTop
      (nhds (crouzeixAuxiliaryOperator A Omega g)) := by
  obtain ⟨C, hC⟩ :=
    exists_bound_crouzeixPolynomialAuxiliaryIntegrand A Omega
      (Polynomial.C 1) hOmega
  have hkernel : ∀ t ∈ Icc (0 : ℝ) (2 * Real.pi),
      ‖deriv Omega.boundaryParam t •
        resolvent A (Omega.boundaryParam t)‖ ≤ C := by
    intro t ht
    simpa only [Polynomial.eval_C, star_one, one_smul] using hC t ht
  have hC0 : 0 ≤ C :=
    (norm_nonneg (deriv Omega.boundaryParam 0 •
      resolvent A (Omega.boundaryParam 0))).trans
      (hkernel 0 ⟨le_rfl, Real.two_pi_pos.le⟩)
  let D : ℝ := ‖(2 * (Real.pi : ℂ) * I)⁻¹‖ * (2 * Real.pi * C)
  have hdist : ∀ j, dist (Polynomial.aeval A (q j))
      (crouzeixAuxiliaryOperator A Omega g) ≤
        D * (1 / ((j : ℝ) + 1)) := by
    intro j
    have hqint : ContourIntegrable
        (fun z ↦ Polynomial.eval z (q j) • resolvent A z)
        Omega.boundaryParam :=
      crouzeixAuxiliaryIntegrand_contourIntegrable A Omega
        (fun z ↦ Polynomial.eval z (q j)) hOmega
          (q j).continuous.continuousOn
    have hgint :=
      crouzeixAuxiliaryIntegrand_contourIntegrable A Omega g hOmega hg
    have hintegrand : ∀ t ∈ Icc (0 : ℝ) (2 * Real.pi),
        ‖deriv Omega.boundaryParam t •
          ((Polynomial.eval (Omega.boundaryParam t) (q j) -
              g (Omega.boundaryParam t)) •
            resolvent A (Omega.boundaryParam t))‖ ≤
          (1 / ((j : ℝ) + 1)) * C := by
      intro t ht
      rw [smul_smul, norm_smul, norm_mul]
      calc
        ‖deriv Omega.boundaryParam t‖ *
            ‖Polynomial.eval (Omega.boundaryParam t) (q j) -
              g (Omega.boundaryParam t)‖ *
              ‖resolvent A (Omega.boundaryParam t)‖ =
            ‖Polynomial.eval (Omega.boundaryParam t) (q j) -
              g (Omega.boundaryParam t)‖ *
              ‖deriv Omega.boundaryParam t •
                resolvent A (Omega.boundaryParam t)‖ := by
          rw [norm_smul]
          ring
        _ ≤ (1 / ((j : ℝ) + 1)) * C :=
          mul_le_mul (happrox j t ht) (hkernel t ht) (norm_nonneg _) (by positivity)
    rw [dist_eq_norm, hCauchy j]
    unfold crouzeixAuxiliaryOperator
    rw [← smul_sub, ← contourIntegral_sub hqint hgint]
    simp only [← sub_smul]
    change ‖(2 * (Real.pi : ℂ) * I)⁻¹ •
        contourIntegral
          (fun z ↦ (Polynomial.eval z (q j) -
            g z) • resolvent A z)
          Omega.boundaryParam‖ ≤ D * (1 / ((j : ℝ) + 1))
    rw [norm_smul]
    calc
      ‖(2 * (Real.pi : ℂ) * I)⁻¹‖ *
          ‖contourIntegral
            (fun z ↦ (Polynomial.eval z (q j) -
              g z) • resolvent A z)
            Omega.boundaryParam‖ ≤
          ‖(2 * (Real.pi : ℂ) * I)⁻¹‖ *
            (2 * Real.pi * ((1 / ((j : ℝ) + 1)) * C)) :=
        mul_le_mul_of_nonneg_left
          (norm_contourIntegral_le_of_norm_le_const hintegrand) (norm_nonneg _)
      _ = D * (1 / ((j : ℝ) + 1)) := by
        simp only [D]
        ring
  rw [tendsto_iff_dist_tendsto_zero]
  apply squeeze_zero (fun _ ↦ dist_nonneg) hdist
  have heps : Tendsto (fun j : ℕ ↦ 1 / ((j : ℝ) + 1)) atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  simpa only [mul_zero] using tendsto_const_nhds.mul heps

/-- Uniform approximation of the conjugate polynomial boundary datum at rate
`1 / (j + 1)` implies operator-norm convergence of the polynomial evaluations
to the canonical Crouzeix auxiliary operator. -/
theorem
    tendsto_aeval_to_crouzeixPolynomialAuxiliaryOperator_of_boundary_approximation
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (q : ℕ → Polynomial ℂ)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier)
    (hCauchy : ∀ j, Polynomial.aeval A (q j) =
      (2 * (Real.pi : ℂ) * I)⁻¹ •
        contourIntegral
          (fun z ↦ Polynomial.eval z (q j) • resolvent A z)
          Omega.boundaryParam)
    (happrox : ∀ (j : ℕ) (t : ℝ),
      t ∈ Icc (0 : ℝ) (2 * Real.pi) →
      ‖Polynomial.eval (Omega.boundaryParam t) (q j) -
        star (Polynomial.eval (Omega.boundaryParam t) p)‖ ≤
          1 / ((j : ℝ) + 1)) :
    Tendsto (fun j ↦ Polynomial.aeval A (q j)) atTop
      (nhds (crouzeixPolynomialAuxiliaryOperator A Omega p)) := by
  simpa only [crouzeixPolynomialAuxiliaryOperator] using
    tendsto_aeval_to_crouzeixAuxiliaryOperator_of_boundary_approximation
      A Omega (fun z ↦ star (Polynomial.eval z p)) q hOmega
        p.continuous.star.continuousOn hCauchy happrox

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
