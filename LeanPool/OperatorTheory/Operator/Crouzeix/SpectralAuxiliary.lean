/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
module


public import LeanPool.OperatorTheory.Operator.Crouzeix.SpectralCauchy

/-!
# The centered-circle auxiliary operator under spectral enclosure

The circle Cauchy formulas in `SpectralCauchy.lean` require only that the
spectrum lie strictly inside the circle.  This file applies their resolvent
and negative-Laurent identities to the conjugate boundary values of a
polynomial.  As in the operator-norm model, every positive monomial vanishes
and only the constant coefficient remains.

This identity does not supply the product norm estimate in the general
Crouzeix--Palencia argument: that estimate still needs the divided-difference
boundary transform rather than a disk von Neumann inequality.

## Main declaration

* `crouzeixPolynomialAuxiliaryOperator_ball_eq_eval_zero_smul_one_of_spectrum_subset_ball`
  -- the exact auxiliary value when the centered circle encloses the spectrum.
* `norm_aeval_add_eval_zero_smul_one_le_two_mul_polynomialSupNorm_closedBall` -- the resulting
  scalar form of the symmetrized estimate when the circle encloses the numerical range.
-/

public section

open Complex ComplexConjugate Polynomial Set spectrum
open scoped InnerProductSpace Interval Real

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

private theorem circleIntegrable_star_eval_smul_resolvent_of_spectrum_subset_ball
    (A : E →L[ℂ] E) {r : ℝ} (hr : 0 < r)
    (hσ : spectrum ℂ A ⊆ Metric.ball (0 : ℂ) r) (q : Polynomial ℂ) :
    CircleIntegrable (fun z => star (Polynomial.eval z q) • resolvent A z) 0 r := by
  apply ContinuousOn.circleIntegrable hr.le
  refine q.continuous.star.continuousOn.smul ?_
  intro z hz
  have hznot : z ∉ Metric.ball (0 : ℂ) r := by
    intro hzball
    rw [Metric.mem_ball] at hzball
    rw [Metric.mem_sphere] at hz
    rw [hz] at hzball
    exact (lt_irrefl r) hzball
  exact (spectrum.hasDerivAt_resolvent_const_left
    (mem_resolventSet_of_notMem_ball_of_spectrum_subset A hσ hznot)).continuousAt.continuousWithinAt

private theorem normalized_circleIntegral_resolvent_eq_one_of_spectrum_subset_ball
    (A : E →L[ℂ] E) {r : ℝ} (hr : 0 < r)
    (hσ : spectrum ℂ A ⊆ Metric.ball (0 : ℂ) r) :
    (2 * (Real.pi : ℂ) * I)⁻¹ • circleIntegral (resolvent A) 0 r =
      (1 : E →L[ℂ] E) := by
  simpa only [Polynomial.eval_one, one_smul, map_one] using
    (normalized_circleIntegral_eval_smul_resolvent_eq_aeval_of_spectrum_subset_ball
      A hr hσ (1 : Polynomial ℂ))

/-- If `spectrum ℂ A` lies in the centered open disk of radius `r`, the
conjugate-polynomial auxiliary operator on its boundary circle is the
constant operator `star (p.eval 0) • 1`. -/
theorem crouzeixPolynomialAuxiliaryOperator_ball_eq_eval_zero_smul_one_of_spectrum_subset_ball
    (A : E →L[ℂ] E) {r : ℝ} (hr : 0 < r)
    (hσ : spectrum ℂ A ⊆ Metric.ball (0 : ℂ) r) (p : Polynomial ℂ) :
    crouzeixPolynomialAuxiliaryOperator A (SmoothJordanDomain.ball 0 r hr) p =
      star (Polynomial.eval 0 p) • (1 : E →L[ℂ] E) := by
  exact crouzeixPolynomialAuxiliaryOperator_ball_eq_eval_zero_of_circle_integrals
    A hr (circleIntegrable_star_eval_smul_resolvent_of_spectrum_subset_ball A hr hσ)
    (normalized_circleIntegral_resolvent_eq_one_of_spectrum_subset_ball A hr hσ)
    (normalized_circleIntegral_inv_pow_smul_resolvent_eq_zero_of_spectrum_subset_ball A hr hσ) p

/-- If the closure of the numerical range lies inside a centered open disk,
the symmetrized Crouzeix--Palencia estimate can be written without an
auxiliary-operator symbol: its adjoint is simply `p.eval 0 • 1`. -/
theorem norm_aeval_add_eval_zero_smul_one_le_two_mul_polynomialSupNorm_closedBall
    (A : E →L[ℂ] E) {r : ℝ} (hr : 0 < r)
    (hW : closure (numericalRange A) ⊆ Metric.ball (0 : ℂ) r) (p : Polynomial ℂ) :
    ‖Polynomial.aeval A p + Polynomial.eval 0 p • (1 : E →L[ℂ] E)‖ ≤
      2 * polynomialSupNorm p (Metric.closedBall (0 : ℂ) r) := by
  have hσ : spectrum ℂ A ⊆ Metric.ball (0 : ℂ) r :=
    (spectrum_subset_closure_numericalRange A).trans hW
  have hbound :=
    norm_aeval_add_star_auxiliary_ball_le_of_closedNumericalRange_subset_ball
      A hr hW p
  rw [crouzeixPolynomialAuxiliaryOperator_ball_eq_eval_zero_smul_one_of_spectrum_subset_ball
    A hr hσ p] at hbound
  simpa only [star_smul, star_star, star_one] using hbound

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
