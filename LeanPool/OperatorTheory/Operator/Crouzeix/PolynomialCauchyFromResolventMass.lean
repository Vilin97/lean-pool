/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
module


public import LeanPool.OperatorTheory.Operator.Crouzeix.ProductContour

/-!
# Polynomial Cauchy representation from resolvent mass

The all-polynomial operator Cauchy formula on a smooth contour follows
algebraically from its constant-polynomial case.  The resolvent splitting

`p(A) R_A(z) = p(z) R_A(z) - (p / (X - z))(A)`

leaves a divided-difference remainder which is polynomial in `z`.  Its
integral around any closed smooth parametrized boundary vanishes term by
term.  Thus a single normalized resolvent-mass identity supplies the full
polynomial representation required by the Crouzeix--Palencia assembly.

## Main declarations

* `contourIntegral_aeval_divByMonic_X_sub_C_eq_zero` -- the evaluated
  divided-difference remainder has zero closed-contour integral;
* `polynomial_aeval_eq_normalized_contourIntegral_of_resolvent_mass` --
  resolvent mass implies the normalized polynomial operator Cauchy formula.
-/

@[expose] public section

open Complex Polynomial Set
open scoped InnerProductSpace Interval Real

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

/-- The operator-valued divided difference
`z ↦ (p /ₘ (X - C z))(A)` has zero integral around every smooth closed
boundary.  Coefficient expansion makes it a finite sum of nonnegative powers
of `z`, each of which has a global polynomial primitive. -/
theorem contourIntegral_aeval_divByMonic_X_sub_C_eq_zero
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain) (p : Polynomial ℂ) :
    contourIntegral
        (fun z => Polynomial.aeval A
          (p /ₘ (Polynomial.X - Polynomial.C z)))
        Omega.boundaryParam = 0 := by
  have hfun :
      (fun z : ℂ => Polynomial.aeval A
        (p /ₘ (Polynomial.X - Polynomial.C z))) =
      fun z => ∑ i ∈ Finset.range (p.natDegree + 1),
        (∑ j ∈ Finset.Icc (i + 1) p.natDegree,
          z ^ (j - (i + 1)) * p.coeff j) • A ^ i := by
    funext z
    rw [Polynomial.aeval_eq_sum_range' (x := A) (n := p.natDegree + 1)]
    · congr 1 with i
      rw [Polynomial.coeff_divByMonic_X_sub_C]
    · rw [Polynomial.natDegree_divByMonic p (Polynomial.monic_X_sub_C z),
        Polynomial.natDegree_X_sub_C]
      omega
  rw [hfun]
  unfold contourIntegral
  simp only [Finset.smul_sum, smul_smul]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_eq_zero
    intro i _
    rw [intervalIntegral.integral_smul_const]
    have hzero :=
      contourIntegral_finset_sum_pow_mul_eq_zero
        Omega (Finset.Icc (i + 1) p.natDegree)
          (fun j => j - (i + 1)) (fun j => p.coeff j)
    unfold contourIntegral at hzero
    have hzero' := congrArg (fun c : ℂ => c • A ^ i) hzero
    simpa only [smul_eq_mul, zero_smul] using hzero'
  · intro i _
    have hcontour : ContourIntegrable
        (fun z => (∑ j ∈ Finset.Icc (i + 1) p.natDegree,
          z ^ (j - (i + 1)) * p.coeff j) • A ^ i)
        Omega.boundaryParam := by
      apply ContourIntegrable.of_continuousOn
      · exact Omega.boundaryParam_contDiff.continuous.continuousOn
      · exact
          (Omega.boundaryParam_contDiff.continuous_deriv (by norm_num)).continuousOn
      · exact (continuous_finsetSum (Finset.Icc (i + 1) p.natDegree) fun j _ =>
          (continuous_pow (j - (i + 1))).mul continuous_const).smul
            continuous_const |>.continuousOn
    simpa only [ContourIntegrable, smul_smul, smul_eq_mul] using hcontour

/-- A single resolvent-mass identity implies the normalized operator Cauchy
formula for every polynomial.  No general-domain Cauchy theorem is needed for
the polynomial remainder: it vanishes by an explicit primitive computation. -/
theorem polynomial_aeval_eq_normalized_contourIntegral_of_resolvent_mass
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier)
    (hmass : contourIntegral (resolvent A) Omega.boundaryParam =
      (2 * (Real.pi : ℂ) * I) • (1 : E →L[ℂ] E))
    (p : Polynomial ℂ) :
    Polynomial.aeval A p =
      (2 * (Real.pi : ℂ) * I)⁻¹ •
        contourIntegral
          (fun z => Polynomial.eval z p • resolvent A z)
          Omega.boundaryParam := by
  let F : E →L[ℂ] E := Polynomial.aeval A p
  let Q : ℂ → E →L[ℂ] E := fun z =>
    Polynomial.aeval A (p /ₘ (Polynomial.X - Polynomial.C z))
  have hresolvent : ContourIntegrable (resolvent A) Omega.boundaryParam := by
    simpa only [one_smul] using
      crouzeixAuxiliaryIntegrand_contourIntegrable A Omega (fun _ => 1)
        hOmega continuous_const.continuousOn
  have hQ : ContourIntegrable Q Omega.boundaryParam := by
    apply ContourIntegrable.of_continuousOn
    · exact Omega.boundaryParam_contDiff.continuous.continuousOn
    · exact
        (Omega.boundaryParam_contDiff.continuous_deriv (by norm_num)).continuousOn
    · exact (continuous_aeval_divByMonic_X_sub_C A p).continuousOn
  have hFresolvent : ContourIntegrable (fun z => F * resolvent A z)
      Omega.boundaryParam := by
    unfold ContourIntegrable at hresolvent ⊢
    have hfun :
        (fun t => deriv Omega.boundaryParam t •
          (F * resolvent A (Omega.boundaryParam t))) =
        fun t => F * (deriv Omega.boundaryParam t •
          resolvent A (Omega.boundaryParam t)) := by
      funext t
      exact (Algebra.mul_smul_comm (deriv Omega.boundaryParam t) F
        (resolvent A (Omega.boundaryParam t))).symm
    rw [hfun]
    exact hresolvent.const_mul F
  have hpoint : ∀ t : ℝ,
      Polynomial.eval (Omega.boundaryParam t) p •
          resolvent A (Omega.boundaryParam t) =
        F * resolvent A (Omega.boundaryParam t) +
          Q (Omega.boundaryParam t) := by
    intro t
    have h := aeval_mul_resolvent_eq_eval_mul_resolvent_sub_aeval_divByMonic
      A p (Omega.boundaryParam_mem_resolventSet A hOmega t)
    dsimp only [F, Q]
    exact ((eq_sub_iff_add_eq).mp h).symm
  have hsplit :
      contourIntegral (fun z => Polynomial.eval z p • resolvent A z)
          Omega.boundaryParam =
        contourIntegral (fun z => F * resolvent A z) Omega.boundaryParam +
          contourIntegral Q Omega.boundaryParam := by
    rw [← contourIntegral_add hFresolvent hQ]
    unfold contourIntegral
    apply intervalIntegral.integral_congr
    intro t _
    exact congrArg (fun T : E →L[ℂ] E =>
      deriv Omega.boundaryParam t • T) (hpoint t)
  rw [hsplit, contourIntegral_const_mul F hresolvent]
  have hQzero : contourIntegral Q Omega.boundaryParam = 0 := by
    exact contourIntegral_aeval_divByMonic_X_sub_C_eq_zero A Omega p
  rw [hQzero, add_zero, hmass]
  dsimp only [F]
  simp only [mul_smul_comm, mul_one, smul_smul]
  rw [inv_mul_cancel₀]
  · exact (one_smul ℂ (Polynomial.aeval A p)).symm
  · exact mul_ne_zero (mul_ne_zero (by norm_num)
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
