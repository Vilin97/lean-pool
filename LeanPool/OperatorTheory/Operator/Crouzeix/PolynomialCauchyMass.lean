/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

import LeanPool.OperatorTheory.Operator.Crouzeix.AuxOperator

/-!
# Resolvent mass from the polynomial Cauchy representation

The normalized operator-valued Cauchy representation for every polynomial
already contains the raw resolvent mass identity: specialize it to the
constant polynomial `1` and clear the nonzero scalar `2πi`.

## Main declaration

* `contourIntegral_resolvent_eq_two_pi_I_smul_one_of_polynomial_cauchy` --
  derives the raw resolvent contour identity from polynomial Cauchy data.
-/

open Complex
open scoped InnerProductSpace

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- A normalized Cauchy representation valid for all polynomials implies the
raw resolvent contour mass identity by taking the constant polynomial `1`. -/
theorem contourIntegral_resolvent_eq_two_pi_I_smul_one_of_polynomial_cauchy
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain)
    (hCauchyP : ∀ p : Polynomial ℂ,
      Polynomial.aeval A p =
        (2 * (Real.pi : ℂ) * I)⁻¹ •
          contourIntegral
            (fun z => Polynomial.eval z p • resolvent A z)
            Omega.boundaryParam) :
    contourIntegral (resolvent A) Omega.boundaryParam =
      (2 * (Real.pi : ℂ) * I) • (1 : E →L[ℂ] E) := by
  let c : ℂ := 2 * (Real.pi : ℂ) * I
  have hc : c ≠ 0 := by
    exact mul_ne_zero
      (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
  have h := hCauchyP (Polynomial.C 1)
  simp only [Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one,
    Polynomial.eval_C, one_smul] at h
  change (1 : E →L[ℂ] E) =
    c⁻¹ • contourIntegral (resolvent A) Omega.boundaryParam at h
  change contourIntegral (resolvent A) Omega.boundaryParam =
    c • (1 : E →L[ℂ] E)
  calc
    contourIntegral (resolvent A) Omega.boundaryParam =
        (1 : ℂ) • contourIntegral (resolvent A) Omega.boundaryParam := by
      exact (one_smul ℂ _).symm
    _ = (c * c⁻¹) • contourIntegral (resolvent A) Omega.boundaryParam := by
      rw [mul_inv_cancel₀ hc]
    _ = c • (c⁻¹ • contourIntegral (resolvent A) Omega.boundaryParam) := by
      rw [smul_smul]
    _ = c • (1 : E →L[ℂ] E) := by rw [← h]

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
