/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
/-
# Constant-polynomial base case for the auxiliary product bound

The recursive product decomposition in `ProductContour.lean` lowers the
degree of its polynomial remainder.  This file supplies the corresponding
degree-zero base case on an arbitrary smooth contour satisfying the raw
resolvent Cauchy identity.

For `p = C a`, the conjugate-polynomial auxiliary operator is
`star a • 1`.  Hence `p(A) G` has norm `‖a‖²`, which is exactly the square of
the polynomial sup norm on every nonempty set.

## Main declarations

* `polynomialSupNorm_C_of_nonempty` -- the sup norm of a constant polynomial.
* `normalized_contourIntegral_resolvent_eq_one_of_cauchy` -- normalization of
  the raw resolvent Cauchy mass identity.
* `crouzeixPolynomialAuxiliaryOperator_C_eq_star_smul_one` -- the auxiliary
  operator for a constant polynomial.
* `norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_le_polynomialSupNorm_sq_of_natDegree_eq_zero`
  -- the sharp L4.2e base case.
-/
import LeanPool.OperatorTheory.Operator.Crouzeix.ProductContour
import LeanPool.OperatorTheory.Operator.Crouzeix.VonNeumann

open Complex Polynomial Set
open scoped InnerProductSpace Interval Real

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The polynomial sup norm of `C a` on a nonempty set is `‖a‖`. -/
theorem polynomialSupNorm_C_of_nonempty (a : ℂ) {K : Set ℂ}
    (hK : K.Nonempty) : polynomialSupNorm (Polynomial.C a) K = ‖a‖ := by
  apply le_antisymm
  · unfold polynomialSupNorm
    refine Real.iSup_le (fun z => ?_) (norm_nonneg a)
    exact Real.iSup_le (fun hz => by
      simp only [Polynomial.eval_C]
      exact le_rfl) (norm_nonneg a)
  · obtain ⟨z, hz⟩ := hK
    simpa only [Polynomial.eval_C] using
      (norm_eval_le_polynomialSupNorm (Polynomial.C a)
        ⟨‖a‖, by
          rintro _ ⟨w, hw, rfl⟩
          simp only [Polynomial.eval_C]
          exact le_rfl⟩ hz)

/-- A raw smooth-contour resolvent Cauchy identity becomes the identity
operator after multiplication by `(2πi)⁻¹`. -/
theorem normalized_contourIntegral_resolvent_eq_one_of_cauchy [CompleteSpace E]
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain)
    (hCauchy : contourIntegral (resolvent A) Omega.boundaryParam =
      (2 * (Real.pi : ℂ) * Complex.I) • (1 : E →L[ℂ] E)) :
    (2 * (Real.pi : ℂ) * Complex.I)⁻¹ •
        contourIntegral (resolvent A) Omega.boundaryParam = 1 := by
  rw [hCauchy, smul_smul]
  rw [inv_mul_cancel₀]
  · exact one_smul _ _
  · exact mul_ne_zero
      (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero

/-- On a contour satisfying the resolvent Cauchy identity, the auxiliary
operator for `C a` is `star a • 1`. -/
theorem crouzeixPolynomialAuxiliaryOperator_C_eq_star_smul_one
    [CompleteSpace E] (A : E →L[ℂ] E) (Omega : SmoothJordanDomain) (a : ℂ)
    (hCauchy : contourIntegral (resolvent A) Omega.boundaryParam =
      (2 * (Real.pi : ℂ) * Complex.I) • (1 : E →L[ℂ] E)) :
    crouzeixPolynomialAuxiliaryOperator A Omega (Polynomial.C a) =
      star a • (1 : E →L[ℂ] E) := by
  unfold crouzeixPolynomialAuxiliaryOperator crouzeixAuxiliaryOperator
  simp only [Polynomial.eval_C]
  rw [contourIntegral_smul, smul_smul]
  rw [mul_comm (2 * (Real.pi : ℂ) * Complex.I)⁻¹ (star a), ← smul_smul]
  rw [normalized_contourIntegral_resolvent_eq_one_of_cauchy A Omega hCauchy]

/-- Adding a constant to a polynomial adds the conjugate scalar identity to
its auxiliary operator.  This is the operator counterpart of the exact
constant-shift invariance of the product remainder. -/
theorem crouzeixPolynomialAuxiliaryOperator_add_C
    [CompleteSpace E] (A : E →L[ℂ] E) (Omega : SmoothJordanDomain)
    (p : Polynomial ℂ) (a : ℂ)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier)
    (hCauchy : contourIntegral (resolvent A) Omega.boundaryParam =
      (2 * (Real.pi : ℂ) * Complex.I) • (1 : E →L[ℂ] E)) :
    crouzeixPolynomialAuxiliaryOperator A Omega (p + Polynomial.C a) =
      crouzeixPolynomialAuxiliaryOperator A Omega p +
        star a • (1 : E →L[ℂ] E) := by
  rw [crouzeixPolynomialAuxiliaryOperator_add A Omega p (Polynomial.C a) hOmega,
    crouzeixPolynomialAuxiliaryOperator_C_eq_star_smul_one A Omega a hCauchy]

/-- Exact constant-shift expansion of the auxiliary product.  All four
terms are retained, so a later quadratic-form argument may choose the
centering scalar without discarding cancellation. -/
theorem aeval_mul_crouzeixPolynomialAuxiliaryOperator_add_C
    [CompleteSpace E] (A : E →L[ℂ] E) (Omega : SmoothJordanDomain)
    (p : Polynomial ℂ) (a : ℂ)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier)
    (hCauchy : contourIntegral (resolvent A) Omega.boundaryParam =
      (2 * (Real.pi : ℂ) * Complex.I) • (1 : E →L[ℂ] E)) :
    Polynomial.aeval A (p + Polynomial.C a) *
        crouzeixPolynomialAuxiliaryOperator A Omega (p + Polynomial.C a) =
      Polynomial.aeval A p * crouzeixPolynomialAuxiliaryOperator A Omega p +
        star a • Polynomial.aeval A p +
        a • crouzeixPolynomialAuxiliaryOperator A Omega p +
        (a * star a) • (1 : E →L[ℂ] E) := by
  rw [map_add, Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one,
    crouzeixPolynomialAuxiliaryOperator_add_C A Omega p a hOmega hCauchy]
  simp only [add_mul, mul_add, mul_smul_comm, smul_mul_assoc,
    one_mul, mul_one]
  module

/-- **Sharp L4.2e base case.**  A degree-zero polynomial satisfies the
auxiliary product bound on every nonempty control set, provided the smooth
contour has the resolvent Cauchy mass identity. -/
theorem
    norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_le_polynomialSupNorm_sq_of_natDegree_eq_zero
    [CompleteSpace E] (A : E →L[ℂ] E) (Omega : SmoothJordanDomain)
    (p : Polynomial ℂ) {K : Set ℂ} (hK : K.Nonempty) (hp : p.natDegree = 0)
    (hCauchy : contourIntegral (resolvent A) Omega.boundaryParam =
      (2 * (Real.pi : ℂ) * Complex.I) • (1 : E →L[ℂ] E)) :
    ‖Polynomial.aeval A p * crouzeixPolynomialAuxiliaryOperator A Omega p‖ ≤
      polynomialSupNorm p K ^ 2 := by
  rw [Polynomial.eq_C_of_natDegree_eq_zero hp]
  let a := p.coeff 0
  rw [crouzeixPolynomialAuxiliaryOperator_C_eq_star_smul_one A Omega a hCauchy]
  rcases subsingleton_or_nontrivial E with hE | hE
  · let _ := hE
    have hzero : Polynomial.aeval A (Polynomial.C a) *
        (star a • (1 : E →L[ℂ] E)) = 0 := Subsingleton.elim _ _
    rw [hzero, norm_zero]
    exact sq_nonneg _
  · let _ := hE
    rw [Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one]
    simp only [smul_mul_smul, norm_smul, norm_mul, norm_star, norm_one, mul_one]
    rw [polynomialSupNorm_C_of_nonempty a hK]
    change ‖a‖ * ‖a‖ ≤ ‖a‖ ^ 2
    rw [pow_two]

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
