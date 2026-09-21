/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
/-
# The separated Crouzeix--Palencia product contour

The pointwise polynomial resolvent splitting in `PalenciaSupport.lean` writes
the integrand for `p(A) G` as the difference of two terms.  To estimate those
terms separately, one first has to know that the divided-difference term
depends continuously on the boundary point.  This file proves that continuity
directly from Mathlib's coefficient formula

`coeff (p /ₘ (X - C z)) n = ∑ i, z ^ (i - n - 1) * coeff p i`,

then proves contour integrability of both terms and separates the contour
integral.  The resulting identity is exact, but its two terms are not
independently sharp: applying the triangle inequality loses the cancellation
needed for the `m²` product constant.  The separated form is therefore an
algebraic diagnostic and a possible input to a stronger coupled invariant,
not by itself a reduction to two attainable norm estimates.

## Main declarations

* `continuous_aeval_divByMonic_X_sub_C` -- continuity of the evaluated
  polynomial divided difference in its boundary point.
* `crouzeixProductMainIntegrand_contourIntegrable` and
  `crouzeixProductRemainderIntegrand_contourIntegrable` -- integrability of
  the two separated product-contour terms.
* `crouzeixProductRemainderPolynomial` and
  `normalized_crouzeixProductRemainderContour_eq_aeval` -- the remainder
  contour is polynomial functional calculus of degree strictly below that
  of a nonconstant input polynomial.
* `crouzeixProductRemainderPolynomial_smul` -- degree-two homogeneity of the
  remainder, its evaluated norm, and its polynomial sup norm under scaling.
* `crouzeixSquareAuxiliaryOperator_smul` -- matching degree-two homogeneity
  of the scalar-square main auxiliary operator.
* `aeval_mul_crouzeixPolynomialAuxiliaryOperator_eq_main_sub_remainder` --
  the exact separated contour identity for `p(A) G`.
* `aeval_mul_crouzeixPolynomialAuxiliaryOperator_eq_main_sub_aeval_remainderPolynomial`
  -- the same identity with the lower-degree remainder written as polynomial
  functional calculus.
* `aeval_mul_crouzeixPolynomialAuxiliaryOperator_eq_squareAux_sub_aeval_remainderPolynomial`
  -- the recursive form: a scalar-square auxiliary operator minus the
  lower-degree polynomial functional calculus.
* `norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_le_main_add_remainder`
  -- the corresponding two-term norm reduction.
-/
import LeanPool.OperatorTheory.Operator.Crouzeix.PalenciaSupport
import Mathlib.Topology.Algebra.Polynomial

open Complex Polynomial Set
open scoped InnerProductSpace Interval Real

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The operator evaluation of the divided difference
`p /ₘ (X - C z)` depends continuously on `z`.

This is not an immediate application of continuity of polynomial evaluation,
because the polynomial itself varies with `z`.  Expanding every coefficient
of the quotient as a finite polynomial sum in `z` makes continuity explicit. -/
theorem continuous_aeval_divByMonic_X_sub_C
    (A : E →L[ℂ] E) (p : Polynomial ℂ) :
    Continuous (fun z : ℂ =>
      Polynomial.aeval A (p /ₘ (Polynomial.X - Polynomial.C z))) := by
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
  fun_prop

/-- Every coefficient of the polynomial divided difference depends
continuously on its boundary point. -/
theorem continuous_coeff_divByMonic_X_sub_C (p : Polynomial ℂ) (n : ℕ) :
    Continuous (fun z : ℂ =>
      (p /ₘ (Polynomial.X - Polynomial.C z)).coeff n) := by
  have hfun :
      (fun z : ℂ => (p /ₘ (Polynomial.X - Polynomial.C z)).coeff n) =
      fun z => ∑ i ∈ Finset.Icc (n + 1) p.natDegree,
        z ^ (i - (n + 1)) * p.coeff i := by
    funext z
    rw [Polynomial.coeff_divByMonic_X_sub_C]
  rw [hfun]
  fun_prop

private theorem contourIntegral_pow_eq_zero
    (Omega : SmoothJordanDomain) (n : ℕ) :
    contourIntegral (fun z : ℂ => z ^ n) Omega.boundaryParam = 0 := by
  apply contourIntegral_eq_zero_of_hasDerivAt_of_closed
    (Fp := fun z : ℂ => z ^ (n + 1) / ((n + 1 : ℕ) : ℂ))
  · intro _ _
    exact (Omega.boundaryParam_contDiff.differentiable (by norm_num)).differentiableAt
  · intro t _
    convert (hasDerivAt_pow (n + 1) (Omega.boundaryParam t)).div_const
      ((n + 1 : ℕ) : ℂ) using 1
    · rfl
    · field_simp
      congr 1
  · apply ContourIntegrable.of_continuousOn
    · exact Omega.boundaryParam_contDiff.continuous.continuousOn
    · exact (Omega.boundaryParam_contDiff.continuous_deriv (by norm_num)).continuousOn
    · exact (continuous_pow n).continuousOn
  · simpa only [zero_add] using Omega.boundaryParam_periodic 0

private theorem contourIntegral_finset_sum_pow_mul_eq_zero
    (Omega : SmoothJordanDomain) (s : Finset ℕ) (k : ℕ → ℕ) (c : ℕ → ℂ) :
    contourIntegral (fun z : ℂ => ∑ j ∈ s, z ^ k j * c j)
      Omega.boundaryParam = 0 := by
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty, smul_zero, contourIntegral,
        intervalIntegral.integral_zero]
  | @insert a s ha ih =>
      let f : ℂ → ℂ := fun z => z ^ k a * c a
      let g : ℂ → ℂ := fun z => ∑ j ∈ s, z ^ k j * c j
      have hf : ContourIntegrable f Omega.boundaryParam := by
        apply ContourIntegrable.of_continuousOn
        · exact Omega.boundaryParam_contDiff.continuous.continuousOn
        · exact (Omega.boundaryParam_contDiff.continuous_deriv (by norm_num)).continuousOn
        · exact ((continuous_pow (k a)).mul continuous_const).continuousOn
      have hg : ContourIntegrable g Omega.boundaryParam := by
        apply ContourIntegrable.of_continuousOn
        · exact Omega.boundaryParam_contDiff.continuous.continuousOn
        · exact (Omega.boundaryParam_contDiff.continuous_deriv (by norm_num)).continuousOn
        · exact (continuous_finsetSum s fun j _ =>
            (continuous_pow (k j)).mul continuous_const).continuousOn
      have hterm : contourIntegral f Omega.boundaryParam = 0 := by
        have hfun : f = fun z => c a • z ^ k a := by
          funext z
          simp only [f, smul_eq_mul]
          ring
        rw [hfun, contourIntegral_smul, contourIntegral_pow_eq_zero, smul_zero]
      have hfun :
          (fun z : ℂ => ∑ j ∈ insert a s, z ^ k j * c j) =
            fun z => f z + g z := by
        funext z
        rw [Finset.sum_insert ha]
      rw [hfun, contourIntegral_add hf hg, hterm, ih, zero_add]

/-- The scalar-square resolvent term in the Crouzeix--Palencia product
splitting is contour integrable on every smooth boundary containing the
closed numerical range. -/
theorem crouzeixProductMainIntegrand_contourIntegrable [CompleteSpace E]
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier) :
    ContourIntegrable
      (fun z => (star (Polynomial.eval z p) * Polynomial.eval z p) •
        resolvent A z) Omega.boundaryParam := by
  exact crouzeixAuxiliaryIntegrand_contourIntegrable A Omega
    (fun z => star (Polynomial.eval z p) * Polynomial.eval z p) hOmega
    (p.continuous.star.mul p.continuous).continuousOn

/-- The polynomial divided-difference remainder in the
Crouzeix--Palencia product splitting is contour integrable on every smooth
boundary. -/
theorem crouzeixProductRemainderIntegrand_contourIntegrable
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain) (p : Polynomial ℂ) :
    ContourIntegrable
      (fun z => star (Polynomial.eval z p) •
        Polynomial.aeval A (p /ₘ (Polynomial.X - Polynomial.C z)))
      Omega.boundaryParam := by
  apply ContourIntegrable.of_continuousOn
  · exact Omega.boundaryParam_contDiff.continuous.continuousOn
  · exact (Omega.boundaryParam_contDiff.continuous_deriv (by norm_num)).continuousOn
  · exact (p.continuous.star.smul
      (continuous_aeval_divByMonic_X_sub_C A p)).continuousOn

/-- The divided-difference remainder contour is a finite sum of scalar
contour coefficients multiplying powers of `A`. -/
theorem contourIntegral_crouzeixProductRemainder_eq_sum [CompleteSpace E]
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain) (p : Polynomial ℂ) :
    contourIntegral
        (fun z => star (Polynomial.eval z p) •
          Polynomial.aeval A (p /ₘ (Polynomial.X - Polynomial.C z)))
        Omega.boundaryParam =
      ∑ i ∈ Finset.range p.natDegree,
        contourIntegral
          (fun z => star (Polynomial.eval z p) *
            (p /ₘ (Polynomial.X - Polynomial.C z)).coeff i)
          Omega.boundaryParam • A ^ i := by
  by_cases hp : p.natDegree = 0
  · have hqzero : ∀ z : ℂ, p /ₘ (Polynomial.X - Polynomial.C z) = 0 := by
      intro z
      ext i
      rw [Polynomial.coeff_divByMonic_X_sub_C, hp]
      rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]
      simp only [coeff_zero]
    simp only [hqzero, map_zero, smul_zero, contourIntegral, intervalIntegral.integral_zero,
      hp, Finset.range_zero, Finset.sum_empty]
  · have hdegree (z : ℂ) :
        (p /ₘ (Polynomial.X - Polynomial.C z)).natDegree < p.natDegree := by
      rw [Polynomial.natDegree_divByMonic p (Polynomial.monic_X_sub_C z),
        Polynomial.natDegree_X_sub_C]
      omega
    have hfun :
        (fun z => star (Polynomial.eval z p) •
          Polynomial.aeval A (p /ₘ (Polynomial.X - Polynomial.C z))) =
        fun z => ∑ i ∈ Finset.range p.natDegree,
          (star (Polynomial.eval z p) *
            (p /ₘ (Polynomial.X - Polynomial.C z)).coeff i) • A ^ i := by
      funext z
      rw [Polynomial.aeval_eq_sum_range' (hdegree z) A]
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [smul_smul]
    rw [hfun]
    unfold contourIntegral
    simp only [Finset.smul_sum, smul_smul]
    rw [intervalIntegral.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro i hi
      simp only [intervalIntegral.integral_smul_const, smul_eq_mul]
    · intro i hi
      have hcontinuous : Continuous (fun z : ℂ =>
          star (Polynomial.eval z p) *
            (p /ₘ (Polynomial.X - Polynomial.C z)).coeff i) :=
        p.continuous.star.mul (continuous_coeff_divByMonic_X_sub_C p i)
      have hcontour : ContourIntegrable
          (fun z => (star (Polynomial.eval z p) *
            (p /ₘ (Polynomial.X - Polynomial.C z)).coeff i) • A ^ i)
          Omega.boundaryParam := by
        apply ContourIntegrable.of_continuousOn
        · exact Omega.boundaryParam_contDiff.continuous.continuousOn
        · exact (Omega.boundaryParam_contDiff.continuous_deriv (by norm_num)).continuousOn
        · exact (hcontinuous.smul continuous_const).continuousOn
      simpa only [ContourIntegrable, smul_smul, smul_eq_mul] using hcontour

/-- The polynomial whose functional calculus is the normalized
divided-difference remainder contour. -/
noncomputable def crouzeixProductRemainderPolynomial
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) : Polynomial ℂ :=
  ∑ i ∈ Finset.range p.natDegree,
    Polynomial.monomial i
      ((2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
        contourIntegral
          (fun z => star (Polynomial.eval z p) *
            (p /ₘ (Polynomial.X - Polynomial.C z)).coeff i)
          Omega.boundaryParam)

/-- Adding a constant to `p` leaves its product-remainder polynomial
unchanged.  The divided difference does not see the constant, while the new
cross term is the contour integral of a scalar polynomial and hence vanishes
on the closed boundary. -/
theorem crouzeixProductRemainderPolynomial_add_C
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) (a : ℂ) :
    crouzeixProductRemainderPolynomial Omega (p + Polynomial.C a) =
      crouzeixProductRemainderPolynomial Omega p := by
  have hquot (z : ℂ) (i : ℕ) :
      ((p + Polynomial.C a) /ₘ (Polynomial.X - Polynomial.C z)).coeff i =
        (p /ₘ (Polynomial.X - Polynomial.C z)).coeff i := by
    rw [Polynomial.coeff_divByMonic_X_sub_C, Polynomial.coeff_divByMonic_X_sub_C,
      Polynomial.natDegree_add_C]
    apply Finset.sum_congr rfl
    intro j hj
    have hjpos : 0 < j := lt_of_lt_of_le (Nat.zero_lt_succ i) (Finset.mem_Icc.mp hj).1
    simp only [Polynomial.coeff_add, Polynomial.coeff_C, if_neg (Nat.ne_of_gt hjpos), add_zero]
  have hintegral (i : ℕ) :
      contourIntegral
          (fun z => star (Polynomial.eval z (p + Polynomial.C a)) *
            ((p + Polynomial.C a) /ₘ
              (Polynomial.X - Polynomial.C z)).coeff i)
          Omega.boundaryParam =
        contourIntegral
          (fun z => star (Polynomial.eval z p) *
            (p /ₘ (Polynomial.X - Polynomial.C z)).coeff i)
          Omega.boundaryParam := by
    let f : ℂ → ℂ := fun z => star (Polynomial.eval z p) *
      (p /ₘ (Polynomial.X - Polynomial.C z)).coeff i
    let g : ℂ → ℂ := fun z => star a *
      (p /ₘ (Polynomial.X - Polynomial.C z)).coeff i
    have hf : ContourIntegrable f Omega.boundaryParam := by
      apply ContourIntegrable.of_continuousOn
      · exact Omega.boundaryParam_contDiff.continuous.continuousOn
      · exact (Omega.boundaryParam_contDiff.continuous_deriv (by norm_num)).continuousOn
      · exact (p.continuous.star.mul
          (continuous_coeff_divByMonic_X_sub_C p i)).continuousOn
    have hg : ContourIntegrable g Omega.boundaryParam := by
      apply ContourIntegrable.of_continuousOn
      · exact Omega.boundaryParam_contDiff.continuous.continuousOn
      · exact (Omega.boundaryParam_contDiff.continuous_deriv (by norm_num)).continuousOn
      · exact (continuous_const.mul
          (continuous_coeff_divByMonic_X_sub_C p i)).continuousOn
    have hcoeffzero : contourIntegral
        (fun z => (p /ₘ (Polynomial.X - Polynomial.C z)).coeff i)
        Omega.boundaryParam = 0 := by
      have hfun :
          (fun z => (p /ₘ (Polynomial.X - Polynomial.C z)).coeff i) =
            fun z => ∑ j ∈ Finset.Icc (i + 1) p.natDegree,
              z ^ (j - (i + 1)) * p.coeff j := by
        funext z
        rw [Polynomial.coeff_divByMonic_X_sub_C]
      rw [hfun]
      exact contourIntegral_finset_sum_pow_mul_eq_zero Omega _ _ _
    have hgzero : contourIntegral g Omega.boundaryParam = 0 := by
      have hfun : g = fun z => star a •
          (p /ₘ (Polynomial.X - Polynomial.C z)).coeff i := by
        funext z
        simp only [g, smul_eq_mul]
      rw [hfun, contourIntegral_smul, hcoeffzero, smul_zero]
    have hfun :
        (fun z => star (Polynomial.eval z (p + Polynomial.C a)) *
          ((p + Polynomial.C a) /ₘ
            (Polynomial.X - Polynomial.C z)).coeff i) =
          fun z => f z + g z := by
      funext z
      rw [Polynomial.eval_add, Polynomial.eval_C, hquot]
      rw [star_add]
      simp only [f, g]
      ring
    rw [hfun, contourIntegral_add hf hg, hgzero, add_zero]
  unfold crouzeixProductRemainderPolynomial
  rw [Polynomial.natDegree_add_C]
  apply Finset.sum_congr rfl
  intro i _
  rw [hintegral]

/-- Scaling `p` by `a` scales its product-remainder polynomial by
`star a * a`. -/
theorem crouzeixProductRemainderPolynomial_smul
    (Omega : SmoothJordanDomain) (a : ℂ) (p : Polynomial ℂ) :
    crouzeixProductRemainderPolynomial Omega (a • p) =
      (star a * a) • crouzeixProductRemainderPolynomial Omega p := by
  by_cases ha : a = 0
  · subst a
    simp only [zero_smul, star_zero, zero_mul,
      crouzeixProductRemainderPolynomial, Polynomial.natDegree_zero,
      Finset.range_zero, Finset.sum_empty]
  have hcoeff (z : ℂ) (i : ℕ) :
      ((a • p) /ₘ (Polynomial.X - Polynomial.C z)).coeff i =
        a * (p /ₘ (Polynomial.X - Polynomial.C z)).coeff i := by
    rw [Polynomial.coeff_divByMonic_X_sub_C, Polynomial.coeff_divByMonic_X_sub_C]
    rw [Polynomial.natDegree_smul p ha]
    simp only [Polynomial.coeff_smul, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hintegral (i : ℕ) :
      contourIntegral
          (fun z => star (Polynomial.eval z (a • p)) *
            ((a • p) /ₘ (Polynomial.X - Polynomial.C z)).coeff i)
          Omega.boundaryParam =
        (star a * a) *
          contourIntegral
            (fun z => star (Polynomial.eval z p) *
              (p /ₘ (Polynomial.X - Polynomial.C z)).coeff i)
            Omega.boundaryParam := by
    have hfun :
        (fun z => star (Polynomial.eval z (a • p)) *
          ((a • p) /ₘ (Polynomial.X - Polynomial.C z)).coeff i) =
        fun z => (star a * a) •
          (star (Polynomial.eval z p) *
            (p /ₘ (Polynomial.X - Polynomial.C z)).coeff i) := by
      funext z
      rw [Polynomial.eval_smul, hcoeff]
      simp only [smul_eq_mul, star_mul]
      ring
    rw [hfun, contourIntegral_smul]
    simp only [smul_eq_mul]
  unfold crouzeixProductRemainderPolynomial
  rw [Finset.smul_sum]
  apply Finset.sum_congr
  · rw [Polynomial.natDegree_smul p ha]
  · intro i hi
    rw [hintegral]
    simp only [Polynomial.smul_monomial]
    congr 1
    ring

/-- After evaluation at `A`, the remainder polynomial is homogeneous of
degree two in norm. -/
theorem norm_aeval_crouzeixProductRemainderPolynomial_smul
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain) (a : ℂ) (p : Polynomial ℂ) :
    ‖Polynomial.aeval A (crouzeixProductRemainderPolynomial Omega (a • p))‖ =
      ‖a‖ ^ 2 *
        ‖Polynomial.aeval A (crouzeixProductRemainderPolynomial Omega p)‖ := by
  rw [crouzeixProductRemainderPolynomial_smul, map_smul, norm_smul,
    norm_mul, norm_star, pow_two]

/-- The product-remainder polynomial has degree-two homogeneity in polynomial
sup norm on every control set. -/
theorem polynomialSupNorm_crouzeixProductRemainderPolynomial_smul
    (Omega : SmoothJordanDomain) (a : ℂ) (p : Polynomial ℂ) (K : Set ℂ) :
    polynomialSupNorm (crouzeixProductRemainderPolynomial Omega (a • p)) K =
      ‖a‖ ^ 2 * polynomialSupNorm (crouzeixProductRemainderPolynomial Omega p) K := by
  rw [crouzeixProductRemainderPolynomial_smul, polynomialSupNorm_smul,
    norm_mul, norm_star, pow_two]

/-- Scaling by a nonzero scalar preserves the natural degree of the
product-remainder polynomial. -/
theorem natDegree_crouzeixProductRemainderPolynomial_smul
    (Omega : SmoothJordanDomain) (a : ℂ) (p : Polynomial ℂ) (ha : a ≠ 0) :
    (crouzeixProductRemainderPolynomial Omega (a • p)).natDegree =
      (crouzeixProductRemainderPolynomial Omega p).natDegree := by
  rw [crouzeixProductRemainderPolynomial_smul,
    Polynomial.natDegree_smul _ (mul_ne_zero (star_ne_zero.mpr ha) ha)]

/-- The auxiliary operator is complex-linear in its scalar boundary datum. -/
theorem crouzeixAuxiliaryOperator_smul (A : E →L[ℂ] E)
    (Omega : SmoothJordanDomain) (a : ℂ) (h : ℂ → ℂ) :
    crouzeixAuxiliaryOperator A Omega (fun z => a • h z) =
      a • crouzeixAuxiliaryOperator A Omega h := by
  unfold crouzeixAuxiliaryOperator
  have hfun :
      (fun z => (a • h z) • resolvent A z) =
        fun z => a • (h z • resolvent A z) := by
    funext z
    simp only [smul_eq_mul, smul_smul]
  rw [hfun, contourIntegral_smul]
  simp only [smul_smul]
  rw [mul_comm (2 * (Real.pi : ℂ) * Complex.I)⁻¹ a]

/-- The scalar-square main auxiliary operator is homogeneous of degree two
under polynomial scaling. -/
theorem crouzeixSquareAuxiliaryOperator_smul (A : E →L[ℂ] E)
    (Omega : SmoothJordanDomain) (a : ℂ) (p : Polynomial ℂ) :
    crouzeixAuxiliaryOperator A Omega
        (fun z => star (Polynomial.eval z (a • p)) * Polynomial.eval z (a • p)) =
      (star a * a) • crouzeixAuxiliaryOperator A Omega
        (fun z => star (Polynomial.eval z p) * Polynomial.eval z p) := by
  have hfun :
      (fun z => star (Polynomial.eval z (a • p)) * Polynomial.eval z (a • p)) =
      fun z => (star a * a) •
        (star (Polynomial.eval z p) * Polynomial.eval z p) := by
    funext z
    rw [Polynomial.eval_smul]
    simp only [smul_eq_mul, star_mul]
    ring
  rw [hfun, crouzeixAuxiliaryOperator_smul]

/-- The scalar-square main auxiliary operator has the corresponding
degree-two norm homogeneity. -/
theorem norm_crouzeixSquareAuxiliaryOperator_smul (A : E →L[ℂ] E)
    (Omega : SmoothJordanDomain) (a : ℂ) (p : Polynomial ℂ) :
    ‖crouzeixAuxiliaryOperator A Omega
        (fun z => star (Polynomial.eval z (a • p)) * Polynomial.eval z (a • p))‖ =
      ‖a‖ ^ 2 * ‖crouzeixAuxiliaryOperator A Omega
        (fun z => star (Polynomial.eval z p) * Polynomial.eval z p)‖ := by
  rw [crouzeixSquareAuxiliaryOperator_smul, norm_smul, norm_mul, norm_star, pow_two]

/-- For a nonconstant `p`, its product-remainder polynomial has strictly
smaller degree. -/
theorem natDegree_crouzeixProductRemainderPolynomial_lt
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) (hp : 0 < p.natDegree) :
    (crouzeixProductRemainderPolynomial Omega p).natDegree < p.natDegree := by
  unfold crouzeixProductRemainderPolynomial
  have hle :
      (∑ i ∈ Finset.range p.natDegree,
        Polynomial.monomial i
          ((2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
            contourIntegral
              (fun z => star (Polynomial.eval z p) *
                (p /ₘ (Polynomial.X - Polynomial.C z)).coeff i)
              Omega.boundaryParam)).natDegree ≤ p.natDegree - 1 := by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro i hi
    exact (Polynomial.natDegree_monomial_le _).trans
      (Nat.le_pred_of_lt (Finset.mem_range.mp hi))
  exact hle.trans_lt (Nat.sub_lt hp (by norm_num))

/-- A constant polynomial has zero product-remainder polynomial. -/
theorem crouzeixProductRemainderPolynomial_eq_zero_of_natDegree_eq_zero
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) (hp : p.natDegree = 0) :
    crouzeixProductRemainderPolynomial Omega p = 0 := by
  simp only [crouzeixProductRemainderPolynomial, hp, Finset.range_zero, Finset.sum_empty]

/-- The normalized divided-difference remainder contour is exactly the
evaluation at `A` of `crouzeixProductRemainderPolynomial`. -/
theorem normalized_crouzeixProductRemainderContour_eq_aeval
    [CompleteSpace E] (A : E →L[ℂ] E) (Omega : SmoothJordanDomain)
    (p : Polynomial ℂ) :
    (2 * (Real.pi : ℂ) * Complex.I)⁻¹ •
        contourIntegral
          (fun z => star (Polynomial.eval z p) •
            Polynomial.aeval A (p /ₘ (Polynomial.X - Polynomial.C z)))
          Omega.boundaryParam =
      Polynomial.aeval A (crouzeixProductRemainderPolynomial Omega p) := by
  rw [contourIntegral_crouzeixProductRemainder_eq_sum]
  unfold crouzeixProductRemainderPolynomial
  rw [map_sum]
  simp only [Finset.smul_sum, Polynomial.aeval_monomial,
    Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, smul_smul]

/-- The product `p(A) G` is the normalized scalar-square resolvent contour
minus the normalized polynomial divided-difference remainder contour. -/
theorem aeval_mul_crouzeixPolynomialAuxiliaryOperator_eq_main_sub_remainder
    [CompleteSpace E] (A : E →L[ℂ] E) (Omega : SmoothJordanDomain)
    (p : Polynomial ℂ)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier) :
    Polynomial.aeval A p * crouzeixPolynomialAuxiliaryOperator A Omega p =
      (2 * (Real.pi : ℂ) * Complex.I)⁻¹ •
          contourIntegral
            (fun z => (star (Polynomial.eval z p) * Polynomial.eval z p) •
              resolvent A z) Omega.boundaryParam -
        (2 * (Real.pi : ℂ) * Complex.I)⁻¹ •
          contourIntegral
            (fun z => star (Polynomial.eval z p) •
              Polynomial.aeval A (p /ₘ (Polynomial.X - Polynomial.C z)))
            Omega.boundaryParam := by
  rw [aeval_mul_crouzeixPolynomialAuxiliaryOperator_eq_split A Omega p hOmega]
  rw [contourIntegral_sub
    (crouzeixProductMainIntegrand_contourIntegrable A Omega p hOmega)
    (crouzeixProductRemainderIntegrand_contourIntegrable A Omega p)]
  rw [smul_sub]

/-- The product `p(A) G` is the scalar-square resolvent contour minus
functional calculus of the explicitly constructed lower-degree remainder
polynomial. -/
theorem
    aeval_mul_crouzeixPolynomialAuxiliaryOperator_eq_main_sub_aeval_remainderPolynomial
    [CompleteSpace E] (A : E →L[ℂ] E) (Omega : SmoothJordanDomain)
    (p : Polynomial ℂ)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier) :
    Polynomial.aeval A p * crouzeixPolynomialAuxiliaryOperator A Omega p =
      (2 * (Real.pi : ℂ) * Complex.I)⁻¹ •
          contourIntegral
            (fun z => (star (Polynomial.eval z p) * Polynomial.eval z p) •
              resolvent A z) Omega.boundaryParam -
        Polynomial.aeval A (crouzeixProductRemainderPolynomial Omega p) := by
  rw [aeval_mul_crouzeixPolynomialAuxiliaryOperator_eq_main_sub_remainder
    A Omega p hOmega]
  rw [normalized_crouzeixProductRemainderContour_eq_aeval]

/-- The induction-ready product decomposition: `p(A) G` is the auxiliary
operator associated to the scalar boundary datum `|p|²`, minus functional
calculus of a strictly lower-degree polynomial. -/
theorem
    aeval_mul_crouzeixPolynomialAuxiliaryOperator_eq_squareAux_sub_aeval_remainderPolynomial
    [CompleteSpace E] (A : E →L[ℂ] E) (Omega : SmoothJordanDomain)
    (p : Polynomial ℂ)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier) :
    Polynomial.aeval A p * crouzeixPolynomialAuxiliaryOperator A Omega p =
      crouzeixAuxiliaryOperator A Omega
          (fun z => star (Polynomial.eval z p) * Polynomial.eval z p) -
        Polynomial.aeval A (crouzeixProductRemainderPolynomial Omega p) := by
  rw [
    aeval_mul_crouzeixPolynomialAuxiliaryOperator_eq_main_sub_aeval_remainderPolynomial
      A Omega p hOmega]
  rfl

/-- The recursive product decomposition reduces its norm to the norm of the
scalar-square auxiliary operator plus the lower-degree functional calculus
term. -/
theorem
    norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_le_squareAux_add_remainder
    [CompleteSpace E] (A : E →L[ℂ] E) (Omega : SmoothJordanDomain)
    (p : Polynomial ℂ)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier) :
    ‖Polynomial.aeval A p * crouzeixPolynomialAuxiliaryOperator A Omega p‖ ≤
      ‖crouzeixAuxiliaryOperator A Omega
        (fun z => star (Polynomial.eval z p) * Polynomial.eval z p)‖ +
      ‖Polynomial.aeval A (crouzeixProductRemainderPolynomial Omega p)‖ := by
  rw [
    aeval_mul_crouzeixPolynomialAuxiliaryOperator_eq_squareAux_sub_aeval_remainderPolynomial
      A Omega p hOmega]
  exact norm_sub_le _ _

/-- The triangle-inequality consequence of the exact separated contour
identity.  This estimate is valid, but it does not retain the cancellation
needed for the sharp `m²` product bound. -/
theorem norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_le_main_add_remainder
    [CompleteSpace E] (A : E →L[ℂ] E) (Omega : SmoothJordanDomain)
    (p : Polynomial ℂ)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier) :
    ‖Polynomial.aeval A p * crouzeixPolynomialAuxiliaryOperator A Omega p‖ ≤
      ‖(2 * (Real.pi : ℂ) * Complex.I)⁻¹ •
        contourIntegral
          (fun z => (star (Polynomial.eval z p) * Polynomial.eval z p) •
            resolvent A z) Omega.boundaryParam‖ +
      ‖(2 * (Real.pi : ℂ) * Complex.I)⁻¹ •
        contourIntegral
          (fun z => star (Polynomial.eval z p) •
            Polynomial.aeval A (p /ₘ (Polynomial.X - Polynomial.C z)))
          Omega.boundaryParam‖ := by
  rw [aeval_mul_crouzeixPolynomialAuxiliaryOperator_eq_main_sub_remainder
    A Omega p hOmega]
  exact norm_sub_le _ _

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
