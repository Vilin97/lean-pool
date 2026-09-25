/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.CorvajaZannier.FiniteExtensionPolynomialHeight
public import LeanPool.MarkoffModP.BGS.CorvajaZannier.PlaneCurveRatFuncModel

/-!
# Exact heights of powered plane-curve coordinates

The two rational-function-field models of a plane curve identify the base
variable `RatFunc.X` with the corresponding coordinate function.  Combining
those models with the polynomial-height formula computes the positive degree
of the principal divisor of `x ^ m - 1` and `y ^ n - 1` exactly.
-/

@[expose] public section

namespace BGS.CorvajaZannier

noncomputable section

variable {K : Type*} [Field K] [DecidableEq K]
  [DecidableEq (RatFunc K)]

/-- In the first-coordinate `RatFunc K` model, the positive principal-divisor
degree of `x ^ m - 1` is `m` times the degree of the curve equation in the
second coordinate. -/
theorem finiteExtensionPositiveDegree_planeCurveFirstCoordinate_pow_sub_one
    {f : MvPolynomial (Fin 2) K} (hf : Irreducible f)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    (m : ℕ) (hm : 0 < m) :
    letI := planeCurveCoordinateRing_isDomain hf
    let hx := firstCoordinate_transcendental hf
      (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
    letI := planeCurveFirstCoordinateRatFuncAlgebra f hx
    letI := finiteDimensional_planeCurveFunctionField_over_ratFunc
      hf hpartialSecond
    letI := separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
    finiteExtensionPositiveDegree K (PlaneCurveFunctionField f)
        ((planeCurveFunction f 0) ^ m - 1) =
      MvPolynomial.degreeOf 1 f * m := by
  let : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let hx := firstCoordinate_transcendental hf
    (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
  let : Algebra (RatFunc K) (PlaneCurveFunctionField f) :=
    planeCurveFirstCoordinateRatFuncAlgebra f hx
  let : FiniteDimensional (RatFunc K) (PlaneCurveFunctionField f) :=
    finiteDimensional_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  let : Algebra.IsSeparable (RatFunc K) (PlaneCurveFunctionField f) :=
    separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  classical
  let P : Polynomial K := Polynomial.X ^ m - 1
  have hP : P ≠ 0 := by
    simpa [P] using
      (Polynomial.X_pow_sub_C_ne_zero (R := K) hm (1 : K))
  have hheight := finiteExtensionPositiveDegree_polynomial
    K (PlaneCurveFunctionField f) P hP
  have hmap :
      algebraMap (RatFunc K) (PlaneCurveFunctionField f)
          (algebraMap (Polynomial K) (RatFunc K) P) =
        (planeCurveFunction f 0) ^ m - 1 := by
    simp [P]
    rw [show ratFuncSpecialization (planeCurveFunction f 0) hx RatFunc.X =
      planeCurveFunction f 0 by
        exact planeCurveFirstCoordinateRatFuncAlgebra_X f hx]
  rw [hmap,
    finrank_planeCurveFunctionField_over_ratFunc_eq_degreeOf_second
      hf hpartialSecond,
    show P.natDegree = m by
      simpa [P] using (Polynomial.natDegree_X_pow_sub_C
        (R := K) (n := m) (r := 1))]
    at hheight
  exact hheight

/-- In the second-coordinate `RatFunc K` model, the positive
principal-divisor degree of `y ^ n - 1` is `n` times the degree of the curve
equation in the first coordinate. -/
theorem finiteExtensionPositiveDegree_planeCurveSecondCoordinate_pow_sub_one
    {f : MvPolynomial (Fin 2) K} (hf : Irreducible f)
    (hpartialFirst : MvPolynomial.pderiv 0 f ≠ 0)
    (n : ℕ) (hn : 0 < n) :
    letI := planeCurveCoordinateRing_isDomain hf
    let hy := secondCoordinate_transcendental hf
      (degreeOf_first_pos_of_pderiv_ne_zero hpartialFirst)
    letI := planeCurveSecondCoordinateRatFuncAlgebra f hy
    letI := finiteDimensional_planeCurveFunctionField_over_secondRatFunc
      hf hpartialFirst
    letI := separable_planeCurveFunctionField_over_secondRatFunc hf hpartialFirst
    finiteExtensionPositiveDegree K (PlaneCurveFunctionField f)
        ((planeCurveFunction f 1) ^ n - 1) =
      MvPolynomial.degreeOf 0 f * n := by
  let : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let hy := secondCoordinate_transcendental hf
    (degreeOf_first_pos_of_pderiv_ne_zero hpartialFirst)
  let : Algebra (RatFunc K) (PlaneCurveFunctionField f) :=
    planeCurveSecondCoordinateRatFuncAlgebra f hy
  let : FiniteDimensional (RatFunc K) (PlaneCurveFunctionField f) :=
    finiteDimensional_planeCurveFunctionField_over_secondRatFunc
      hf hpartialFirst
  let : Algebra.IsSeparable (RatFunc K) (PlaneCurveFunctionField f) :=
    separable_planeCurveFunctionField_over_secondRatFunc hf hpartialFirst
  classical
  let P : Polynomial K := Polynomial.X ^ n - 1
  have hP : P ≠ 0 := by
    simpa [P] using
      (Polynomial.X_pow_sub_C_ne_zero (R := K) hn (1 : K))
  have hheight := finiteExtensionPositiveDegree_polynomial
    K (PlaneCurveFunctionField f) P hP
  have hmap :
      algebraMap (RatFunc K) (PlaneCurveFunctionField f)
          (algebraMap (Polynomial K) (RatFunc K) P) =
        (planeCurveFunction f 1) ^ n - 1 := by
    simp [P]
  rw [hmap,
    finrank_planeCurveFunctionField_over_secondRatFunc_eq_degreeOf_first
      hf hpartialFirst,
    show P.natDegree = n by
      simpa [P] using (Polynomial.natDegree_X_pow_sub_C
        (R := K) (n := n) (r := 1))]
    at hheight
  exact hheight

end

end BGS.CorvajaZannier
