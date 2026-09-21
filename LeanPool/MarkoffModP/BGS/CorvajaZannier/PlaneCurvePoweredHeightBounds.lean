/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.CorvajaZannier.FiniteExtensionPositiveDegreePower
import LeanPool.MarkoffModP.BGS.CorvajaZannier.FiniteExtensionOneSubGcdHeight
import LeanPool.MarkoffModP.BGS.CorvajaZannier.PlaneCurveBoundarySupport
import Mathlib.Tactic

/-!
# Powered coordinate heights in the first-coordinate place model

The canonical place summation uses the first-coordinate `RatFunc` model.
This module records the exact first-coordinate height and the transported
upper bound for the second-coordinate height, including positive powers.
-/

namespace BGS.CorvajaZannier

noncomputable section

open scoped Polynomial

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
  [DecidableEq (RatFunc K)]

/-- In the first-coordinate place model, `x^m` has its expected exact
positive divisor degree. -/
theorem finiteExtensionPositiveDegree_planeCurveFirstCoordinate_pow
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
        ((planeCurveFunction f 0) ^ m) =
      m * MvPolynomial.degreeOf 1 f := by
  letI : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let hx := firstCoordinate_transcendental hf
    (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
  let L := PlaneCurveFunctionField f
  let x : L := planeCurveFunction f 0
  have hx0 : x ≠ 0 := by
    change planeCurveFunction f 0 ≠ 0
    intro h
    apply hx
    rw [h]
    exact isAlgebraic_zero
  letI : Algebra (RatFunc K) L :=
    planeCurveFirstCoordinateRatFuncAlgebra f hx
  letI : FiniteDimensional (RatFunc K) L :=
    finiteDimensional_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  letI : Algebra.IsSeparable (RatFunc K) L :=
    separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  change finiteExtensionPositiveDegree K L (x ^ m) =
    m * MvPolynomial.degreeOf 1 f
  have hxDegree : finiteExtensionPositiveDegree K L x =
      MvPolynomial.degreeOf 1 f := by
    have hheight := finiteExtensionPositiveDegree_polynomial
      K L Polynomial.X Polynomial.X_ne_zero
    have hmap : algebraMap (RatFunc K) L
        (algebraMap K[X] (RatFunc K) Polynomial.X) = x := by
      change ratFuncSpecialization x hx RatFunc.X = x
      exact planeCurveFirstCoordinateRatFuncAlgebra_X f hx
    rw [hmap,
      finrank_planeCurveFunctionField_over_ratFunc_eq_degreeOf_second
        hf hpartialSecond] at hheight
    simpa using hheight
  rw [finiteExtensionPositiveDegree_pow K L x hx0 m, hxDegree]

/-- In the same first-coordinate place model, the transported second
coordinate power has height at most `n * degreeOf 0 f`. -/
theorem finiteExtensionPositiveDegree_planeCurveSecondCoordinate_pow_le
    {f : MvPolynomial (Fin 2) K} (hf : Irreducible f)
    (hpartialFirst : MvPolynomial.pderiv 0 f ≠ 0)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    (n : ℕ) :
    letI := planeCurveCoordinateRing_isDomain hf
    let hx := firstCoordinate_transcendental hf
      (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
    letI := planeCurveFirstCoordinateRatFuncAlgebra f hx
    letI := finiteDimensional_planeCurveFunctionField_over_ratFunc
      hf hpartialSecond
    letI := separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
    finiteExtensionPositiveDegree K (PlaneCurveFunctionField f)
        ((planeCurveFunction f 1) ^ n) ≤
      n * MvPolynomial.degreeOf 0 f := by
  letI : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let hx := firstCoordinate_transcendental hf
    (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
  let L := PlaneCurveFunctionField f
  let y : L := planeCurveFunction f 1
  have hyTrans : Transcendental K y :=
    secondCoordinate_transcendental hf
      (degreeOf_first_pos_of_pderiv_ne_zero hpartialFirst)
  have hy0 : y ≠ 0 := by
    intro h
    apply hyTrans
    rw [h]
    exact isAlgebraic_zero
  letI : Algebra (RatFunc K) L :=
    planeCurveFirstCoordinateRatFuncAlgebra f hx
  letI : FiniteDimensional (RatFunc K) L :=
    finiteDimensional_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  letI : Algebra.IsSeparable (RatFunc K) L :=
    separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  change finiteExtensionPositiveDegree K L (y ^ n) ≤
    n * MvPolynomial.degreeOf 0 f
  rw [finiteExtensionPositiveDegree_pow K L y hy0 n]
  exact Nat.mul_le_mul_left n
    (finiteExtensionPositiveDegree_planeCurveSecondCoordinate_le_degreeOf_first
      hf hpartialFirst hpartialSecond)

/-- The exhaustive gcd of `1-u` and `1-v` is bounded by the powered height
of `v`, and hence by its displayed plane-curve degree budget. -/
theorem finiteExtensionGcdWeightedDegree_one_sub_planeCurvePowers_le
    {f : MvPolynomial (Fin 2) K} (hf : Irreducible f)
    (hpartialFirst : MvPolynomial.pderiv 0 f ≠ 0)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    letI := planeCurveCoordinateRing_isDomain hf
    let hx := firstCoordinate_transcendental hf
      (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
    letI := planeCurveFirstCoordinateRatFuncAlgebra f hx
    letI := finiteDimensional_planeCurveFunctionField_over_ratFunc
      hf hpartialSecond
    letI := separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
    finiteExtensionGcdWeightedDegree K (PlaneCurveFunctionField f)
        (1 - (planeCurveFunction f 0) ^ m)
        (1 - (planeCurveFunction f 1) ^ n) ≤
      n * MvPolynomial.degreeOf 0 f := by
  letI : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let hx := firstCoordinate_transcendental hf
    (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
  let L := PlaneCurveFunctionField f
  let x : L := planeCurveFunction f 0
  let y : L := planeCurveFunction f 1
  have hxTrans : Transcendental K x := hx
  have hyTrans : Transcendental K y :=
    secondCoordinate_transcendental hf
      (degreeOf_first_pos_of_pderiv_ne_zero hpartialFirst)
  have hx0 : x ≠ 0 := by
    intro h
    apply hxTrans
    rw [h]
    exact isAlgebraic_zero
  have hy0 : y ≠ 0 := by
    intro h
    apply hyTrans
    rw [h]
    exact isAlgebraic_zero
  have hxmOne : x ^ m ≠ 1 := by
    intro h
    apply hxTrans.pow hm
    rw [h]
    exact isAlgebraic_one
  have hynOne : y ^ n ≠ 1 := by
    intro h
    apply hyTrans.pow hn
    rw [h]
    exact isAlgebraic_one
  letI : Algebra (RatFunc K) L :=
    planeCurveFirstCoordinateRatFuncAlgebra f hx
  letI : FiniteDimensional (RatFunc K) L :=
    finiteDimensional_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  letI : Algebra.IsSeparable (RatFunc K) L :=
    separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  change finiteExtensionGcdWeightedDegree K L (1 - x ^ m) (1 - y ^ n) ≤
    n * MvPolynomial.degreeOf 0 f
  have hgcd := finiteExtensionOneSubGcd_add_outsideHeight_le_positiveDegree_coordinate
    K L (x ^ m) (y ^ n) (pow_ne_zero _ hx0) (pow_ne_zero _ hy0)
      hxmOne hynOne
  have hv : finiteExtensionPositiveDegree K L (y ^ n) ≤
      n * MvPolynomial.degreeOf 0 f := by
    simpa only [L, y] using
      finiteExtensionPositiveDegree_planeCurveSecondCoordinate_pow_le
        hf hpartialFirst hpartialSecond n
  omega

/-- The exhaustive gcd degree is symmetric in its two arguments. -/
theorem finiteExtensionGcdWeightedDegree_comm
    {L : Type*} [Field L] [Algebra (RatFunc K) L]
    [FiniteDimensional (RatFunc K) L] [Algebra.IsSeparable (RatFunc K) L]
    (x y : L) :
    finiteExtensionGcdWeightedDegree K L x y =
      finiteExtensionGcdWeightedDegree K L y x := by
  classical
  unfold finiteExtensionGcdWeightedDegree finiteExtensionGcdMultiplicity
    finiteExtensionGcdSupport
  rw [Finset.union_comm]
  apply Finset.sum_congr rfl
  intro w _hw
  rw [min_comm]

/-- Simultaneously changing the signs of the two functions does not change
their exhaustive gcd divisor degree. -/
theorem finiteExtensionGcdWeightedDegree_neg_neg
    {L : Type*} [Field L] [Algebra (RatFunc K) L]
    [FiniteDimensional (RatFunc K) L] [Algebra.IsSeparable (RatFunc K) L]
    (x y : L) (hx : x ≠ 0) (hy : y ≠ 0) :
    finiteExtensionGcdWeightedDegree K L (-x) (-y) =
      finiteExtensionGcdWeightedDegree K L x y := by
  classical
  have hdivx : finiteExtensionPrincipalDivisor K L (-x) =
      finiteExtensionPrincipalDivisor K L x := by
    ext w
    exact finiteExtensionPrincipalDivisor_neg_apply K L x hx w
  have hdivy : finiteExtensionPrincipalDivisor K L (-y) =
      finiteExtensionPrincipalDivisor K L y := by
    ext w
    exact finiteExtensionPrincipalDivisor_neg_apply K L y hy w
  unfold finiteExtensionGcdWeightedDegree finiteExtensionGcdMultiplicity
    finiteExtensionGcdSupport
  rw [hdivx, hdivy]

/-- The torsion gcd used by the endpoint is exactly the `1-u`, `1-v` gcd
used by the canonical Wronskian estimate. -/
theorem planeCurveExhaustiveTorsionGcdWeightedDegree_eq_one_sub
    {f : MvPolynomial (Fin 2) K} (hf : Irreducible f)
    (hpartialFirst : MvPolynomial.pderiv 0 f ≠ 0)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    letI := planeCurveCoordinateRing_isDomain hf
    letI : DecidableEq (RatFunc K) := Classical.decEq _
    let hx := firstCoordinate_transcendental hf
      (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
    letI := planeCurveFirstCoordinateRatFuncAlgebra f hx
    letI := finiteDimensional_planeCurveFunctionField_over_ratFunc
      hf hpartialSecond
    letI := separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
    planeCurveExhaustiveTorsionGcdWeightedDegree
        hf hpartialSecond m n =
      finiteExtensionGcdWeightedDegree K (PlaneCurveFunctionField f)
        (1 - (planeCurveFunction f 0) ^ m)
        (1 - (planeCurveFunction f 1) ^ n) := by
  letI : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  letI : DecidableEq (RatFunc K) := Classical.decEq _
  let hx := firstCoordinate_transcendental hf
    (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
  let L := PlaneCurveFunctionField f
  let x : L := planeCurveFunction f 0
  let y : L := planeCurveFunction f 1
  have hxTrans : Transcendental K x := hx
  have hyTrans : Transcendental K y :=
    secondCoordinate_transcendental hf
      (degreeOf_first_pos_of_pderiv_ne_zero hpartialFirst)
  have hxm : 1 - x ^ m ≠ 0 := by
    apply sub_ne_zero.mpr
    intro h
    apply hxTrans.pow hm
    rw [← h]
    exact isAlgebraic_one
  have hyn : 1 - y ^ n ≠ 0 := by
    apply sub_ne_zero.mpr
    intro h
    apply hyTrans.pow hn
    rw [← h]
    exact isAlgebraic_one
  letI : Algebra (RatFunc K) L :=
    planeCurveFirstCoordinateRatFuncAlgebra f hx
  letI : FiniteDimensional (RatFunc K) L :=
    finiteDimensional_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  letI : Algebra.IsSeparable (RatFunc K) L :=
    separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  dsimp only [planeCurveExhaustiveTorsionGcdWeightedDegree]
  change finiteExtensionGcdWeightedDegree K L (x ^ m - 1) (y ^ n - 1) =
    finiteExtensionGcdWeightedDegree K L (1 - x ^ m) (1 - y ^ n)
  rw [show x ^ m - 1 = -(1 - x ^ m) by ring,
    show y ^ n - 1 = -(1 - y ^ n) by ring]
  exact finiteExtensionGcdWeightedDegree_neg_neg
    (K := K) (L := L) (1 - x ^ m) (1 - y ^ n) hxm hyn

/-- With the coordinates swapped, the one-minus gcd is bounded by the exact
powered height of the first coordinate. -/
theorem finiteExtensionGcdWeightedDegree_one_sub_planeCurvePowers_swapped_le
    {f : MvPolynomial (Fin 2) K} (hf : Irreducible f)
    (hpartialFirst : MvPolynomial.pderiv 0 f ≠ 0)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    letI := planeCurveCoordinateRing_isDomain hf
    let hx := firstCoordinate_transcendental hf
      (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
    letI := planeCurveFirstCoordinateRatFuncAlgebra f hx
    letI := finiteDimensional_planeCurveFunctionField_over_ratFunc
      hf hpartialSecond
    letI := separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
    finiteExtensionGcdWeightedDegree K (PlaneCurveFunctionField f)
        (1 - (planeCurveFunction f 1) ^ n)
        (1 - (planeCurveFunction f 0) ^ m) ≤
      m * MvPolynomial.degreeOf 1 f := by
  letI : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let hx := firstCoordinate_transcendental hf
    (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
  let L := PlaneCurveFunctionField f
  let x : L := planeCurveFunction f 0
  let y : L := planeCurveFunction f 1
  have hxTrans : Transcendental K x := hx
  have hyTrans : Transcendental K y :=
    secondCoordinate_transcendental hf
      (degreeOf_first_pos_of_pderiv_ne_zero hpartialFirst)
  have hx0 : x ≠ 0 := by
    intro h
    apply hxTrans
    rw [h]
    exact isAlgebraic_zero
  have hy0 : y ≠ 0 := by
    intro h
    apply hyTrans
    rw [h]
    exact isAlgebraic_zero
  have hxmOne : x ^ m ≠ 1 := by
    intro h
    apply hxTrans.pow hm
    rw [h]
    exact isAlgebraic_one
  have hynOne : y ^ n ≠ 1 := by
    intro h
    apply hyTrans.pow hn
    rw [h]
    exact isAlgebraic_one
  letI : Algebra (RatFunc K) L :=
    planeCurveFirstCoordinateRatFuncAlgebra f hx
  letI : FiniteDimensional (RatFunc K) L :=
    finiteDimensional_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  letI : Algebra.IsSeparable (RatFunc K) L :=
    separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  change finiteExtensionGcdWeightedDegree K L (1 - y ^ n) (1 - x ^ m) ≤
    m * MvPolynomial.degreeOf 1 f
  have hgcd := finiteExtensionOneSubGcd_add_outsideHeight_le_positiveDegree_coordinate
    K L (y ^ n) (x ^ m) (pow_ne_zero _ hy0) (pow_ne_zero _ hx0)
      hynOne hxmOne
  have hxPower : finiteExtensionPositiveDegree K L (x ^ m) =
      m * MvPolynomial.degreeOf 1 f := by
    simpa only [L, x] using
      finiteExtensionPositiveDegree_planeCurveFirstCoordinate_pow
        hf hpartialSecond m hm
  omega

end

end BGS.CorvajaZannier
