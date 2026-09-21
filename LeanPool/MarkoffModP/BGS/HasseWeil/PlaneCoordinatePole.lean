/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.CorvajaZannier.PlaneCurvePoweredHeightBounds
import LeanPool.MarkoffModP.BGS.HasseWeil.FiniteExtensionZeroCounting
import LeanPool.MarkoffModP.BGS.HasseWeil.PoleDivisor
import Mathlib.Tactic

/-!
# A controlled pole place for the first plane coordinate

In the first-coordinate rational-function model of an irreducible plane
curve, the pole divisor of the first coordinate has degree exactly the degree
of the defining polynomial in the second variable.  Consequently that pole
divisor has nonempty support, and one can choose a pole place whose (possibly
nontrivial) place degree is bounded by that second-variable degree.

No rationality assertion is made about the selected place.
-/

namespace BGS.HasseWeil

open BGS.CorvajaZannier
open scoped nonZeroDivisors Polynomial BigOperators

noncomputable section

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
  [DecidableEq (RatFunc K)]

/-- In the first-coordinate `RatFunc` model, the pole height of the first
coordinate is the degree of the plane equation in the second variable. -/
theorem finiteExtensionHeight_planeCurveFirstCoordinate
    {f : MvPolynomial (Fin 2) K} (hf : Irreducible f)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0) :
    letI := planeCurveCoordinateRing_isDomain hf
    let hx := firstCoordinate_transcendental hf
      (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
    letI := planeCurveFirstCoordinateRatFuncAlgebra f hx
    letI := finiteDimensional_planeCurveFunctionField_over_ratFunc
      hf hpartialSecond
    letI := separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
    finiteExtensionHeight K (PlaneCurveFunctionField f)
        (planeCurveFunction f 0) =
      MvPolynomial.degreeOf 1 f := by
  letI : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let hx := firstCoordinate_transcendental hf
    (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
  let L := PlaneCurveFunctionField f
  let x : L := planeCurveFunction f 0
  letI : Algebra (RatFunc K) L :=
    planeCurveFirstCoordinateRatFuncAlgebra f hx
  letI : FiniteDimensional (RatFunc K) L :=
    finiteDimensional_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  letI : Algebra.IsSeparable (RatFunc K) L :=
    separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  have hx0 : x ≠ 0 := by
    change planeCurveFunction f 0 ≠ 0
    intro hzero
    apply hx
    rw [hzero]
    exact isAlgebraic_zero
  calc
    finiteExtensionHeight K L x =
        finiteExtensionPositiveDegree K L x :=
      (finiteExtensionPositiveDegree_eq_height K L x hx0).symm
    _ = MvPolynomial.degreeOf 1 f := by
      have hpositive :=
        finiteExtensionPositiveDegree_planeCurveFirstCoordinate_pow
          hf hpartialSecond 1 (by omega)
      simpa only [x, pow_one, one_mul] using hpositive

/-- Equivalently, the effective pole divisor of the first coordinate has
degree equal to the degree of the plane equation in the second variable. -/
theorem finiteExtensionDivisorDegree_planeCurveFirstCoordinate_poleDivisor
    {f : MvPolynomial (Fin 2) K} (hf : Irreducible f)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0) :
    letI := planeCurveCoordinateRing_isDomain hf
    let hx := firstCoordinate_transcendental hf
      (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
    letI := planeCurveFirstCoordinateRatFuncAlgebra f hx
    letI := finiteDimensional_planeCurveFunctionField_over_ratFunc
      hf hpartialSecond
    letI := separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
    finiteExtensionDivisorDegree K (PlaneCurveFunctionField f)
        (finiteExtensionPoleDivisor K (PlaneCurveFunctionField f)
          (planeCurveFunction f 0)) =
      (MvPolynomial.degreeOf 1 f : ℤ) := by
  letI : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let hx := firstCoordinate_transcendental hf
    (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
  let L := PlaneCurveFunctionField f
  let x : L := planeCurveFunction f 0
  letI : Algebra (RatFunc K) L :=
    planeCurveFirstCoordinateRatFuncAlgebra f hx
  letI : FiniteDimensional (RatFunc K) L :=
    finiteDimensional_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  letI : Algebra.IsSeparable (RatFunc K) L :=
    separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  change finiteExtensionDivisorDegree K L
      (finiteExtensionPoleDivisor K L x) =
    (MvPolynomial.degreeOf 1 f : ℤ)
  rw [finiteExtensionDivisorDegree_poleDivisor,
    finiteExtensionHeight_planeCurveFirstCoordinate hf hpartialSecond]

/-- A positive coefficient of an effective divisor contributes at least the
degree of its place to the total divisor degree. -/
theorem finiteExtensionPlaceDegree_le_divisorDegree_of_effective_of_pos
    (L : Type*) [Field L] [Algebra (RatFunc K) L]
    [FiniteDimensional (RatFunc K) L]
    [Algebra.IsSeparable (RatFunc K) L]
    (D : FiniteExtensionDivisor K L)
    (hD : ∀ v, 0 ≤ D v) {P : FiniteExtensionPlace K L}
    (hP : 0 < D P) :
    (finiteExtensionPlaceDegree K L P : ℤ) ≤
      finiteExtensionDivisorDegree K L D := by
  classical
  rw [finiteExtensionDivisorDegree, Finsupp.sum]
  have hPmem : P ∈ D.support :=
    Finsupp.mem_support_iff.mpr hP.ne'
  calc
    (finiteExtensionPlaceDegree K L P : ℤ) ≤
        D P * (finiteExtensionPlaceDegree K L P : ℤ) := by
      have hcoefficient : (1 : ℤ) ≤ D P := by omega
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hcoefficient
          (show 0 ≤ (finiteExtensionPlaceDegree K L P : ℤ) by positivity)
    _ ≤ ∑ v ∈ D.support,
        D v * (finiteExtensionPlaceDegree K L v : ℤ) := by
      exact Finset.single_le_sum
        (fun v _hv => mul_nonneg (hD v) (by positivity)) hPmem

/-- The first-coordinate pole divisor has nonempty support. -/
theorem planeCurveFirstCoordinate_poleDivisor_support_nonempty
    {f : MvPolynomial (Fin 2) K} (hf : Irreducible f)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0) :
    letI := planeCurveCoordinateRing_isDomain hf
    let hx := firstCoordinate_transcendental hf
      (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
    letI := planeCurveFirstCoordinateRatFuncAlgebra f hx
    letI := finiteDimensional_planeCurveFunctionField_over_ratFunc
      hf hpartialSecond
    letI := separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
    (finiteExtensionPoleDivisor K (PlaneCurveFunctionField f)
      (planeCurveFunction f 0)).support.Nonempty := by
  letI : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let hx := firstCoordinate_transcendental hf
    (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
  let L := PlaneCurveFunctionField f
  let x : L := planeCurveFunction f 0
  letI : Algebra (RatFunc K) L :=
    planeCurveFirstCoordinateRatFuncAlgebra f hx
  letI : FiniteDimensional (RatFunc K) L :=
    finiteDimensional_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  letI : Algebra.IsSeparable (RatFunc K) L :=
    separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  change (finiteExtensionPoleDivisor K L x).support.Nonempty
  apply Finsupp.support_nonempty_iff.mpr
  intro hzero
  have hdegree :=
    finiteExtensionDivisorDegree_planeCurveFirstCoordinate_poleDivisor
      hf hpartialSecond
  change finiteExtensionDivisorDegree K L
      (finiteExtensionPoleDivisor K L x) =
    (MvPolynomial.degreeOf 1 f : ℤ) at hdegree
  rw [hzero] at hdegree
  simp only [finiteExtensionDivisorDegree, Finsupp.sum_zero_index] at hdegree
  have hpositive : 0 < MvPolynomial.degreeOf 1 f :=
    degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond
  omega

/-- There is a pole place for the first coordinate.  Its coefficient in the
pole divisor is positive, and its (not necessarily one) place degree lies
between one and the degree of the plane equation in the second variable. -/
theorem exists_planeCurveFirstCoordinate_polePlace
    {f : MvPolynomial (Fin 2) K} (hf : Irreducible f)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0) :
    letI := planeCurveCoordinateRing_isDomain hf
    let hx := firstCoordinate_transcendental hf
      (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
    letI := planeCurveFirstCoordinateRatFuncAlgebra f hx
    letI := finiteDimensional_planeCurveFunctionField_over_ratFunc
      hf hpartialSecond
    letI := separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
    ∃ P : FiniteExtensionPlace K (PlaneCurveFunctionField f),
      0 < finiteExtensionPoleDivisor K (PlaneCurveFunctionField f)
          (planeCurveFunction f 0) P ∧
        0 < finiteExtensionPlaceDegree K (PlaneCurveFunctionField f) P ∧
        finiteExtensionPlaceDegree K (PlaneCurveFunctionField f) P ≤
          MvPolynomial.degreeOf 1 f := by
  letI : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let hx := firstCoordinate_transcendental hf
    (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
  let L := PlaneCurveFunctionField f
  let x : L := planeCurveFunction f 0
  letI : Algebra (RatFunc K) L :=
    planeCurveFirstCoordinateRatFuncAlgebra f hx
  letI : FiniteDimensional (RatFunc K) L :=
    finiteDimensional_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  letI : Algebra.IsSeparable (RatFunc K) L :=
    separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  obtain ⟨P, hPsupport⟩ :=
    planeCurveFirstCoordinate_poleDivisor_support_nonempty
      hf hpartialSecond
  have hPcoefficient :
      0 < finiteExtensionPoleDivisor K L x P := by
    exact lt_of_le_of_ne
      (finiteExtensionPoleDivisor_effective K L x P)
      (Finsupp.mem_support_iff.mp hPsupport).symm
  have hPdegreePositive : 0 < finiteExtensionPlaceDegree K L P :=
    finiteExtensionPlaceDegree_pos K L P
  have hPdegreeCast :
      (finiteExtensionPlaceDegree K L P : ℤ) ≤
        (MvPolynomial.degreeOf 1 f : ℤ) := by
    rw [← finiteExtensionDivisorDegree_planeCurveFirstCoordinate_poleDivisor
      hf hpartialSecond]
    exact finiteExtensionPlaceDegree_le_divisorDegree_of_effective_of_pos
      (K := K) L (finiteExtensionPoleDivisor K L x)
        (finiteExtensionPoleDivisor_effective K L x) hPcoefficient
  refine ⟨P, hPcoefficient, hPdegreePositive, ?_⟩
  exact_mod_cast hPdegreeCast

end

end BGS.HasseWeil
