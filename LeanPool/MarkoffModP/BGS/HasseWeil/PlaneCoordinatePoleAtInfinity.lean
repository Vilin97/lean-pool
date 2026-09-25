/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.HasseWeil.PlaneCoordinatePole

/-!
# The first plane coordinate only has poles above infinity

The first-coordinate rational-function model sends `RatFunc.X` to the first
plane coordinate.  At a finite place, `Polynomial.X` lies in the finite
integral closure, so its order is nonnegative.  Thus the effective pole
divisor of the first coordinate vanishes at every finite place.

Combining this support statement with the previously constructed controlled
pole place shows that the selected pole may be taken above the rational-
function place at infinity, without changing its place-degree bound.
-/

@[expose] public section

namespace BGS.HasseWeil

open BGS.CorvajaZannier
open IsDedekindDomain
open scoped nonZeroDivisors Polynomial BigOperators

noncomputable section

attribute [local instance] FractionRing.liftAlgebra
  FractionRing.isScalarTower_liftAlgebra

variable (K : Type*) [Field K] [Fintype K] [DecidableEq K]
  [DecidableEq (RatFunc K)]
variable (L : Type*) [Field L] [Algebra (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L]

local instance (priority := 10) coordinatePolePolynomialAlgebra :
    Algebra K[X] L :=
  RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
    (algebraMap K[X] (RatFunc K)))

local instance coordinatePolePolynomialScalarTower :
    IsScalarTower K[X] (RatFunc K) L :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance coordinatePoleFiniteIntegralClosureModuleFinite :
    Module.Finite K[X] (RatFuncFiniteIntegralClosure K L) :=
  Module.IsNoetherian.finite K[X] (RatFuncFiniteIntegralClosure K L)

local instance coordinatePoleFiniteIntegralClosureIsIntegral :
    Algebra.IsIntegral K[X] (RatFuncFiniteIntegralClosure K L) :=
  IsIntegralClosure.isIntegral_algebra K[X] L

local instance coordinatePolePolynomialTorsionFreeTop :
    Module.IsTorsionFree K[X] L :=
  Module.IsTorsionFree.trans_faithfulSMul K[X] (RatFunc K) L

local instance coordinatePoleFiniteIntegralClosureIsTorsionFree :
    Module.IsTorsionFree K[X] (RatFuncFiniteIntegralClosure K L) :=
  IsIntegralClosure.isTorsionFree K[X] L

local instance coordinatePoleInfinityIntegralClosureModuleFinite :
    Module.Finite (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L) :=
  IsIntegralClosure.finite (RatFuncInfinityIntegers K) (RatFunc K) L
    (RatFuncInfinityIntegralClosure K L)

local instance coordinatePoleInfinityIntegralClosureIsIntegral :
    Algebra.IsIntegral (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L) :=
  IsIntegralClosure.isIntegral_algebra (RatFuncInfinityIntegers K) L

local instance coordinatePoleInfinityBaseTorsionFreeTop :
    Module.IsTorsionFree (RatFuncInfinityIntegers K) L :=
  Module.IsTorsionFree.trans_faithfulSMul
    (RatFuncInfinityIntegers K) (RatFunc K) L

local instance coordinatePoleInfinityIntegralClosureIsTorsionFree :
    Module.IsTorsionFree (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L) :=
  IsIntegralClosure.isTorsionFree (RatFuncInfinityIntegers K) L

local instance coordinatePoleInfinityIntegralClosureIsDedekindDomain :
    IsDedekindDomain (RatFuncInfinityIntegralClosure K L) :=
  IsIntegralClosure.isDedekindDomain
    (RatFuncInfinityIntegers K) (RatFunc K) L
      (RatFuncInfinityIntegralClosure K L)

local instance coordinatePoleInfinityIntegralClosureIsFractionRing :
    IsFractionRing (RatFuncInfinityIntegralClosure K L) L :=
  IsIntegralClosure.isFractionRing_of_finite_extension
    (RatFuncInfinityIntegers K) (RatFunc K) L
      (RatFuncInfinityIntegralClosure K L)

omit [Fintype K] in
private theorem principalDivisor_algebraMap_X_inl_nonnegative
    (q : FiniteExtensionFinitePlace K L) :
    0 ≤ finiteExtensionPrincipalDivisor K L
      (algebraMap (RatFunc K) L RatFunc.X) (.inl q) := by
  let S := RatFuncFiniteIntegralClosure K L
  let e := ratFuncFiniteIntegralClosureFractionRingEquiv K L
  let s : S := algebraMap K[X] S Polynomial.X
  have hs : s ≠ 0 := by
    have hinj : Function.Injective (algebraMap K[X] S) :=
      FunctionField.ringOfIntegers.algebraMap_injective K L
    dsimp only [s]
    exact (map_ne_zero_iff (algebraMap K[X] S) hinj).2 Polynomial.X_ne_zero
  have hrepr :
      e.symm (algebraMap (RatFunc K) L RatFunc.X) =
        algebraMap S (FractionRing S) s := by
    apply e.injective
    rw [e.apply_symm_apply, e.commutes]
    rfl
  rw [finiteExtensionPrincipalDivisor_inl, hrepr]
  exact finitePlaceOrder_algebraMap_nonnegative q s hs

omit [Fintype K] in
/-- At every place above the rational-function place at infinity, the image
of `RatFunc.X` has strictly negative order.  This is stronger than merely
knowing that some infinity place is a pole: it makes the pole divisor of the
first coordinate cofinal among divisors supported at infinity. -/
theorem finiteExtensionPrincipalDivisor_algebraMap_X_inr_negative
    (P : FiniteExtensionInfinityPlace K L) :
    finiteExtensionPrincipalDivisor K L
      (algebraMap (RatFunc K) L RatFunc.X) (.inr P) < 0 := by
  let q := primeOverHeightOne (ratFuncInfinityPlace K) P
  let pi := ratFuncInfinityUniformizer K
  have hpiBase : pi ∈ (ratFuncInfinityPlace K).asIdeal := by
    rw [ratFuncInfinityPlace_span_uniformizer]
    exact Ideal.mem_span_singleton_self pi
  have hpiP : algebraMap (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L) pi ∈ P.1 := by
    have hover : (ratFuncInfinityPlace K).asIdeal = Ideal.comap
        (algebraMap (RatFuncInfinityIntegers K)
          (RatFuncInfinityIntegralClosure K L)) P.1 := by
      exact Ideal.over_def P.1 (ratFuncInfinityPlace K).asIdeal
    exact Ideal.mem_comap.mp (hover ▸ hpiBase)
  have hpiLt : q.valuation L
      (algebraMap (RatFuncInfinityIntegers K)
        (RatFuncInfinityIntegralClosure K L) pi) < 1 :=
    (q.valuation_lt_one_iff_mem
      (algebraMap (RatFuncInfinityIntegers K)
        (RatFuncInfinityIntegralClosure K L) pi)).mpr hpiP
  have hpiImage : algebraMap
      (RatFuncInfinityIntegralClosure K L) L
        (algebraMap (RatFuncInfinityIntegers K)
          (RatFuncInfinityIntegralClosure K L) pi) =
        (algebraMap (RatFunc K) L RatFunc.X)⁻¹ := by
    change algebraMap (RatFunc K) L (1 / RatFunc.X) =
      (algebraMap (RatFunc K) L RatFunc.X)⁻¹
    simp
  have hxinverse : q.valuation L
      (algebraMap (RatFunc K) L RatFunc.X)⁻¹ < 1 := by
    rw [← hpiImage]
    exact hpiLt
  have hX0 : algebraMap (RatFunc K) L RatFunc.X ≠ 0 := by
    simpa using (algebraMap (RatFunc K) L).injective.ne RatFunc.X_ne_zero
  have hXgt : 1 < q.valuation L
      (algebraMap (RatFunc K) L RatFunc.X) :=
    ((q.valuation L).one_lt_val_iff hX0).mpr hxinverse
  have horder := valuation_eq_exp_neg_finitePlaceOrder q
    (algebraMap (RatFunc K) L RatFunc.X) hX0
  rw [horder, ← WithZero.exp_zero, WithZero.exp_lt_exp] at hXgt
  have hnegative : finitePlaceOrder q
      (algebraMap (RatFunc K) L RatFunc.X) < 0 := by
    omega
  have hord := fractionRingAlgEquiv_finitePlaceOrder_eq
    (L := L) q
    ((ratFuncInfinityIntegralClosureFractionRingEquiv K L).symm
      (algebraMap (RatFunc K) L RatFunc.X))
  have hord' : finitePlaceOrder q
      (algebraMap (RatFunc K) L RatFunc.X) =
      finitePlaceOrder q
        ((ratFuncInfinityIntegralClosureFractionRingEquiv K L).symm
          (algebraMap (RatFunc K) L RatFunc.X)) := by
    simpa [ratFuncInfinityIntegralClosureFractionRingEquiv] using hord
  rw [finiteExtensionPrincipalDivisor_inr, ← hord']
  exact hnegative

variable {K}

omit [Fintype K] in
/-- The first plane coordinate has nonnegative principal-divisor order at
every finite place in its rational-function model. -/
theorem finiteExtensionPrincipalDivisor_planeCurveFirstCoordinate_inl_nonnegative
    {f : MvPolynomial (Fin 2) K} (hf : Irreducible f)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0) :
    letI := planeCurveCoordinateRing_isDomain hf
    let hx := firstCoordinate_transcendental hf
      (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
    letI := planeCurveFirstCoordinateRatFuncAlgebra f hx
    letI := finiteDimensional_planeCurveFunctionField_over_ratFunc
      hf hpartialSecond
    letI := separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
    ∀ q : FiniteExtensionFinitePlace K (PlaneCurveFunctionField f),
      0 ≤ finiteExtensionPrincipalDivisor K (PlaneCurveFunctionField f)
        (planeCurveFunction f 0) (.inl q) := by
  let : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let hx := firstCoordinate_transcendental hf
    (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
  let L := PlaneCurveFunctionField f
  let x : L := planeCurveFunction f 0
  let : Algebra (RatFunc K) L :=
    planeCurveFirstCoordinateRatFuncAlgebra f hx
  let : FiniteDimensional (RatFunc K) L :=
    finiteDimensional_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  let : Algebra.IsSeparable (RatFunc K) L :=
    separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  change ∀ q : FiniteExtensionFinitePlace K L,
    0 ≤ finiteExtensionPrincipalDivisor K L x (.inl q)
  intro q
  dsimp only [x]
  rw [← planeCurveFirstCoordinateRatFuncAlgebra_X f hx]
  exact principalDivisor_algebraMap_X_inl_nonnegative K L q

/-- Consequently, the pole divisor of the first plane coordinate vanishes at
every finite place. -/
theorem finiteExtensionPoleDivisor_planeCurveFirstCoordinate_inl_eq_zero
    {f : MvPolynomial (Fin 2) K} (hf : Irreducible f)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0) :
    letI := planeCurveCoordinateRing_isDomain hf
    let hx := firstCoordinate_transcendental hf
      (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
    letI := planeCurveFirstCoordinateRatFuncAlgebra f hx
    letI := finiteDimensional_planeCurveFunctionField_over_ratFunc
      hf hpartialSecond
    letI := separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
    ∀ q : FiniteExtensionFinitePlace K (PlaneCurveFunctionField f),
      finiteExtensionPoleDivisor K (PlaneCurveFunctionField f)
        (planeCurveFunction f 0) (.inl q) = 0 := by
  let : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let hx := firstCoordinate_transcendental hf
    (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
  let L := PlaneCurveFunctionField f
  let x : L := planeCurveFunction f 0
  let : Algebra (RatFunc K) L :=
    planeCurveFirstCoordinateRatFuncAlgebra f hx
  let : FiniteDimensional (RatFunc K) L :=
    finiteDimensional_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  let : Algebra.IsSeparable (RatFunc K) L :=
    separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  change ∀ q : FiniteExtensionFinitePlace K L,
    finiteExtensionPoleDivisor K L x (.inl q) = 0
  intro q
  rw [finiteExtensionPoleDivisor_apply]
  rw [ite_eq_right (not_lt_of_ge
    (finiteExtensionPrincipalDivisor_planeCurveFirstCoordinate_inl_nonnegative
      hf hpartialSecond q))]

/-- Every place above infinity occurs with positive coefficient in the pole
divisor of the first plane coordinate. -/
theorem finiteExtensionPoleDivisor_planeCurveFirstCoordinate_inr_positive
    {f : MvPolynomial (Fin 2) K} (hf : Irreducible f)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0) :
    letI := planeCurveCoordinateRing_isDomain hf
    let hx := firstCoordinate_transcendental hf
      (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
    letI := planeCurveFirstCoordinateRatFuncAlgebra f hx
    letI := finiteDimensional_planeCurveFunctionField_over_ratFunc
      hf hpartialSecond
    letI := separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
    ∀ P : FiniteExtensionInfinityPlace K (PlaneCurveFunctionField f),
      0 < finiteExtensionPoleDivisor K (PlaneCurveFunctionField f)
        (planeCurveFunction f 0) (.inr P) := by
  let : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let hx := firstCoordinate_transcendental hf
    (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
  let L := PlaneCurveFunctionField f
  let x : L := planeCurveFunction f 0
  let : Algebra (RatFunc K) L :=
    planeCurveFirstCoordinateRatFuncAlgebra f hx
  let : FiniteDimensional (RatFunc K) L :=
    finiteDimensional_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  let : Algebra.IsSeparable (RatFunc K) L :=
    separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  change ∀ P : FiniteExtensionInfinityPlace K L,
    0 < finiteExtensionPoleDivisor K L x (.inr P)
  intro P
  have hnegative : finiteExtensionPrincipalDivisor K L x (.inr P) < 0 := by
    have hmapX : algebraMap (RatFunc K) L RatFunc.X = x := by
      dsimp only [x]
      exact planeCurveFirstCoordinateRatFuncAlgebra_X f hx
    rw [← hmapX]
    exact finiteExtensionPrincipalDivisor_algebraMap_X_inr_negative K L P
  rw [finiteExtensionPoleDivisor_apply, ite_eq_left hnegative]
  omega

/-- The controlled pole place for the first plane coordinate lies above the
rational-function place at infinity.  Its positive pole coefficient and
place-degree bound are the same as in `exists_planeCurveFirstCoordinate_polePlace`. -/
theorem exists_planeCurveFirstCoordinate_infinityPolePlace
    {f : MvPolynomial (Fin 2) K} (hf : Irreducible f)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0) :
    letI := planeCurveCoordinateRing_isDomain hf
    let hx := firstCoordinate_transcendental hf
      (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
    letI := planeCurveFirstCoordinateRatFuncAlgebra f hx
    letI := finiteDimensional_planeCurveFunctionField_over_ratFunc
      hf hpartialSecond
    letI := separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
    ∃ P : FiniteExtensionInfinityPlace K (PlaneCurveFunctionField f),
      0 < finiteExtensionPoleDivisor K (PlaneCurveFunctionField f)
          (planeCurveFunction f 0) (.inr P) ∧
        0 < finiteExtensionPlaceDegree K (PlaneCurveFunctionField f) (.inr P) ∧
        finiteExtensionPlaceDegree K (PlaneCurveFunctionField f) (.inr P) ≤
          MvPolynomial.degreeOf 1 f := by
  let : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let hx := firstCoordinate_transcendental hf
    (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
  let L := PlaneCurveFunctionField f
  let x : L := planeCurveFunction f 0
  let : Algebra (RatFunc K) L :=
    planeCurveFirstCoordinateRatFuncAlgebra f hx
  let : FiniteDimensional (RatFunc K) L :=
    finiteDimensional_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  let : Algebra.IsSeparable (RatFunc K) L :=
    separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  change ∃ P : FiniteExtensionInfinityPlace K L,
    0 < finiteExtensionPoleDivisor K L x (.inr P) ∧
      0 < finiteExtensionPlaceDegree K L (.inr P) ∧
      finiteExtensionPlaceDegree K L (.inr P) ≤ MvPolynomial.degreeOf 1 f
  obtain ⟨P, hPpole, hPdegreePositive, hPdegreeBound⟩ :=
    exists_planeCurveFirstCoordinate_polePlace hf hpartialSecond
  cases P with
  | inl q =>
      have hzero :=
        finiteExtensionPoleDivisor_planeCurveFirstCoordinate_inl_eq_zero
          hf hpartialSecond q
      rw [hzero] at hPpole
      omega
  | inr P =>
      exact ⟨P, hPpole, hPdegreePositive, hPdegreeBound⟩

end

end BGS.HasseWeil
