/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.CorvajaZannier.TorsionExhaustiveGcdDivisorBound

/-!
# Finite places centered at affine rational points

For an irreducible plane curve with both coordinates separating, this file
chooses an exhaustive finite place centered at each affine rational point.
Both coordinate differences have positive order at the selected place, and
distinct affine points give distinct places.

The construction records the affine center through equality of valuation
subrings.  It deliberately makes no residue-degree-one claim: above a
singular rational point, a chosen normalization branch need not be rational.
-/

open IsDedekindDomain
open Multiplicative WithZero

namespace BGS.HasseWeil

open BGS.CorvajaZannier

noncomputable section

variable {K : Type*} [Field K]
variable {f : MvPolynomial (Fin 2) K}

/-- The first coordinate minus its value at an affine point belongs to the
point's maximal ideal. -/
theorem firstCoordinate_sub_mem_affinePlaneCurvePointMaximalIdeal
    (z : AffinePlaneCurvePoint f) :
    planeCurveCoordinate f 0 -
        algebraMap K (PlaneCurveCoordinateRing f) z.1.1 ∈
      (affinePlaneCurvePointMaximalIdeal f z).asIdeal := by
  change planeCurvePointEval f z
    (planeCurveCoordinate f 0 -
      algebraMap K (PlaneCurveCoordinateRing f) z.1.1) = 0
  simp

/-- The second coordinate minus its value at an affine point belongs to the
point's maximal ideal. -/
theorem secondCoordinate_sub_mem_affinePlaneCurvePointMaximalIdeal
    (z : AffinePlaneCurvePoint f) :
    planeCurveCoordinate f 1 -
        algebraMap K (PlaneCurveCoordinateRing f) z.1.2 ∈
      (affinePlaneCurvePointMaximalIdeal f z).asIdeal := by
  change planeCurvePointEval f z
    (planeCurveCoordinate f 1 -
      algebraMap K (PlaneCurveCoordinateRing f) z.1.2) = 0
  simp

/-- A separating first coordinate cannot equal the constant first coordinate
of an affine point in the function field. -/
theorem firstCoordinate_sub_affinePoint_ne_zero
    (hf : Irreducible f)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    (z : AffinePlaneCurvePoint f) :
    letI := planeCurveCoordinateRing_isDomain hf
    planeCurveFunction f 0 -
        algebraMap K (PlaneCurveFunctionField f) z.1.1 ≠ 0 := by
  let : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  have htrans : Transcendental K (planeCurveFunction f 0) :=
    firstCoordinate_transcendental hf
      (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
  intro hzero
  apply htrans
  rw [sub_eq_zero.mp hzero]
  exact isAlgebraic_algebraMap z.1.1

/-- A separating second coordinate cannot equal the constant second
coordinate of an affine point in the function field. -/
theorem secondCoordinate_sub_affinePoint_ne_zero
    (hf : Irreducible f)
    (hpartialFirst : MvPolynomial.pderiv 0 f ≠ 0)
    (z : AffinePlaneCurvePoint f) :
    letI := planeCurveCoordinateRing_isDomain hf
    planeCurveFunction f 1 -
        algebraMap K (PlaneCurveFunctionField f) z.1.2 ≠ 0 := by
  let : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  have htrans : Transcendental K (planeCurveFunction f 1) :=
    secondCoordinate_transcendental hf
      (degreeOf_first_pos_of_pderiv_ne_zero hpartialFirst)
  intro hzero
  apply htrans
  rw [sub_eq_zero.mp hzero]
  exact isAlgebraic_algebraMap z.1.2

private theorem ratFuncSpecialization_X_sub_C
    {K E : Type*} [Field K] [Field E] [Algebra K E]
    (x : E) (hx : Transcendental K x) (c : K) :
    ratFuncSpecialization x hx
      (algebraMap (Polynomial K) (RatFunc K) (Polynomial.X - Polynomial.C c)) =
      x - algebraMap K E c := by
  have hcomp := congrArg
    (fun h : Polynomial K →+* E => h (Polynomial.X - Polynomial.C c))
    (ratFuncSpecialization_comp_polynomial_algebraMap x hx)
  simpa using hcomp

/-- Every affine rational point has an exhaustive finite place centered at
that point where both coordinate differences have positive order. -/
theorem exists_affinePoint_exhaustiveFinitePlace_orders_positive
    (hf : Irreducible f)
    (hpartialFirst : MvPolynomial.pderiv 0 f ≠ 0)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    (z : AffinePlaneCurvePoint f) :
    let := planeCurveCoordinateRing_isDomain hf
    let hx := firstCoordinate_transcendental hf
      (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
    let := planeCurveFirstCoordinateRatFuncAlgebra f hx
    let : Algebra (Polynomial K) (PlaneCurveFunctionField f) :=
      RingHom.toAlgebra
        ((algebraMap (RatFunc K) (PlaneCurveFunctionField f)).comp
          (algebraMap (Polynomial K) (RatFunc K)))
    let : IsScalarTower (Polynomial K) (RatFunc K)
        (PlaneCurveFunctionField f) :=
      IsScalarTower.of_algebraMap_eq' rfl
    let : FiniteDimensional (RatFunc K) (PlaneCurveFunctionField f) :=
      finiteDimensional_planeCurveFunctionField_over_ratFunc hf hpartialSecond
    let : Algebra.IsSeparable (RatFunc K) (PlaneCurveFunctionField f) :=
      separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
    let : IsDedekindDomain
        (integralClosure (Polynomial K) (PlaneCurveFunctionField f)) :=
      integralClosure.isDedekindDomain (Polynomial K) (RatFunc K)
        (PlaneCurveFunctionField f)
    let : IsFractionRing
        (integralClosure (Polynomial K) (PlaneCurveFunctionField f))
        (PlaneCurveFunctionField f) :=
      integralClosure.isFractionRing_of_finite_extension (RatFunc K)
        (PlaneCurveFunctionField f)
    ∃ q : HeightOneSpectrum
        (integralClosure (Polynomial K) (PlaneCurveFunctionField f)),
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime
          (PlaneCurveFunctionField f) q =
        dominatingValuationSubring
          (affinePlaneCurvePointMaximalIdeal f z) ∧
        0 < finitePlaceOrder q
          (planeCurveFunction f 0 -
            algebraMap K (PlaneCurveFunctionField f) z.1.1) ∧
        0 < finitePlaceOrder q
          (planeCurveFunction f 1 -
            algebraMap K (PlaneCurveFunctionField f) z.1.2) := by
  intro domain hx ratFuncAlgebra polynomialAlgebra scalarTower finiteDimension separable
    dedekind fraction
  let A := PlaneCurveCoordinateRing f
  let E := PlaneCurveFunctionField f
  let B := integralClosure (Polynomial K) E
  let m := affinePlaneCurvePointMaximalIdeal f z
  let hbase : ∀ P : Polynomial K,
      algebraMap (Polynomial K) E P ∈ (algebraMap A E).range :=
    polynomial_algebraMap_mem_planeCurveCoordinateRing_range hf hpartialSecond
  let rfirst : A := planeCurveCoordinate f 0 - algebraMap K A z.1.1
  let rsecond : A := planeCurveCoordinate f 1 - algebraMap K A z.1.2
  let Pfirst : Polynomial K := Polynomial.X - Polynomial.C z.1.1
  let bfirst : B := algebraMap (Polynomial K) B Pfirst
  have hfirstNonzero :
      planeCurveFunction f 0 - algebraMap K E z.1.1 ≠ 0 :=
    firstCoordinate_sub_affinePoint_ne_zero hf hpartialSecond z
  have hsecondNonzero :
      planeCurveFunction f 1 - algebraMap K E z.1.2 ≠ 0 :=
    secondCoordinate_sub_affinePoint_ne_zero hf hpartialFirst z
  have hrfirst : rfirst ∈ m.asIdeal :=
    firstCoordinate_sub_mem_affinePlaneCurvePointMaximalIdeal z
  have hrsecond : rsecond ∈ m.asIdeal :=
    secondCoordinate_sub_mem_affinePlaneCurvePointMaximalIdeal z
  have hrfirstMap : algebraMap A E rfirst =
      planeCurveFunction f 0 - algebraMap K E z.1.1 := by
    simp only [rfirst, map_sub]
    rfl
  have hrsecondMap : algebraMap A E rsecond =
      planeCurveFunction f 1 - algebraMap K E z.1.2 := by
    simp only [rsecond, map_sub]
    rfl
  have hPfirstMap : algebraMap (Polynomial K) E Pfirst =
      planeCurveFunction f 0 - algebraMap K E z.1.1 := by
    change ratFuncSpecialization (planeCurveFunction f 0) hx
      (algebraMap (Polynomial K) (RatFunc K) Pfirst) = _
    exact ratFuncSpecialization_X_sub_C (planeCurveFunction f 0) hx z.1.1
  have hbfirstMap : algebraMap B E bfirst =
      planeCurveFunction f 0 - algebraMap K E z.1.1 := by
    rw [show algebraMap B E bfirst =
      algebraMap (Polynomial K) E Pfirst by
        exact IsScalarTower.algebraMap_apply (Polynomial K) B E Pfirst]
    exact hPfirstMap
  have hrfirstMap0 : algebraMap A E rfirst ≠ 0 := by
    rwa [hrfirstMap]
  have hrsecondMap0 : algebraMap A E rsecond ≠ 0 := by
    rwa [hrsecondMap]
  have hb : algebraMap B E bfirst = algebraMap A E rfirst :=
    hbfirstMap.trans hrfirstMap.symm
  obtain ⟨q, hq, hfirst, hsecond⟩ := exists_integralClosurePlace_orders_positive
    m hbase rfirst rsecond hrfirst hrsecond hrfirstMap0 hrsecondMap0 bfirst hb
  exact ⟨q, hq, hrfirstMap ▸ hfirst, hrsecondMap ▸ hsecond⟩

variable [DecidableEq K]

/-- The exhaustive finite place selected above an affine rational point. -/
def affinePointExhaustiveFinitePlace
    (hf : Irreducible f)
    (hpartialFirst : MvPolynomial.pderiv 0 f ≠ 0)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    (z : AffinePlaneCurvePoint f) :
    letI := planeCurveCoordinateRing_isDomain hf
    let hx := firstCoordinate_transcendental hf
      (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
    letI := planeCurveFirstCoordinateRatFuncAlgebra f hx
    letI : Algebra (Polynomial K) (PlaneCurveFunctionField f) :=
      RingHom.toAlgebra
        ((algebraMap (RatFunc K) (PlaneCurveFunctionField f)).comp
          (algebraMap (Polynomial K) (RatFunc K)))
    letI : IsScalarTower (Polynomial K) (RatFunc K)
        (PlaneCurveFunctionField f) :=
      IsScalarTower.of_algebraMap_eq' rfl
    letI : FiniteDimensional (RatFunc K) (PlaneCurveFunctionField f) :=
      finiteDimensional_planeCurveFunctionField_over_ratFunc hf hpartialSecond
    letI : Algebra.IsSeparable (RatFunc K) (PlaneCurveFunctionField f) :=
      separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
    FiniteExtensionFinitePlace K (PlaneCurveFunctionField f) := by
  exact Classical.choose
    (exists_affinePoint_exhaustiveFinitePlace_orders_positive
      hf hpartialFirst hpartialSecond z)

omit [DecidableEq K] in
/-- The selected finite place has the prescribed affine center, and both
coordinate differences have positive order there. -/
theorem affinePointExhaustiveFinitePlace_spec
    (hf : Irreducible f)
    (hpartialFirst : MvPolynomial.pderiv 0 f ≠ 0)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    (z : AffinePlaneCurvePoint f) :
    letI := planeCurveCoordinateRing_isDomain hf
    let hx := firstCoordinate_transcendental hf
      (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
    letI := planeCurveFirstCoordinateRatFuncAlgebra f hx
    letI : Algebra (Polynomial K) (PlaneCurveFunctionField f) :=
      RingHom.toAlgebra
        ((algebraMap (RatFunc K) (PlaneCurveFunctionField f)).comp
          (algebraMap (Polynomial K) (RatFunc K)))
    letI : IsScalarTower (Polynomial K) (RatFunc K)
        (PlaneCurveFunctionField f) :=
      IsScalarTower.of_algebraMap_eq' rfl
    letI : FiniteDimensional (RatFunc K) (PlaneCurveFunctionField f) :=
      finiteDimensional_planeCurveFunctionField_over_ratFunc hf hpartialSecond
    letI : Algebra.IsSeparable (RatFunc K) (PlaneCurveFunctionField f) :=
      separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
    IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime
        (PlaneCurveFunctionField f)
        (affinePointExhaustiveFinitePlace
          hf hpartialFirst hpartialSecond z) =
      dominatingValuationSubring (affinePlaneCurvePointMaximalIdeal f z) ∧
      0 < finitePlaceOrder
        (affinePointExhaustiveFinitePlace
          hf hpartialFirst hpartialSecond z)
        (planeCurveFunction f 0 -
          algebraMap K (PlaneCurveFunctionField f) z.1.1) ∧
      0 < finitePlaceOrder
        (affinePointExhaustiveFinitePlace
          hf hpartialFirst hpartialSecond z)
        (planeCurveFunction f 1 -
          algebraMap K (PlaneCurveFunctionField f) z.1.2) := by
  exact Classical.choose_spec
    (exists_affinePoint_exhaustiveFinitePlace_orders_positive
      hf hpartialFirst hpartialSecond z)

omit [DecidableEq K] in
/-- Distinct affine rational points have distinct selected exhaustive finite
places.  The proof uses equality of affine centers, not residue degrees. -/
theorem affinePointExhaustiveFinitePlace_injective
    (hf : Irreducible f)
    (hpartialFirst : MvPolynomial.pderiv 0 f ≠ 0)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0) :
    letI := planeCurveCoordinateRing_isDomain hf
    let hx := firstCoordinate_transcendental hf
      (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
    letI := planeCurveFirstCoordinateRatFuncAlgebra f hx
    letI : Algebra (Polynomial K) (PlaneCurveFunctionField f) :=
      RingHom.toAlgebra
        ((algebraMap (RatFunc K) (PlaneCurveFunctionField f)).comp
          (algebraMap (Polynomial K) (RatFunc K)))
    letI : IsScalarTower (Polynomial K) (RatFunc K)
        (PlaneCurveFunctionField f) :=
      IsScalarTower.of_algebraMap_eq' rfl
    letI : FiniteDimensional (RatFunc K) (PlaneCurveFunctionField f) :=
      finiteDimensional_planeCurveFunctionField_over_ratFunc hf hpartialSecond
    letI : Algebra.IsSeparable (RatFunc K) (PlaneCurveFunctionField f) :=
      separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
    Function.Injective
      (affinePointExhaustiveFinitePlace
        hf hpartialFirst hpartialSecond) := by
  let : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let hx := firstCoordinate_transcendental hf
    (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
  let : Algebra (RatFunc K) (PlaneCurveFunctionField f) :=
    planeCurveFirstCoordinateRatFuncAlgebra f hx
  let : Algebra (Polynomial K) (PlaneCurveFunctionField f) :=
    RingHom.toAlgebra
      ((algebraMap (RatFunc K) (PlaneCurveFunctionField f)).comp
        (algebraMap (Polynomial K) (RatFunc K)))
  let : IsScalarTower (Polynomial K) (RatFunc K)
      (PlaneCurveFunctionField f) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : FiniteDimensional (RatFunc K) (PlaneCurveFunctionField f) :=
    finiteDimensional_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  let : Algebra.IsSeparable (RatFunc K) (PlaneCurveFunctionField f) :=
    separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  change Function.Injective
    (affinePointExhaustiveFinitePlace hf hpartialFirst hpartialSecond)
  intro z w hzw
  apply affinePlaneCurvePointMaximalIdeal_injective f
  apply MaximalSpectrum.ext
  apply pointIdeal_eq_of_dominatingValuationSubring_eq
    (A := PlaneCurveCoordinateRing f)
    (L := PlaneCurveFunctionField f)
  calc
    dominatingValuationSubring (affinePlaneCurvePointMaximalIdeal f z) =
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime
          (PlaneCurveFunctionField f)
          (affinePointExhaustiveFinitePlace
            hf hpartialFirst hpartialSecond z) :=
      (affinePointExhaustiveFinitePlace_spec
        hf hpartialFirst hpartialSecond z).1.symm
    _ = IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime
          (PlaneCurveFunctionField f)
          (affinePointExhaustiveFinitePlace
            hf hpartialFirst hpartialSecond w) := by
      rw [hzw]
    _ = dominatingValuationSubring
          (affinePlaneCurvePointMaximalIdeal f w) :=
      (affinePointExhaustiveFinitePlace_spec
        hf hpartialFirst hpartialSecond w).1

omit [DecidableEq K] in
/-- Any nonzero regular function vanishing at an affine point has positive
order at that point's selected finite place. -/
theorem finitePlaceOrder_affinePointExhaustiveFinitePlace_pos_of_mem
    (hf : Irreducible f)
    (hpartialFirst : MvPolynomial.pderiv 0 f ≠ 0)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    (z : AffinePlaneCurvePoint f)
    (r : PlaneCurveCoordinateRing f)
    (hr : r ∈ (affinePlaneCurvePointMaximalIdeal f z).asIdeal)
    (hr0 : algebraMap (PlaneCurveCoordinateRing f)
      (PlaneCurveFunctionField f) r ≠ 0) :
    letI := planeCurveCoordinateRing_isDomain hf
    let hx := firstCoordinate_transcendental hf
      (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
    letI := planeCurveFirstCoordinateRatFuncAlgebra f hx
    letI : Algebra (Polynomial K) (PlaneCurveFunctionField f) :=
      RingHom.toAlgebra
        ((algebraMap (RatFunc K) (PlaneCurveFunctionField f)).comp
          (algebraMap (Polynomial K) (RatFunc K)))
    letI : IsScalarTower (Polynomial K) (RatFunc K)
        (PlaneCurveFunctionField f) :=
      IsScalarTower.of_algebraMap_eq' rfl
    letI : FiniteDimensional (RatFunc K) (PlaneCurveFunctionField f) :=
      finiteDimensional_planeCurveFunctionField_over_ratFunc hf hpartialSecond
    letI : Algebra.IsSeparable (RatFunc K) (PlaneCurveFunctionField f) :=
      separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
    0 < finitePlaceOrder
      (affinePointExhaustiveFinitePlace
        hf hpartialFirst hpartialSecond z)
      (algebraMap (PlaneCurveCoordinateRing f)
        (PlaneCurveFunctionField f) r) := by
  let : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let hx := firstCoordinate_transcendental hf
    (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
  let : Algebra (RatFunc K) (PlaneCurveFunctionField f) :=
    planeCurveFirstCoordinateRatFuncAlgebra f hx
  let : Algebra (Polynomial K) (PlaneCurveFunctionField f) :=
    RingHom.toAlgebra
      ((algebraMap (RatFunc K) (PlaneCurveFunctionField f)).comp
        (algebraMap (Polynomial K) (RatFunc K)))
  let : IsScalarTower (Polynomial K) (RatFunc K)
      (PlaneCurveFunctionField f) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : FiniteDimensional (RatFunc K) (PlaneCurveFunctionField f) :=
    finiteDimensional_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  let : Algebra.IsSeparable (RatFunc K) (PlaneCurveFunctionField f) :=
    separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  let E := PlaneCurveFunctionField f
  let q := affinePointExhaustiveFinitePlace
    hf hpartialFirst hpartialSecond z
  let V := dominatingValuationSubring
    (A := PlaneCurveCoordinateRing f) (L := E)
    (affinePlaneCurvePointMaximalIdeal f z)
  have hnonunits :
      algebraMap (PlaneCurveCoordinateRing f) E r ∈ V.nonunits :=
    algebraMap_mem_dominatingValuationSubring_nonunits_of_mem
      (A := PlaneCurveCoordinateRing f)
      (L := E) (affinePlaneCurvePointMaximalIdeal f z) r hr
  have hVlt : V.valuation
      (algebraMap (PlaneCurveCoordinateRing f) E r) < 1 :=
    hnonunits
  have hequiv : (q.valuation E).IsEquiv V.valuation := by
    rw [Valuation.isEquiv_iff_valuationSubring,
      ← IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring,
      ValuationSubring.valuationSubring_valuation]
    exact (affinePointExhaustiveFinitePlace_spec
      hf hpartialFirst hpartialSecond z).1
  have hqlt : q.valuation E
      (algebraMap (PlaneCurveCoordinateRing f) E r) < 1 :=
    hequiv.lt_one_iff_lt_one.mpr hVlt
  have horder := valuation_eq_exp_neg_finitePlaceOrder q
    (algebraMap (PlaneCurveCoordinateRing f) E r) hr0
  rw [horder, ← exp_zero, exp_lt_exp] at hqlt
  have hpos : 0 < finitePlaceOrder q
      (algebraMap (PlaneCurveCoordinateRing f) E r) := by
    omega
  simpa [q, E] using hpos

/-- A finite family of distinct affine rational points at which two fixed
nonzero regular functions vanish is bounded by their degree-weighted positive
gcd divisor.  Positive place degree suffices; no selected place is asserted
to have degree one. -/
theorem affinePointFamily_card_le_finiteExtensionGcdWeightedDegree
    {ι : Type*} [Fintype ι]
    (hf : Irreducible f)
    (hpartialFirst : MvPolynomial.pderiv 0 f ≠ 0)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    (point : ι → AffinePlaneCurvePoint f)
    (hpoint : Function.Injective point)
    (r s : PlaneCurveCoordinateRing f)
    (hr : ∀ i, r ∈ (affinePlaneCurvePointMaximalIdeal f (point i)).asIdeal)
    (hs : ∀ i, s ∈ (affinePlaneCurvePointMaximalIdeal f (point i)).asIdeal)
    (hr0 : algebraMap (PlaneCurveCoordinateRing f)
      (PlaneCurveFunctionField f) r ≠ 0)
    (hs0 : algebraMap (PlaneCurveCoordinateRing f)
      (PlaneCurveFunctionField f) s ≠ 0) :
    letI := planeCurveCoordinateRing_isDomain hf
    letI : DecidableEq (RatFunc K) := Classical.decEq (RatFunc K)
    let hx := firstCoordinate_transcendental hf
      (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
    letI := planeCurveFirstCoordinateRatFuncAlgebra f hx
    letI : FiniteDimensional (RatFunc K) (PlaneCurveFunctionField f) :=
      finiteDimensional_planeCurveFunctionField_over_ratFunc hf hpartialSecond
    letI : Algebra.IsSeparable (RatFunc K) (PlaneCurveFunctionField f) :=
      separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
    Fintype.card ι ≤ finiteExtensionGcdWeightedDegree K
      (PlaneCurveFunctionField f)
      (algebraMap (PlaneCurveCoordinateRing f)
        (PlaneCurveFunctionField f) r)
      (algebraMap (PlaneCurveCoordinateRing f)
        (PlaneCurveFunctionField f) s) := by
  classical
  let : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let : DecidableEq (RatFunc K) := Classical.decEq (RatFunc K)
  let hx := firstCoordinate_transcendental hf
    (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
  let : Algebra (RatFunc K) (PlaneCurveFunctionField f) :=
    planeCurveFirstCoordinateRatFuncAlgebra f hx
  let : Algebra (Polynomial K) (PlaneCurveFunctionField f) :=
    RingHom.toAlgebra
      ((algebraMap (RatFunc K) (PlaneCurveFunctionField f)).comp
        (algebraMap (Polynomial K) (RatFunc K)))
  let : IsScalarTower (Polynomial K) (RatFunc K)
      (PlaneCurveFunctionField f) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : FiniteDimensional (RatFunc K) (PlaneCurveFunctionField f) :=
    finiteDimensional_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  let : Algebra.IsSeparable (RatFunc K) (PlaneCurveFunctionField f) :=
    separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  let E := PlaneCurveFunctionField f
  let x : E := algebraMap (PlaneCurveCoordinateRing f) E r
  let y : E := algebraMap (PlaneCurveCoordinateRing f) E s
  let finitePlace : ι → FiniteExtensionFinitePlace K E := fun i =>
    affinePointExhaustiveFinitePlace
      hf hpartialFirst hpartialSecond (point i)
  let _ : DecidableEq (FiniteExtensionPlace K E) := Classical.decEq _
  let place : ι → FiniteExtensionPlace K E := fun i => .inl (finitePlace i)
  have hFinitePlaceInjective : Function.Injective finitePlace :=
    (affinePointExhaustiveFinitePlace_injective
      hf hpartialFirst hpartialSecond).comp hpoint
  have hPlaceInjective : Function.Injective place := by
    intro i j hij
    apply hFinitePlaceInjective
    exact Sum.inl_injective hij
  have hImageSubset : Finset.univ.image place ⊆
      finiteExtensionGcdSupport K E x y := by
    intro v hv
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hv
    have hri : 0 < finitePlaceOrder (finitePlace i) x :=
      finitePlaceOrder_affinePointExhaustiveFinitePlace_pos_of_mem
        hf hpartialFirst hpartialSecond (point i) r (hr i) hr0
    exact inl_mem_finiteExtensionGcdSupport_of_orders_positive
      K E x y (finitePlace i) hri
  calc
    Fintype.card ι = (Finset.univ.image place).card := by
      rw [Finset.card_image_of_injective _ hPlaceInjective,
        Finset.card_univ]
    _ = ∑ v ∈ Finset.univ.image place, 1 := by simp
    _ ≤ ∑ v ∈ Finset.univ.image place,
        finiteExtensionGcdMultiplicity K E x y v *
          finiteExtensionPlaceDegree K E v := by
      apply Finset.sum_le_sum
      intro v hv
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hv
      have hri : 0 < finitePlaceOrder (finitePlace i) x :=
        finitePlaceOrder_affinePointExhaustiveFinitePlace_pos_of_mem
          hf hpartialFirst hpartialSecond (point i) r (hr i) hr0
      have hsi : 0 < finitePlaceOrder (finitePlace i) y :=
        finitePlaceOrder_affinePointExhaustiveFinitePlace_pos_of_mem
          hf hpartialFirst hpartialSecond (point i) s (hs i) hs0
      exact one_le_finiteExtensionGcdMultiplicity_mul_degree_inl_of_orders_positive
        K E x y (finitePlace i) hri hsi
    _ ≤ ∑ v ∈ finiteExtensionGcdSupport K E x y,
        finiteExtensionGcdMultiplicity K E x y v *
          finiteExtensionPlaceDegree K E v := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hImageSubset (by omega)
    _ = finiteExtensionGcdWeightedDegree K E x y := by
      rfl

end

end BGS.HasseWeil
