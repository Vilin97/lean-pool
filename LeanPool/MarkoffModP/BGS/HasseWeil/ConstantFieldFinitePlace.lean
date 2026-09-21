/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.HasseWeil.ConstantFieldRatFuncCompatibility
import LeanPool.MarkoffModP.BGS.HasseWeil.RationalPlaceTower
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

/-!
# Finite places under constant-field extension

If `R → S` is integral and both rings act compatibly on a common overring
`L`, then an element of `L` is integral over `R` exactly when it is integral
over `S`.  Thus the two integral closures are canonically ring-equivalent by
the identity on `L`.

For a plane-curve constant extension this identifies the integral closure of
`K[X]` in the enlarged function field with the integral closure of `E[X]` in
that same field.  It therefore gives an equivalence between the finite-place
types based on `K(X)` and `E(X)`.

This file concerns only finite places.  The valuation rings at infinity and
the comparison of place degrees are separate boundaries.
-/

open scoped Polynomial

namespace BGS.HasseWeil

noncomputable section

open BGS.CorvajaZannier

/-- Integral closures in a common overring agree after enlarging the base by
an integral extension.  The equivalence is the identity on the overring. -/
def integralClosureRingEquivOfIntegralTower
    (R S L : Type*) [CommRing R] [CommRing S] [CommRing L]
    [Algebra R S] [Algebra R L] [Algebra S L] [IsScalarTower R S L]
    [Algebra.IsIntegral R S] :
    integralClosure R L ≃+* integralClosure S L where
  toFun x := ⟨x.1, x.2.tower_top⟩
  invFun x := ⟨x.1, isIntegral_trans (R := R) (x : L) x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

/-- Algebra-equivalence form of the integral-closure identity. -/
def integralClosureAlgEquivOfIntegralTower
    (R S L : Type*) [CommRing R] [CommRing S] [CommRing L]
    [Algebra R S] [Algebra R L] [Algebra S L] [IsScalarTower R S L]
    [Algebra.IsIntegral R S] :
    integralClosure R L ≃ₐ[R] integralClosure S L :=
  { integralClosureRingEquivOfIntegralTower R S L with
    commutes' := fun _ => rfl }

@[simp]
theorem integralClosureRingEquivOfIntegralTower_coe
    (R S L : Type*) [CommRing R] [CommRing S] [CommRing L]
    [Algebra R S] [Algebra R L] [Algebra S L] [IsScalarTower R S L]
    [Algebra.IsIntegral R S] (x : integralClosure R L) :
    ((integralClosureRingEquivOfIntegralTower R S L x :
        integralClosure S L) : L) = x := rfl

variable (K E L : Type*) [Field K] [Field E] [Field L]
  [Algebra K E] [Algebra (RatFunc K) L] [Algebra (RatFunc E) L]

local instance constantFieldFinitePolynomialCoefficientAlgebra :
    Algebra K[X] E[X] :=
  (Polynomial.mapRingHom (algebraMap K E)).toAlgebra

local instance finiteBasePolynomialAlgebra : Algebra K[X] L :=
  RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
    (algebraMap K[X] (RatFunc K)))

local instance finiteExtensionPolynomialAlgebra : Algebra E[X] L :=
  RingHom.toAlgebra ((algebraMap (RatFunc E) L).comp
    (algebraMap E[X] (RatFunc E)))

/-- Compatible coefficient extension identifies the two finite integral
closures inside the common top function field. -/
def ratFuncFiniteIntegralClosureRingEquiv
    [Algebra.IsIntegral K E]
    (hcomm : ∀ p : K[X],
      algebraMap (RatFunc K) L (algebraMap K[X] (RatFunc K) p) =
        algebraMap (RatFunc E) L
          (algebraMap E[X] (RatFunc E)
            (algebraMap K[X] E[X] p))) :
    RatFuncFiniteIntegralClosure K L ≃+*
      RatFuncFiniteIntegralClosure E L := by
  letI : IsScalarTower K[X] E[X] L :=
    IsScalarTower.of_algebraMap_eq hcomm
  exact integralClosureRingEquivOfIntegralTower K[X] E[X] L

variable (f : MvPolynomial (Fin 2) K)

/-- The finite integral closures for a plane curve before and after constant
extension are canonically ring-equivalent inside the enlarged function
field. -/
def planeCurveFiniteIntegralClosureBaseChangeRingEquiv
    (hf : Irreducible f)
    (hfE : Irreducible (MvPolynomial.map (algebraMap K E) f))
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    [Algebra.IsAlgebraic K E] :
    let fE := MvPolynomial.map (algebraMap K E) f
    letI : IsDomain (PlaneCurveCoordinateRing f) :=
      planeCurveCoordinateRing_isDomain hf
    letI : IsDomain (PlaneCurveCoordinateRing fE) :=
      planeCurveCoordinateRing_isDomain hfE
    let hx := firstCoordinate_transcendental hf
      (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
    let hpartialSecondE : MvPolynomial.pderiv 1 fE ≠ 0 := by
      rw [MvPolynomial.pderiv_map]
      intro hz
      apply hpartialSecond
      apply MvPolynomial.map_injective (algebraMap K E)
        (algebraMap K E).injective
      simpa using hz
    let hxE := firstCoordinate_transcendental hfE
      (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecondE)
    letI := planeCurveFirstCoordinateRatFuncAlgebra f hx
    letI := planeCurveFirstCoordinateRatFuncAlgebra fE hxE
    letI := planeCurveFunctionFieldBaseChangeRatFuncAlgebra K E f hf hfE hx
    RatFuncFiniteIntegralClosure K (PlaneCurveFunctionField fE) ≃+*
      RatFuncFiniteIntegralClosure E (PlaneCurveFunctionField fE) := by
  let fE := MvPolynomial.map (algebraMap K E) f
  letI : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  letI : IsDomain (PlaneCurveCoordinateRing fE) :=
    planeCurveCoordinateRing_isDomain hfE
  let hx := firstCoordinate_transcendental hf
    (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
  let hpartialSecondE : MvPolynomial.pderiv 1 fE ≠ 0 := by
    rw [MvPolynomial.pderiv_map]
    intro hz
    apply hpartialSecond
    apply MvPolynomial.map_injective (algebraMap K E)
      (algebraMap K E).injective
    simpa using hz
  let hxE := firstCoordinate_transcendental hfE
    (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecondE)
  letI := planeCurveFirstCoordinateRatFuncAlgebra f hx
  letI := planeCurveFirstCoordinateRatFuncAlgebra fE hxE
  letI := planeCurveFunctionFieldBaseChangeRatFuncAlgebra K E f hf hfE hx
  apply ratFuncFiniteIntegralClosureRingEquiv K E
    (PlaneCurveFunctionField fE)
  intro p
  change planeCurveFunctionFieldBaseChangeAlgHom K E f hf hfE
      (algebraMap (RatFunc K) (PlaneCurveFunctionField f) p) = _
  rw [planeCurveFunctionFieldBaseChange_ratFunc_commutes
    K E f hf hfE hpartialSecond]
  apply congrArg (algebraMap (RatFunc E) (PlaneCurveFunctionField fE))
  exact ratFuncCoefficientAlgHom_algebraMap K E p

/-- The identity equivalence of finite integral closures transports their
height-one spectra, giving the finite-place base-change equivalence. -/
def planeCurveFinitePlaceBaseChangeEquiv
    (hf : Irreducible f)
    (hfE : Irreducible (MvPolynomial.map (algebraMap K E) f))
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    [Algebra.IsAlgebraic K E] :
    let fE := MvPolynomial.map (algebraMap K E) f
    letI : IsDomain (PlaneCurveCoordinateRing f) :=
      planeCurveCoordinateRing_isDomain hf
    letI : IsDomain (PlaneCurveCoordinateRing fE) :=
      planeCurveCoordinateRing_isDomain hfE
    let hx := firstCoordinate_transcendental hf
      (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
    let hpartialSecondE : MvPolynomial.pderiv 1 fE ≠ 0 := by
      rw [MvPolynomial.pderiv_map]
      intro hz
      apply hpartialSecond
      apply MvPolynomial.map_injective (algebraMap K E)
        (algebraMap K E).injective
      simpa using hz
    let hxE := firstCoordinate_transcendental hfE
      (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecondE)
    letI := planeCurveFirstCoordinateRatFuncAlgebra f hx
    letI := planeCurveFirstCoordinateRatFuncAlgebra fE hxE
    letI := planeCurveFunctionFieldBaseChangeRatFuncAlgebra K E f hf hfE hx
    FiniteExtensionFinitePlace K (PlaneCurveFunctionField fE) ≃
      FiniteExtensionFinitePlace E (PlaneCurveFunctionField fE) := by
  exact IsDedekindDomain.HeightOneSpectrum.equivOfRingEquiv
    (planeCurveFiniteIntegralClosureBaseChangeRingEquiv
      K E f hf hfE hpartialSecond)

end

end BGS.HasseWeil
