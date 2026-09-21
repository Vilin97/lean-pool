/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.HasseWeil.ConstantFieldAutomorphism
import LeanPool.MarkoffModP.BGS.CorvajaZannier.PoweredImageBaseChange
import LeanPool.MarkoffModP.BGS.CorvajaZannier.PlaneCurveRatFuncModel
import LeanPool.MarkoffModP.BGS.HasseWeil.RatFuncConstantExtension

/-!
# Rational-function models under constant extension

This file proves that the scalar extension of a plane-curve function field is
compatible with coefficient extension of its rational-function base.  With
the first coordinate as separating variable, the square

`K(X) → K(C)`

`↓        ↓`

`E(X) → E(C_E)`

commutes exactly.  The induced `K(X)`-algebra on `E(C_E)` factors both through
`K(C)` and through `E(X)`.  For finite constant extensions it is finite and
separable over `K(X)`, so the existing exhaustive place-tower API can be
applied to `K(C) ⊂ E(C_E)`.

No fixed-point or rational-place correspondence is asserted here.
-/

open scoped TensorProduct Polynomial

namespace BGS.HasseWeil

noncomputable section

open BGS.CorvajaZannier

variable (K E : Type*) [Field K] [Field E] [Algebra K E]
  (f : MvPolynomial (Fin 2) K)

theorem planeCurveCoordinateRingBaseChangeAlgEquiv_includeRight
    (a : PlaneCurveCoordinateRing f) :
    planeCurveCoordinateRingBaseChangeAlgEquiv K E f
        (Algebra.TensorProduct.includeRight
          (R := K) (A := E) (B := PlaneCurveCoordinateRing f) a) =
      planeCurveCoordinateRingMap (E := E) f a := by
  let Φ : PlaneCurveCoordinateRing f →ₐ[K]
      PlaneCurveCoordinateRing (MvPolynomial.map (algebraMap K E) f) :=
    ((planeCurveCoordinateRingBaseChangeAlgEquiv K E f).restrictScalars K).toAlgHom.comp
      (Algebra.TensorProduct.includeRight
        (R := K) (A := E) (B := PlaneCurveCoordinateRing f))
  change Φ a = planeCurveCoordinateRingMap (E := E) f a
  suffices Φ = planeCurveCoordinateRingMap (E := E) f by
    exact DFunLike.congr_fun this a
  apply Ideal.Quotient.algHom_ext K
  apply MvPolynomial.algHom_ext
  intro i
  simp [Φ, planeCurveCoordinateRingBaseChangeAlgEquiv,
    planeCurveCoordinateRingMap]
  erw [Ideal.quotientEquivAlg_mk]
  simp only [MvPolynomial.algebraTensorAlgEquiv_tmul, one_smul]
  rfl

theorem planeCurveFunctionFieldBaseChangeAlgHom_function
    (hf : Irreducible f)
    (hfE : Irreducible (MvPolynomial.map (algebraMap K E) f))
    [Algebra.IsAlgebraic K E] (i : Fin 2) :
    planeCurveFunctionFieldBaseChangeAlgHom K E f hf hfE
        (planeCurveFunction f i) =
      planeCurveFunction (MvPolynomial.map (algebraMap K E) f) i := by
  letI : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  letI : IsDomain (E ⊗[K] PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRingBaseChange_isDomain K E f hfE
  letI : IsDomain (PlaneCurveCoordinateRing
      (MvPolynomial.map (algebraMap K E) f)) :=
    planeCurveCoordinateRing_isDomain hfE
  letI : IsFractionRing
      (E ⊗[K] PlaneCurveCoordinateRing f)
      (E ⊗[K] PlaneCurveFunctionField f) :=
    tensorFraction_isFractionRing K E (PlaneCurveCoordinateRing f)
  change planeCurveFunctionFieldBaseChangeAlgEquiv K E f hf hfE
      (1 ⊗ₜ[K] algebraMap (PlaneCurveCoordinateRing f)
        (PlaneCurveFunctionField f) (planeCurveCoordinate f i)) = _
  rw [← tensorBaseTensorFraction_algebraMap_tmul]
  rw [show planeCurveFunctionFieldBaseChangeAlgEquiv K E f hf hfE =
      IsFractionRing.algEquivOfAlgEquiv
        (planeCurveCoordinateRingBaseChangeAlgEquiv K E f) by rfl]
  rw [IsFractionRing.algEquivOfAlgEquiv_algebraMap]
  change algebraMap _ _
      (planeCurveCoordinateRingBaseChangeAlgEquiv K E f
        (Algebra.TensorProduct.includeRight
          (R := K) (A := E) (B := PlaneCurveCoordinateRing f)
            (planeCurveCoordinate f i))) = _
  rw [planeCurveCoordinateRingBaseChangeAlgEquiv_includeRight]
  rw [planeCurveCoordinateRingMap_coordinate]
  rfl

theorem planeCurveFunctionFieldBaseChange_ratFunc_commutes
    (hf : Irreducible f)
    (hfE : Irreducible (MvPolynomial.map (algebraMap K E) f))
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    [Algebra.IsAlgebraic K E] :
    let fE := MvPolynomial.map (algebraMap K E) f
    let hpartialSecondE : MvPolynomial.pderiv 1 fE ≠ 0 := by
      rw [MvPolynomial.pderiv_map]
      intro hz
      apply hpartialSecond
      apply MvPolynomial.map_injective (algebraMap K E)
        (algebraMap K E).injective
      simpa using hz
    letI : IsDomain (PlaneCurveCoordinateRing f) :=
      planeCurveCoordinateRing_isDomain hf
    letI : IsDomain (PlaneCurveCoordinateRing fE) :=
      planeCurveCoordinateRing_isDomain hfE
    let hx := firstCoordinate_transcendental hf
      (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
    let hxE := firstCoordinate_transcendental hfE
      (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecondE)
    letI := planeCurveFirstCoordinateRatFuncAlgebra f hx
    letI := planeCurveFirstCoordinateRatFuncAlgebra fE hxE
    ∀ z : RatFunc K,
      planeCurveFunctionFieldBaseChangeAlgHom K E f hf hfE
          (algebraMap (RatFunc K) (PlaneCurveFunctionField f) z) =
        algebraMap (RatFunc E) (PlaneCurveFunctionField fE)
          (ratFuncCoefficientAlgHom K E z) := by
  let fE := MvPolynomial.map (algebraMap K E) f
  let hpartialSecondE : MvPolynomial.pderiv 1 fE ≠ 0 := by
    rw [MvPolynomial.pderiv_map]
    intro hz
    apply hpartialSecond
    apply MvPolynomial.map_injective (algebraMap K E)
      (algebraMap K E).injective
    simpa using hz
  letI : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  letI : IsDomain (PlaneCurveCoordinateRing fE) :=
    planeCurveCoordinateRing_isDomain hfE
  let hx := firstCoordinate_transcendental hf
    (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
  let hxE := firstCoordinate_transcendental hfE
    (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecondE)
  letI := planeCurveFirstCoordinateRatFuncAlgebra f hx
  letI := planeCurveFirstCoordinateRatFuncAlgebra fE hxE
  letI : Algebra K[X] E[X] :=
    (Polynomial.mapRingHom (algebraMap K E)).toAlgebra
  change ∀ z : RatFunc K,
    planeCurveFunctionFieldBaseChangeAlgHom K E f hf hfE
        (algebraMap (RatFunc K) (PlaneCurveFunctionField f) z) =
      algebraMap (RatFunc E) (PlaneCurveFunctionField fE)
        (ratFuncCoefficientAlgHom K E z)
  let left : RatFunc K →+* PlaneCurveFunctionField fE :=
    (planeCurveFunctionFieldBaseChangeAlgHom K E f hf hfE).toRingHom.comp
      (algebraMap (RatFunc K) (PlaneCurveFunctionField f))
  let right : RatFunc K →+* PlaneCurveFunctionField fE :=
    (algebraMap (RatFunc E) (PlaneCurveFunctionField fE)).comp
      (ratFuncCoefficientAlgHom K E).toRingHom
  have hhom : left = right := by
    apply IsFractionRing.ringHom_ext (A := K[X])
    intro p
    suffices
        left (algebraMap K[X] (RatFunc K) Polynomial.X) =
          right (algebraMap K[X] (RatFunc K) Polynomial.X) by
      let lpoly : K[X] →+* PlaneCurveFunctionField fE :=
        left.comp (algebraMap K[X] (RatFunc K))
      let rpoly : K[X] →+* PlaneCurveFunctionField fE :=
        right.comp (algebraMap K[X] (RatFunc K))
      have hpoly : lpoly = rpoly := by
        apply Polynomial.ringHom_ext
        · intro c
          have hspecK :
              ratFuncSpecialization (planeCurveFunction f 0) hx (RatFunc.C c) =
                algebraMap K (PlaneCurveFunctionField f) c := by
            have h := DFunLike.congr_fun
              (ratFuncSpecialization_comp_polynomial_algebraMap
                (planeCurveFunction f 0) hx) (Polynomial.C c)
            simpa using h
          have hspecE :
              ratFuncSpecialization (planeCurveFunction fE 0) hxE
                  (RatFunc.C (algebraMap K E c)) =
                algebraMap E (PlaneCurveFunctionField fE) (algebraMap K E c) := by
            have h := DFunLike.congr_fun
              (ratFuncSpecialization_comp_polynomial_algebraMap
                (planeCurveFunction fE 0) hxE)
              (Polynomial.C (algebraMap K E c))
            simpa using h
          have hcoeff :
              ratFuncCoefficientAlgHom K E (RatFunc.C c) =
                RatFunc.C (algebraMap K E c) := by
            change ratFuncCoefficientAlgHom K E
                (algebraMap K[X] (RatFunc K) (Polynomial.C c)) = _
            rw [ratFuncCoefficientAlgHom_algebraMap]
            simp
          change planeCurveFunctionFieldBaseChangeAlgHom K E f hf hfE
              (ratFuncSpecialization (planeCurveFunction f 0) hx (RatFunc.C c)) =
            ratFuncSpecialization (planeCurveFunction fE 0) hxE
              (ratFuncCoefficientAlgHom K E (RatFunc.C c))
          rw [hspecK, hcoeff, hspecE]
          exact (planeCurveFunctionFieldBaseChangeAlgHom K E f hf hfE).commutes c
        · exact this
      exact DFunLike.congr_fun hpoly p
    change planeCurveFunctionFieldBaseChangeAlgHom K E f hf hfE
        (algebraMap (RatFunc K) (PlaneCurveFunctionField f) RatFunc.X) =
      algebraMap (RatFunc E) (PlaneCurveFunctionField fE)
        (ratFuncCoefficientAlgHom K E RatFunc.X)
    rw [planeCurveFirstCoordinateRatFuncAlgebra_X,
      planeCurveFunctionFieldBaseChangeAlgHom_function]
    rw [show RatFunc.X = algebraMap K[X] (RatFunc K) Polynomial.X by rfl,
      ratFuncCoefficientAlgHom_algebraMap]
    rw [show algebraMap K[X] E[X] Polynomial.X = Polynomial.X by simp]
    change planeCurveFunction fE 0 =
      algebraMap (RatFunc E) (PlaneCurveFunctionField fE) RatFunc.X
    rw [planeCurveFirstCoordinateRatFuncAlgebra_X]
  intro z
  exact DFunLike.congr_fun hhom z

/-- The `K(X)`-algebra structure on the base-changed function field obtained
through the original function field. -/
@[reducible] noncomputable def planeCurveFunctionFieldBaseChangeRatFuncAlgebra
    (hf : Irreducible f)
    (hfE : Irreducible (MvPolynomial.map (algebraMap K E) f))
    [Algebra.IsAlgebraic K E]
    (hx : Transcendental K (planeCurveFunction f 0)) :
    Algebra (RatFunc K)
      (PlaneCurveFunctionField (MvPolynomial.map (algebraMap K E) f)) := by
  letI : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  letI : IsDomain (PlaneCurveCoordinateRing
      (MvPolynomial.map (algebraMap K E) f)) :=
    planeCurveCoordinateRing_isDomain hfE
  exact RingHom.toAlgebra
    ((planeCurveFunctionFieldBaseChangeAlgHom K E f hf hfE).toRingHom.comp
      (ratFuncSpecialization (planeCurveFunction f 0) hx))

theorem planeCurveFunctionFieldBaseChangeRatFunc_isScalarTower
    (hf : Irreducible f)
    (hfE : Irreducible (MvPolynomial.map (algebraMap K E) f))
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    [Algebra.IsAlgebraic K E] :
    letI : IsDomain (PlaneCurveCoordinateRing f) :=
      planeCurveCoordinateRing_isDomain hf
    letI : IsDomain (PlaneCurveCoordinateRing
        (MvPolynomial.map (algebraMap K E) f)) :=
      planeCurveCoordinateRing_isDomain hfE
    let hx := firstCoordinate_transcendental hf
      (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
    letI := planeCurveFirstCoordinateRatFuncAlgebra f hx
    letI := planeCurveFunctionFieldBaseChangeAlgebra K E f hf hfE
    letI := planeCurveFunctionFieldBaseChangeRatFuncAlgebra K E f hf hfE hx
    IsScalarTower (RatFunc K) (PlaneCurveFunctionField f)
      (PlaneCurveFunctionField
        (MvPolynomial.map (algebraMap K E) f)) := by
  letI : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  letI : IsDomain (PlaneCurveCoordinateRing
      (MvPolynomial.map (algebraMap K E) f)) :=
    planeCurveCoordinateRing_isDomain hfE
  let hx := firstCoordinate_transcendental hf
    (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
  letI := planeCurveFirstCoordinateRatFuncAlgebra f hx
  letI := planeCurveFunctionFieldBaseChangeAlgebra K E f hf hfE
  letI := planeCurveFunctionFieldBaseChangeRatFuncAlgebra K E f hf hfE hx
  exact IsScalarTower.of_algebraMap_eq' rfl

theorem planeCurveFunctionFieldBaseChangeCoefficientRatFunc_isScalarTower
    (hf : Irreducible f)
    (hfE : Irreducible (MvPolynomial.map (algebraMap K E) f))
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    [Algebra.IsAlgebraic K E] :
    let fE := MvPolynomial.map (algebraMap K E) f
    let hpartialSecondE : MvPolynomial.pderiv 1 fE ≠ 0 := by
      rw [MvPolynomial.pderiv_map]
      intro hz
      apply hpartialSecond
      apply MvPolynomial.map_injective (algebraMap K E)
        (algebraMap K E).injective
      simpa using hz
    letI : IsDomain (PlaneCurveCoordinateRing f) :=
      planeCurveCoordinateRing_isDomain hf
    letI : IsDomain (PlaneCurveCoordinateRing fE) :=
      planeCurveCoordinateRing_isDomain hfE
    let hx := firstCoordinate_transcendental hf
      (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
    let hxE := firstCoordinate_transcendental hfE
      (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecondE)
    letI := ratFuncCoefficientAlgebra K E
    letI := planeCurveFirstCoordinateRatFuncAlgebra fE hxE
    letI := planeCurveFunctionFieldBaseChangeRatFuncAlgebra K E f hf hfE hx
    IsScalarTower (RatFunc K) (RatFunc E)
      (PlaneCurveFunctionField fE) := by
  let fE := MvPolynomial.map (algebraMap K E) f
  let hpartialSecondE : MvPolynomial.pderiv 1 fE ≠ 0 := by
    rw [MvPolynomial.pderiv_map]
    intro hz
    apply hpartialSecond
    apply MvPolynomial.map_injective (algebraMap K E)
      (algebraMap K E).injective
    simpa using hz
  letI : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  letI : IsDomain (PlaneCurveCoordinateRing fE) :=
    planeCurveCoordinateRing_isDomain hfE
  let hx := firstCoordinate_transcendental hf
    (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
  let hxE := firstCoordinate_transcendental hfE
    (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecondE)
  letI := ratFuncCoefficientAlgebra K E
  letI := planeCurveFirstCoordinateRatFuncAlgebra f hx
  letI := planeCurveFirstCoordinateRatFuncAlgebra fE hxE
  letI := planeCurveFunctionFieldBaseChangeRatFuncAlgebra K E f hf hfE hx
  apply IsScalarTower.of_algebraMap_eq'
  ext z
  exact (planeCurveFunctionFieldBaseChange_ratFunc_commutes
    K E f hf hfE hpartialSecond z)

theorem finiteDimensional_planeCurveFunctionFieldBaseChange_over_ratFunc
    (hf : Irreducible f)
    (hfE : Irreducible (MvPolynomial.map (algebraMap K E) f))
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    [Algebra.IsAlgebraic K E] [FiniteDimensional K E] :
    letI : IsDomain (PlaneCurveCoordinateRing f) :=
      planeCurveCoordinateRing_isDomain hf
    letI : IsDomain (PlaneCurveCoordinateRing
        (MvPolynomial.map (algebraMap K E) f)) :=
      planeCurveCoordinateRing_isDomain hfE
    let hx := firstCoordinate_transcendental hf
      (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
    letI := planeCurveFunctionFieldBaseChangeRatFuncAlgebra K E f hf hfE hx
    FiniteDimensional (RatFunc K)
      (PlaneCurveFunctionField
        (MvPolynomial.map (algebraMap K E) f)) := by
  letI : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  letI : IsDomain (PlaneCurveCoordinateRing
      (MvPolynomial.map (algebraMap K E) f)) :=
    planeCurveCoordinateRing_isDomain hfE
  let hx := firstCoordinate_transcendental hf
    (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
  letI := planeCurveFirstCoordinateRatFuncAlgebra f hx
  letI := planeCurveFunctionFieldBaseChangeAlgebra K E f hf hfE
  letI := planeCurveFunctionFieldBaseChangeRatFuncAlgebra K E f hf hfE hx
  letI : IsScalarTower (RatFunc K) (PlaneCurveFunctionField f)
      (PlaneCurveFunctionField
        (MvPolynomial.map (algebraMap K E) f)) :=
    planeCurveFunctionFieldBaseChangeRatFunc_isScalarTower
      K E f hf hfE hpartialSecond
  letI : FiniteDimensional (RatFunc K) (PlaneCurveFunctionField f) :=
    finiteDimensional_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  let e := planeCurveFunctionFieldBaseChangeLinearEquiv K E f hf hfE
  letI : Module.Finite (PlaneCurveFunctionField f)
      ((PlaneCurveFunctionField f) ⊗[K] E) :=
    Module.Finite.base_change K (PlaneCurveFunctionField f) E
  letI : Module.Finite (PlaneCurveFunctionField f)
      (PlaneCurveFunctionField (MvPolynomial.map (algebraMap K E) f)) :=
    Module.Finite.equiv e
  exact FiniteDimensional.trans (RatFunc K) (PlaneCurveFunctionField f)
    (PlaneCurveFunctionField (MvPolynomial.map (algebraMap K E) f))

theorem separable_planeCurveFunctionFieldBaseChange_over_ratFunc
    (hf : Irreducible f)
    (hfE : Irreducible (MvPolynomial.map (algebraMap K E) f))
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    [Algebra.IsAlgebraic K E] [Fintype K] [Finite E] :
    letI : IsDomain (PlaneCurveCoordinateRing f) :=
      planeCurveCoordinateRing_isDomain hf
    letI : IsDomain (PlaneCurveCoordinateRing
        (MvPolynomial.map (algebraMap K E) f)) :=
      planeCurveCoordinateRing_isDomain hfE
    let hx := firstCoordinate_transcendental hf
      (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
    letI := planeCurveFunctionFieldBaseChangeRatFuncAlgebra K E f hf hfE hx
    Algebra.IsSeparable (RatFunc K)
      (PlaneCurveFunctionField
        (MvPolynomial.map (algebraMap K E) f)) := by
  letI : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  letI : IsDomain (PlaneCurveCoordinateRing
      (MvPolynomial.map (algebraMap K E) f)) :=
    planeCurveCoordinateRing_isDomain hfE
  let hx := firstCoordinate_transcendental hf
    (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
  letI := planeCurveFirstCoordinateRatFuncAlgebra f hx
  letI := planeCurveFunctionFieldBaseChangeAlgebra K E f hf hfE
  letI := planeCurveFunctionFieldBaseChangeRatFuncAlgebra K E f hf hfE hx
  letI : IsScalarTower (RatFunc K) (PlaneCurveFunctionField f)
      (PlaneCurveFunctionField
        (MvPolynomial.map (algebraMap K E) f)) :=
    planeCurveFunctionFieldBaseChangeRatFunc_isScalarTower
      K E f hf hfE hpartialSecond
  letI : FiniteDimensional (RatFunc K) (PlaneCurveFunctionField f) :=
    finiteDimensional_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  letI : Algebra.IsSeparable (RatFunc K) (PlaneCurveFunctionField f) :=
    separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  let e := planeCurveFunctionFieldBaseChangeLinearEquiv K E f hf hfE
  letI : Module.Finite (PlaneCurveFunctionField f)
      ((PlaneCurveFunctionField f) ⊗[K] E) :=
    Module.Finite.base_change K (PlaneCurveFunctionField f) E
  letI : Module.Finite (PlaneCurveFunctionField f)
      (PlaneCurveFunctionField (MvPolynomial.map (algebraMap K E) f)) :=
    Module.Finite.equiv e
  letI : IsGalois (PlaneCurveFunctionField f)
      (PlaneCurveFunctionField (MvPolynomial.map (algebraMap K E) f)) :=
    planeCurveFunctionFieldBaseChange_isGalois K E f hf hfE
  exact Algebra.IsSeparable.trans (RatFunc K) (PlaneCurveFunctionField f)
    (PlaneCurveFunctionField (MvPolynomial.map (algebraMap K E) f))

end

end BGS.HasseWeil
