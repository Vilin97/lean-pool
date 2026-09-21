/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.CorvajaZannier.PlaneCurveFunctionField
import Mathlib.FieldTheory.LinearDisjoint
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Constant extensions of plane-curve function fields

This file constructs scalar extension at both the affine coordinate-ring and
function-field levels.  If `E / K` is algebraic and the base-changed plane
curve stays irreducible, then

`E ⊗[K] K(C) ≃ₐ[E] E(C_E)`.

The proof identifies the tensor product of `E` with the fraction field of the
coordinate ring as the fraction field of the tensor-product coordinate ring.
It then transports this fraction field through the explicit base-change
equivalence for the plane-curve coordinate ring.  No Galois, Frobenius, place,
or point-counting assertion is made here.
-/

open scoped TensorProduct nonZeroDivisors

namespace BGS.HasseWeil

noncomputable section

section TensorFraction

variable (K E A : Type*) [Field K] [Field E] [CommRing A]
  [Algebra K E] [Algebra K A]

/-- Tensor the fraction field of `A` with an extension field `E / K`. -/
abbrev TensorFraction := E ⊗[K] FractionRing A

/-- Tensor `A` itself with an extension field `E / K`. -/
abbrev TensorBase := E ⊗[K] A

/-- Localize the tensor-product base ring at the images of the nonzero
elements of `A`. -/
abbrev TensorBaseLocalization := Localization
  (A⁰.map (Algebra.TensorProduct.includeRight (R := K) (A := E) (B := A)))

noncomputable instance tensorBaseTensorFractionAlgebra :
    Algebra (TensorBase K E A) (TensorFraction K E A) :=
  (Algebra.TensorProduct.map (AlgHom.id K E)
    (IsScalarTower.toAlgHom K A (FractionRing A))).toAlgebra

theorem tensorBaseTensorFraction_algebraMap_tmul (e : E) (a : A) :
    algebraMap (TensorBase K E A) (TensorFraction K E A) (e ⊗ₜ[K] a) =
      e ⊗ₜ[K] algebraMap A (FractionRing A) a := by
  change Algebra.TensorProduct.map (AlgHom.id K E)
      (IsScalarTower.toAlgHom K A (FractionRing A)) (e ⊗ₜ[K] a) = _
  rw [Algebra.TensorProduct.map_tmul]
  rfl

instance tensorBaseTensorFractionScalarTower :
    IsScalarTower E (TensorBase K E A) (TensorFraction K E A) :=
  IsScalarTower.of_algebraMap_eq' (by
    ext e
    change e ⊗ₜ[K] 1 =
      algebraMap (TensorBase K E A) (TensorFraction K E A) (e ⊗ₜ[K] 1)
    rw [tensorBaseTensorFraction_algebraMap_tmul]
    simp)

variable [IsDomain A] [IsDomain (TensorBase K E A)]

private theorem tensorBase_nonZero_map :
    A⁰.map (Algebra.TensorProduct.includeRight (R := K) (A := E) (B := A)) ≤
      (TensorBase K E A)⁰ := by
  intro z hz
  rcases hz with ⟨a, ha, rfl⟩
  rw [mem_nonZeroDivisors_iff_ne_zero]
  intro hzero
  apply nonZeroDivisors.ne_zero ha
  apply Algebra.TensorProduct.includeRight_injective
    (R := K) (A := E) (B := A) (algebraMap K E).injective
  simpa using hzero

/-- Tensoring the fraction field agrees with localizing the tensor-product
base ring at the nonzero elements coming from `A`. -/
noncomputable def tensorFractionLocalizationEquiv :
    TensorFraction K E A ≃ₐ[E] TensorBaseLocalization K E A :=
  IsLocalization.tensorProductEquivOfMapIncludeRight K E A⁰
    (FractionRing A) (TensorBaseLocalization K E A)

omit [IsDomain A] [IsDomain (TensorBase K E A)] in
theorem tensorFractionLocalizationEquiv_algebraMap (z : TensorBase K E A) :
    tensorFractionLocalizationEquiv K E A
        (algebraMap (TensorBase K E A) (TensorFraction K E A) z) =
      algebraMap (TensorBase K E A) (TensorBaseLocalization K E A) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul e a =>
      exact IsLocalization.tensorProductEquivOfMapIncludeRight_tmul
        A A⁰ (FractionRing A) (TensorBaseLocalization K E A) e a
  | add x y hx hy => simp only [map_add, hx, hy]

local instance tensorFractionIsDomain : IsDomain (TensorFraction K E A) := by
  letI : IsDomain (TensorBaseLocalization K E A) :=
    IsLocalization.isDomain_localization (tensorBase_nonZero_map K E A)
  exact (tensorFractionLocalizationEquiv K E A).toMulEquiv.isDomain_iff.mpr
    inferInstance

noncomputable local instance tensorFractionField [Algebra.IsAlgebraic K E] :
    Field (TensorFraction K E A) :=
  (Algebra.TensorProduct.isField_of_isAlgebraic K E (FractionRing A)
    (.inl inferInstance)).toField

omit [IsDomain A] [IsDomain (TensorBase K E A)] in
private theorem tensorProduct_map_id_injective
    {B : Type*} [CommRing B] [Algebra K B]
    (F : A →ₐ[K] B) (hF : Function.Injective F) :
    Function.Injective
      (Algebra.TensorProduct.map (AlgHom.id E E) F) := by
  have heq :
      (Algebra.TensorProduct.map (AlgHom.id E E) F).toLinearMap.restrictScalars K =
        F.toLinearMap.lTensor E := by
    ext e a
    simp
  rw [← heq] at *
  exact Module.Flat.lTensor_preserves_injective_linearMap F.toLinearMap hF

local instance tensorBaseTensorFractionFaithfulSMul :
    FaithfulSMul (TensorBase K E A) (TensorFraction K E A) :=
  (faithfulSMul_iff_algebraMap_injective _ _).mpr
    (tensorProduct_map_id_injective K E A
      (IsScalarTower.toAlgHom K A (FractionRing A))
      (IsFractionRing.injective A (FractionRing A)))

/-- If the scalar-extended base ring is a domain and `E / K` is algebraic,
then tensoring the fraction field produces the fraction field of the
scalar-extended base ring. -/
theorem tensorFraction_isFractionRing [Algebra.IsAlgebraic K E] :
    IsFractionRing (TensorBase K E A) (TensorFraction K E A) := by
  apply IsFractionRing.of_field
  intro z
  let e := tensorFractionLocalizationEquiv K E A
  obtain ⟨⟨x, s⟩, hs⟩ := IsLocalization.surj
    (A⁰.map (Algebra.TensorProduct.includeRight
      (R := K) (A := E) (B := A))) (e z)
  refine ⟨x, s, ?_⟩
  have hsT :
      z * algebraMap (TensorBase K E A) (TensorFraction K E A) s =
        algebraMap (TensorBase K E A) (TensorFraction K E A) x := by
    apply e.injective
    simpa only [e, map_mul,
      tensorFractionLocalizationEquiv_algebraMap] using hs
  apply (eq_div_iff ?_).mpr
  · exact hsT
  · exact map_ne_zero_of_mem_nonZeroDivisors _
      (FaithfulSMul.algebraMap_injective _ _)
      (tensorBase_nonZero_map K E A s.property)

end TensorFraction

section PlaneCurve

open BGS.CorvajaZannier

variable (K E : Type*) [Field K] [Field E] [Algebra K E]
  (f : MvPolynomial (Fin 2) K)

/-- Scalar extension of a plane-curve coordinate ring, as an equivalence of
algebras over the enlarged constant field. -/
noncomputable def planeCurveCoordinateRingBaseChangeAlgEquiv :
    E ⊗[K] PlaneCurveCoordinateRing f ≃ₐ[E]
      PlaneCurveCoordinateRing (MvPolynomial.map (algebraMap K E) f) := by
  let P := MvPolynomial (Fin 2) K
  let PE := MvPolynomial (Fin 2) E
  let I : Ideal P := Ideal.span {f}
  let eP : E ⊗[K] P ≃ₐ[E] PE :=
    MvPolynomial.algebraTensorAlgEquiv K E
  let IT : Ideal (E ⊗[K] P) :=
    I.map (Algebra.TensorProduct.includeRight (R := K) (A := E) (B := P))
  let IE : Ideal PE :=
    Ideal.span {MvPolynomial.map (algebraMap K E) f}
  have hideal : IE = IT.map eP.toRingEquiv.toRingHom := by
    simp only [IE, IT, I, Ideal.map_span, Set.image_singleton]
    congr 2
    symm
    change (MvPolynomial.algebraTensorAlgEquiv K E) (1 ⊗ₜ[K] f) =
      MvPolynomial.map (algebraMap K E) f
    simpa only [one_smul] using
      (MvPolynomial.algebraTensorAlgEquiv_tmul
        (R := K) (A := E) (a := (1 : E)) f)
  exact
    (Algebra.TensorProduct.tensorQuotientEquiv
      (R := K) E P E I).trans
        (Ideal.quotientEquivAlg IT IE eP hideal)

/-- If the base-changed equation is irreducible, then its tensor-product
coordinate ring is a domain. -/
theorem planeCurveCoordinateRingBaseChange_isDomain
    (hfE : Irreducible (MvPolynomial.map (algebraMap K E) f)) :
    IsDomain (E ⊗[K] PlaneCurveCoordinateRing f) := by
  letI : IsDomain (PlaneCurveCoordinateRing
      (MvPolynomial.map (algebraMap K E) f)) :=
    planeCurveCoordinateRing_isDomain hfE
  exact (planeCurveCoordinateRingBaseChangeAlgEquiv K E f).toMulEquiv.isDomain_iff.mpr
    inferInstance

variable (hf : Irreducible f)
  (hfE : Irreducible (MvPolynomial.map (algebraMap K E) f))
  [Algebra.IsAlgebraic K E]

/-- Constant extension commutes with passing from an irreducible plane-curve
coordinate ring to its function field. -/
noncomputable def planeCurveFunctionFieldBaseChangeAlgEquiv :
    E ⊗[K] PlaneCurveFunctionField f ≃ₐ[E]
      PlaneCurveFunctionField (MvPolynomial.map (algebraMap K E) f) := by
  letI : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  letI : IsDomain (E ⊗[K] PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRingBaseChange_isDomain K E f hfE
  letI : IsFractionRing
      (E ⊗[K] PlaneCurveCoordinateRing f)
      (E ⊗[K] PlaneCurveFunctionField f) :=
    tensorFraction_isFractionRing K E (PlaneCurveCoordinateRing f)
  exact IsFractionRing.algEquivOfAlgEquiv
    (R := E)
    (A := E ⊗[K] PlaneCurveCoordinateRing f)
    (B := PlaneCurveCoordinateRing
      (MvPolynomial.map (algebraMap K E) f))
    (K := E ⊗[K] PlaneCurveFunctionField f)
    (L := PlaneCurveFunctionField
      (MvPolynomial.map (algebraMap K E) f))
    (planeCurveCoordinateRingBaseChangeAlgEquiv K E f)

theorem planeCurveFunctionFieldBaseChangeAlgEquiv_tmul_one (e : E) :
    planeCurveFunctionFieldBaseChangeAlgEquiv K E f hf hfE
        (e ⊗ₜ[K] 1) =
      algebraMap E
        (PlaneCurveFunctionField
          (MvPolynomial.map (algebraMap K E) f)) e := by
  letI : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  letI : IsDomain (E ⊗[K] PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRingBaseChange_isDomain K E f hfE
  letI : IsFractionRing
      (E ⊗[K] PlaneCurveCoordinateRing f)
      (E ⊗[K] PlaneCurveFunctionField f) :=
    tensorFraction_isFractionRing K E (PlaneCurveCoordinateRing f)
  change planeCurveFunctionFieldBaseChangeAlgEquiv K E f hf hfE
      (algebraMap E (E ⊗[K] PlaneCurveFunctionField f) e) = _
  exact (planeCurveFunctionFieldBaseChangeAlgEquiv K E f hf hfE).commutes e

end PlaneCurve

end

end BGS.HasseWeil
