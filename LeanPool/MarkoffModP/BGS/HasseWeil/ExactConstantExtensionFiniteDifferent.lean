/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.HasseWeil.FiniteFieldPolynomialDifferent
import LeanPool.MarkoffModP.BGS.HasseWeil.RatFuncExactConstantExtension
import Mathlib.RingTheory.DedekindDomain.LinearDisjoint

/-!
# The finite different after exact constant extension

This file supplies the field-theoretic input for transporting the finite
different through an exact finite constant extension.  Inside
`ExactConstantExtension C N S`, the copies of `S(X)` and `N` generate the
whole tensor field and are linearly disjoint over `C(X)`.  The proof uses the
explicit tensor generation and the extension-degree formulas already proved
for rational-function and exact constant extensions.
-/

open scoped Polynomial TensorProduct

namespace BGS.HasseWeil

noncomputable section


@[reducible] private noncomputable def
    finiteDifferentCanonicalRatFuncPolynomialAlgebra
    (K : Type*) [Field K] : Algebra K[X] (RatFunc K) := inferInstance

private theorem finiteDifferentCanonicalRatFuncPolynomialFractionRing
    (K : Type*) [Field K] :
    letI := finiteDifferentCanonicalRatFuncPolynomialAlgebra K
    IsFractionRing K[X] (RatFunc K) := by
  letI := finiteDifferentCanonicalRatFuncPolynomialAlgebra K
  infer_instance

@[reducible] private noncomputable def
    finiteDifferentCanonicalFractionRingAlgebra
    (R : Type*) [CommRing R] [IsDomain R] :
    Algebra R (FractionRing R) := inferInstance

private theorem finiteDifferentCanonicalFractionRing
    (R : Type*) [CommRing R] [IsDomain R] :
    letI := finiteDifferentCanonicalFractionRingAlgebra R
    IsFractionRing R (FractionRing R) := by
  letI := finiteDifferentCanonicalFractionRingAlgebra R
  infer_instance

variable (C S N : Type*) [Field C] [Field S] [Field N]
  [Algebra (RatFunc C) N] [FiniteDimensional (RatFunc C) N]
  [Algebra.IsSeparable (RatFunc C) N]
  [Algebra C S] [FiniteDimensional C S] [IsGalois C S]

local instance finiteDifferentBaseConstantAlgebra : Algebra C N :=
  RingHom.toAlgebra ((algebraMap (RatFunc C) N).comp
    (algebraMap C (RatFunc C)))

local instance finiteDifferentBasePolynomialAlgebra : Algebra C[X] N :=
  ratFuncInducedPolynomialAlgebra C N

local instance finiteDifferentBaseConstantPolynomialTower :
    IsScalarTower C C[X] N :=
  IsScalarTower.of_algebraMap_eq' (by ext c; rfl)

local instance finiteDifferentCoefficientPolynomialAlgebra :
    Algebra C[X] S[X] := Polynomial.algebra C S

local instance finiteDifferentTargetPolynomialAlgebra :
    Algebra S[X] (ExactConstantExtension C N S) :=
  constantExtensionTensorPolynomialAlgebra C S N

local instance finiteDifferentTensorNormalizationPolynomialAlgebra :
    Algebra S[X] (S ⊗[C] integralClosure C[X] N) :=
  constantExtensionNormalizationTensorPolynomialAlgebra C S N

/-- The original finite normalization acts on the finite normalization after
constant extension through the right tensor factor and the canonical
normalization equivalence. -/
@[reducible] noncomputable def
    exactConstantExtensionFiniteNormalizationAlgebra
    [Fintype C] [Finite S] :
    Algebra (integralClosure C[X] N)
      (integralClosure S[X] (ExactConstantExtension C N S)) :=
  by
    let eNorm :
        S ⊗[C] integralClosure C[X] N ≃+*
          integralClosure S[X] (ExactConstantExtension C N S) :=
      finiteFieldConstantExtensionIntegralClosureRingEquiv C S N
    exact RingHom.toAlgebra
      (eNorm.toRingHom.comp
        (Algebra.TensorProduct.includeRight
          (R := C) (A := S) (B := integralClosure C[X] N)).toRingHom)

variable (hExact : algebraicClosure C N =
  (⊥ : IntermediateField C N))

/-- In an exact constant extension, the embedded copies of `S(X)` and `N`
are linearly disjoint over `C(X)` and generate the whole tensor field. -/
theorem exactConstantExtension_rationalFunctionRanges_linearDisjoint :
    let L := ExactConstantExtension C N S
    letI : Field L := exactConstantExtensionField C N S hExact
    letI : Algebra (RatFunc C) L :=
      exactConstantExtensionBaseAlgebra C (RatFunc C) N S
    letI : SMul (RatFunc C) L := Algebra.toSMul
    letI : Module (RatFunc C) L := Algebra.toModule
    letI : DistribMulAction (RatFunc C) L := Module.toDistribMulAction
    letI : MulAction (RatFunc C) L := DistribMulAction.toMulAction
    letI : Algebra N L := exactConstantExtensionAlgebra C N S
    letI : SMul N L := Algebra.toSMul
    letI : Module N L := Algebra.toModule
    letI : IsScalarTower (RatFunc C) N L :=
      exactConstantExtensionBaseTower C (RatFunc C) N S
    letI : Algebra (RatFunc C) (RatFunc S) :=
      ratFuncCoefficientAlgebra C S
    letI : SMul (RatFunc C) (RatFunc S) := Algebra.toSMul
    letI : Module (RatFunc C) (RatFunc S) := Algebra.toModule
    letI : Algebra (RatFunc S) L :=
      ratFuncExactConstantExtensionAlgebra C S N hExact
    letI : SMul (RatFunc S) L := Algebra.toSMul
    letI : Module (RatFunc S) L := Algebra.toModule
    letI : IsScalarTower (RatFunc C) (RatFunc S) L :=
      rationalBase_scalarTower C S N hExact
    let f₁ : RatFunc S →ₐ[RatFunc C] L :=
      IsScalarTower.toAlgHom (RatFunc C) (RatFunc S) L
    let f₂ : N →ₐ[RatFunc C] L :=
      IsScalarTower.toAlgHom (RatFunc C) N L
    let F₁ : IntermediateField (RatFunc C) L := f₁.fieldRange
    let F₂ : IntermediateField (RatFunc C) L := f₂.fieldRange
    F₁.LinearDisjoint F₂ ∧ F₁ ⊔ F₂ = ⊤ := by
  let L := ExactConstantExtension C N S
  letI : Field L := exactConstantExtensionField C N S hExact
  letI : Algebra (RatFunc C) L :=
    exactConstantExtensionBaseAlgebra C (RatFunc C) N S
  letI : SMul (RatFunc C) L := Algebra.toSMul
  letI : Module (RatFunc C) L := Algebra.toModule
  letI : DistribMulAction (RatFunc C) L := Module.toDistribMulAction
  letI : MulAction (RatFunc C) L := DistribMulAction.toMulAction
  letI : Algebra N L := exactConstantExtensionAlgebra C N S
  letI : SMul N L := Algebra.toSMul
  letI : Module N L := Algebra.toModule
  letI : IsScalarTower (RatFunc C) N L :=
    exactConstantExtensionBaseTower C (RatFunc C) N S
  letI : Algebra (RatFunc C) (RatFunc S) :=
    ratFuncCoefficientAlgebra C S
  letI : SMul (RatFunc C) (RatFunc S) := Algebra.toSMul
  letI : Module (RatFunc C) (RatFunc S) := Algebra.toModule
  letI : Algebra (RatFunc S) L :=
    ratFuncExactConstantExtensionAlgebra C S N hExact
  letI : SMul (RatFunc S) L := Algebra.toSMul
  letI : Module (RatFunc S) L := Algebra.toModule
  letI : IsScalarTower (RatFunc C) (RatFunc S) L :=
    rationalBase_scalarTower C S N hExact
  let e := exactConstantExtensionLinearEquiv C N S
  letI : Module.Finite N (N ⊗[C] S) :=
    Module.Finite.base_change C N S
  letI : Module.Finite N L := Module.Finite.equiv e
  letI : FiniteDimensional (RatFunc C) L :=
    Module.Finite.trans N L
  let f₁ : RatFunc S →ₐ[RatFunc C] L :=
    IsScalarTower.toAlgHom (RatFunc C) (RatFunc S) L
  let f₂ : N →ₐ[RatFunc C] L :=
    IsScalarTower.toAlgHom (RatFunc C) N L
  let F₁ : IntermediateField (RatFunc C) L := f₁.fieldRange
  let F₂ : IntermediateField (RatFunc C) L := f₂.fieldRange
  have hsup : F₁ ⊔ F₂ = ⊤ := by
    apply top_unique
    intro z _
    induction z using TensorProduct.induction_on with
    | zero => exact (F₁ ⊔ F₂).zero_mem
    | tmul s n =>
        rw [show s ⊗ₜ[C] n = (s ⊗ₜ[C] 1) * (1 ⊗ₜ[C] n) by simp]
        apply (F₁ ⊔ F₂).mul_mem
        · apply (show F₁ ≤ F₁ ⊔ F₂ from le_sup_left)
          exact ⟨algebraMap S (RatFunc S) s, by
            change f₁ (algebraMap S (RatFunc S) s) = s ⊗ₜ[C] 1
            exact (ratFuncToExactConstantExtension C S N hExact).commutes s⟩
        · apply (show F₂ ≤ F₁ ⊔ F₂ from le_sup_right)
          exact ⟨n, rfl⟩
    | add x y hx hy =>
        exact (F₁ ⊔ F₂).add_mem (hx (by simp)) (hy (by simp))
  let e₁ : RatFunc S ≃ₐ[RatFunc C] F₁ := f₁.equivFieldRange
  let e₂ : N ≃ₐ[RatFunc C] F₂ := f₂.equivFieldRange
  letI : FiniteDimensional (RatFunc C) F₁ := by
    letI : Module.Finite (RatFunc C) (RatFunc S) :=
      ratFuncCoefficient_moduleFinite C S
    exact Module.Finite.equiv e₁.toLinearEquiv
  letI : FiniteDimensional (RatFunc C) F₂ :=
    Module.Finite.equiv e₂.toLinearEquiv
  have hfinL :
      Module.finrank (RatFunc C) L =
        Module.finrank (RatFunc C) F₁ *
          Module.finrank (RatFunc C) F₂ := by
    calc
      Module.finrank (RatFunc C) L =
          Module.finrank (RatFunc C) N * Module.finrank N L := by
        rw [Module.finrank_mul_finrank]
      _ = Module.finrank (RatFunc C) N * Module.finrank C S := by
        rw [exactConstantExtension_finrank C N S]
      _ = Module.finrank C S * Module.finrank (RatFunc C) N := by
        rw [mul_comm]
      _ = Module.finrank (RatFunc C) (RatFunc S) *
          Module.finrank (RatFunc C) N := by
        rw [ratFuncCoefficient_finrank C S]
      _ = Module.finrank (RatFunc C) F₁ *
          Module.finrank (RatFunc C) F₂ := by
        rw [e₁.toLinearEquiv.finrank_eq, e₂.toLinearEquiv.finrank_eq]
  have hdisjoint : F₁.LinearDisjoint F₂ := by
    apply IntermediateField.LinearDisjoint.of_finrank_sup
    rw [hsup, IntermediateField.finrank_top']
    exact hfinL
  exact ⟨hdisjoint, hsup⟩

/-- In an exact finite constant extension, the different of the extended
finite normalization is the extension of the original finite different.
The map on ideals is the right-factor map supplied by
`exactConstantExtensionFiniteNormalizationAlgebra`. -/
theorem exactConstantExtension_finiteDifferent_eq_map
    [Fintype C] [Finite S] :
    let L := ExactConstantExtension C N S
    let R₂ := integralClosure C[X] N
    let B := integralClosure S[X] L
    letI : Field L := exactConstantExtensionField C N S hExact
    letI : Algebra S[X] L :=
      constantExtensionTensorPolynomialAlgebra C S N
    letI : SMul S[X] L := Algebra.toSMul
    letI : Module S[X] L := Algebra.toModule
    letI : Algebra (RatFunc S) L :=
      ratFuncExactConstantExtensionAlgebra C S N hExact
    letI : SMul (RatFunc S) L := Algebra.toSMul
    letI : Module (RatFunc S) L := Algebra.toModule
    letI : Algebra S[X] (RatFunc S) :=
      finiteDifferentCanonicalRatFuncPolynomialAlgebra S
    letI : IsFractionRing S[X] (RatFunc S) :=
      finiteDifferentCanonicalRatFuncPolynomialFractionRing S
    letI : IsScalarTower S[X] (RatFunc S) L :=
      IsScalarTower.of_algebraMap_eq' (by
        apply DFunLike.ext _ _
        intro p
        change algebraMap S[X] L p =
          ratFuncToExactConstantExtension C S N hExact
            (algebraMap S[X] (RatFunc S) p)
        exact
          (ratFuncToExactConstantExtension_algebraMap C S N hExact p).symm)
    letI : Module.IsTorsionFree S[X] L := by
      rw [Module.isTorsionFree_iff_algebraMap_injective]
      intro p q hpq
      apply RatFunc.algebraMap_injective S
      apply (algebraMap (RatFunc S) L).injective
      simpa only [IsScalarTower.algebraMap_apply S[X] (RatFunc S) L]
        using hpq
    letI : FiniteDimensional (RatFunc S) L :=
      finiteDimensional_over_extendedRatFunc C S N hExact
    letI : Algebra.IsSeparable (RatFunc S) L :=
      isSeparable_over_extendedRatFunc C S N hExact
    letI : IsDedekindDomain B :=
      IsIntegralClosure.isDedekindDomain S[X] (RatFunc S) L B
    letI : Module.IsTorsionFree S[X] B :=
      IsIntegralClosure.isTorsionFree S[X] L
    letI : Algebra C[X] (RatFunc C) :=
      finiteDifferentCanonicalRatFuncPolynomialAlgebra C
    letI : IsFractionRing C[X] (RatFunc C) :=
      finiteDifferentCanonicalRatFuncPolynomialFractionRing C
    letI : IsScalarTower C[X] (RatFunc C) N :=
      IsScalarTower.of_algebraMap_eq' rfl
    letI : IsDedekindDomain R₂ :=
      IsIntegralClosure.isDedekindDomain C[X] (RatFunc C) N R₂
    letI : Module.IsTorsionFree C[X] N := by
      rw [Module.isTorsionFree_iff_algebraMap_injective]
      change Function.Injective
        ((algebraMap (RatFunc C) N).comp
          (algebraMap C[X] (RatFunc C)))
      exact (algebraMap (RatFunc C) N).injective.comp
        (RatFunc.algebraMap_injective C)
    letI : Module.IsTorsionFree C[X] R₂ :=
      IsIntegralClosure.isTorsionFree C[X] N
    letI : Algebra R₂ B :=
      exactConstantExtensionFiniteNormalizationAlgebra C S N
    differentIdeal S[X] B =
      Ideal.map (algebraMap R₂ B) (differentIdeal C[X] R₂) := by
  let L := ExactConstantExtension C N S
  let R₂ := integralClosure C[X] N
  let B := integralClosure S[X] L
  letI : Field L := exactConstantExtensionField C N S hExact
  letI : Algebra S[X] L :=
    constantExtensionTensorPolynomialAlgebra C S N
  letI : IsDomain R₂ := inferInstance
  letI : IsDomain B := inferInstance
  letI : SMul S[X] L := Algebra.toSMul
  letI : Module S[X] L := Algebra.toModule
  letI : Algebra (RatFunc C) L :=
    exactConstantExtensionBaseAlgebra C (RatFunc C) N S
  letI : SMul (RatFunc C) L := Algebra.toSMul
  letI : Module (RatFunc C) L := Algebra.toModule
  letI : DistribMulAction (RatFunc C) L := Module.toDistribMulAction
  letI : MulAction (RatFunc C) L := DistribMulAction.toMulAction
  letI : Algebra N L := exactConstantExtensionAlgebra C N S
  letI : SMul N L := Algebra.toSMul
  letI : Module N L := Algebra.toModule
  letI : IsScalarTower (RatFunc C) N L :=
    exactConstantExtensionBaseTower C (RatFunc C) N S
  letI : Algebra (RatFunc C) (RatFunc S) :=
    ratFuncCoefficientAlgebra C S
  letI : SMul (RatFunc C) (RatFunc S) := Algebra.toSMul
  letI : Module (RatFunc C) (RatFunc S) := Algebra.toModule
  letI : Algebra (RatFunc S) L :=
    ratFuncExactConstantExtensionAlgebra C S N hExact
  letI : SMul (RatFunc S) L := Algebra.toSMul
  letI : Module (RatFunc S) L := Algebra.toModule
  letI : IsScalarTower (RatFunc C) (RatFunc S) L :=
    rationalBase_scalarTower C S N hExact
  letI : Algebra C[X] (RatFunc C) :=
    finiteDifferentCanonicalRatFuncPolynomialAlgebra C
  letI : IsFractionRing C[X] (RatFunc C) :=
    finiteDifferentCanonicalRatFuncPolynomialFractionRing C
  letI : IsScalarTower C[X] (RatFunc C) N :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra C[X] L :=
    RingHom.toAlgebra
      ((algebraMap (RatFunc C) L).comp
        (algebraMap C[X] (RatFunc C)))
  letI : SMul C[X] L := Algebra.toSMul
  letI : Module C[X] L := Algebra.toModule
  letI : IsScalarTower C[X] (RatFunc C) L :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra C[X] B :=
    RingHom.toAlgebra
      ((algebraMap S[X] B).comp (algebraMap C[X] S[X]))
  letI : SMul C[X] B := Algebra.toSMul
  letI : Module C[X] B := Algebra.toModule
  letI : IsScalarTower C[X] S[X] B :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower S[X] B L :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra S[X] (RatFunc S) :=
    finiteDifferentCanonicalRatFuncPolynomialAlgebra S
  letI : IsFractionRing S[X] (RatFunc S) :=
    finiteDifferentCanonicalRatFuncPolynomialFractionRing S
  letI : IsScalarTower S[X] (RatFunc S) L :=
    IsScalarTower.of_algebraMap_eq' (by
      apply DFunLike.ext _ _
      intro p
      change algebraMap S[X] L p =
        ratFuncToExactConstantExtension C S N hExact
          (algebraMap S[X] (RatFunc S) p)
      exact (ratFuncToExactConstantExtension_algebraMap C S N hExact p).symm)
  letI : IsScalarTower C[X] S[X] L :=
    IsScalarTower.of_algebraMap_eq' (by
      apply DFunLike.ext _ _
      intro p
      change algebraMap (RatFunc C) L
          (algebraMap C[X] (RatFunc C) p) =
        algebraMap S[X] L (algebraMap C[X] S[X] p)
      rw [IsScalarTower.algebraMap_apply S[X] (RatFunc S) L]
      rw [rationalBase_algebraMap_eq C S N hExact]
      apply congrArg (algebraMap (RatFunc S) L)
      exact ratFuncCoefficientAlgHom_algebraMap C S p)
  letI : IsScalarTower C[X] B L :=
    IsScalarTower.of_algebraMap_eq' (by
      apply DFunLike.ext _ _
      intro p
      change algebraMap C[X] L p =
        algebraMap S[X] L (algebraMap C[X] S[X] p)
      exact IsScalarTower.algebraMap_apply C[X] S[X] L p)
  letI : SMul C[X] S[X] := Algebra.toSMul
  letI : Module C[X] S[X] := Algebra.toModule
  letI : Module.Finite C[X] (C[X] ⊗[C] S) :=
    Module.Finite.base_change C C[X] S
  letI : Module.Finite C[X] S[X] :=
    Module.Finite.equiv
      (Algebra.IsPushout.equiv C C[X] S S[X]).toLinearEquiv
  letI : Module.IsTorsionFree C[X] S[X] := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]
    change Function.Injective (Polynomial.map (algebraMap C S))
    exact Polynomial.map_injective (algebraMap C S) (algebraMap C S).injective
  letI : Module.Free C[X] S[X] :=
    Module.free_of_finite_type_torsion_free'
  letI : Module.IsTorsionFree S[X] L := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]
    intro p q hpq
    apply RatFunc.algebraMap_injective S
    apply (algebraMap (RatFunc S) L).injective
    simpa only [IsScalarTower.algebraMap_apply S[X] (RatFunc S) L]
      using hpq
  letI : FiniteDimensional (RatFunc S) L :=
    finiteDimensional_over_extendedRatFunc C S N hExact
  letI : Algebra.IsSeparable (RatFunc S) L :=
    isSeparable_over_extendedRatFunc C S N hExact
  let eNL := exactConstantExtensionLinearEquiv C N S
  letI : Module.Finite N (N ⊗[C] S) :=
    Module.Finite.base_change C N S
  letI : Module.Finite N L := Module.Finite.equiv eNL
  letI : FiniteDimensional (RatFunc C) L :=
    Module.Finite.trans N L
  letI : Algebra.IsSeparable (RatFunc C) L :=
    isSeparable_exactConstantExtension_over_baseRatFunc C S N hExact
  let f₁ : RatFunc S →ₐ[RatFunc C] L :=
    IsScalarTower.toAlgHom (RatFunc C) (RatFunc S) L
  let f₂ : N →ₐ[RatFunc C] L :=
    IsScalarTower.toAlgHom (RatFunc C) N L
  let F₁ : IntermediateField (RatFunc C) L := f₁.fieldRange
  let F₂ : IntermediateField (RatFunc C) L := f₂.fieldRange
  let e₁ : RatFunc S ≃ₐ[RatFunc C] F₁ := f₁.equivFieldRange
  let e₂ : N ≃ₐ[RatFunc C] F₂ := f₂.equivFieldRange
  letI : Algebra S[X] F₁ :=
    RingHom.toAlgebra
      (e₁.toRingEquiv.toRingHom.comp (algebraMap S[X] (RatFunc S)))
  letI : SMul S[X] F₁ := Algebra.toSMul
  letI : Module S[X] F₁ := Algebra.toModule
  let e₁poly : RatFunc S ≃ₐ[S[X]] F₁ :=
    { e₁.toRingEquiv with commutes' := fun _ => rfl }
  letI : IsFractionRing S[X] F₁ :=
    IsFractionRing.of_algEquiv e₁poly
  letI : Module.IsTorsionFree S[X] F₁ := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]
    exact IsFractionRing.injective S[X] F₁
  letI : Algebra R₂ F₂ :=
    RingHom.toAlgebra
      (e₂.toRingEquiv.toRingHom.comp (algebraMap R₂ N))
  letI : SMul R₂ F₂ := Algebra.toSMul
  letI : Module R₂ F₂ := Algebra.toModule
  let e₂norm : N ≃ₐ[R₂] F₂ :=
    { e₂.toRingEquiv with commutes' := fun _ => rfl }
  letI : Algebra R₂ L :=
    RingHom.toAlgebra
      ((algebraMap F₂ L).comp (algebraMap R₂ F₂))
  letI : SMul R₂ L := Algebra.toSMul
  letI : Module R₂ L := Algebra.toModule
  letI : IsScalarTower R₂ F₂ L :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsFractionRing R₂ N :=
    IsIntegralClosure.isFractionRing_of_finite_extension
      C[X] (RatFunc C) N R₂
  letI : IsFractionRing R₂ F₂ :=
    IsFractionRing.of_algEquiv e₂norm
  letI : Algebra C[X] F₂ := IntermediateField.algebra' F₂
  letI : SMul C[X] F₂ := Algebra.toSMul
  letI : IsScalarTower C[X] R₂ F₂ :=
    IsScalarTower.of_algebraMap_eq' (by
      apply DFunLike.ext _ _
      intro p
      apply Subtype.ext
      change algebraMap (RatFunc C) L
          (algebraMap C[X] (RatFunc C) p) =
        algebraMap N L (algebraMap C[X] N p)
      rw [IsScalarTower.algebraMap_apply C[X] (RatFunc C) N]
      exact IsScalarTower.algebraMap_apply (RatFunc C) N L _)
  letI : IsScalarTower C[X] F₂ L :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower C[X] R₂ L :=
    IsScalarTower.of_algebraMap_eq' (by
      apply DFunLike.ext _ _
      intro p
      change algebraMap C[X] L p =
        algebraMap F₂ L
          (algebraMap R₂ F₂ (algebraMap C[X] R₂ p))
      rw [← IsScalarTower.algebraMap_apply C[X] R₂ F₂]
      exact IsScalarTower.algebraMap_apply C[X] F₂ L p)
  letI : IsLocalization
      (Algebra.algebraMapSubmonoid R₂ (nonZeroDivisors C[X])) N :=
    IsIntegralClosure.isLocalization C[X] (RatFunc C) N R₂
  letI : IsLocalization
      (Algebra.algebraMapSubmonoid R₂ (nonZeroDivisors C[X])) F₂ :=
    IsLocalization.isLocalization_of_algEquiv _ e₂norm
  letI : Algebra R₂ (S ⊗[C] R₂) :=
    Algebra.TensorProduct.rightAlgebra
  letI : SMul R₂ (S ⊗[C] R₂) := Algebra.toSMul
  letI : Module R₂ (S ⊗[C] R₂) := Algebra.toModule
  letI : Algebra R₂ (R₂ ⊗[C] S) :=
    Algebra.TensorProduct.leftAlgebra
  letI : SMul R₂ (R₂ ⊗[C] S) := Algebra.toSMul
  letI : Module R₂ (R₂ ⊗[C] S) := Algebra.toModule
  let eSwap : R₂ ⊗[C] S ≃ₐ[R₂] S ⊗[C] R₂ :=
    { (Algebra.TensorProduct.comm C R₂ S).toRingEquiv with
      commutes' := fun r => by
        change (Algebra.TensorProduct.comm C R₂ S)
          (r ⊗ₜ[C] (1 : S)) = (1 : S) ⊗ₜ[C] r
        rfl }
  letI : Module.Finite R₂ (R₂ ⊗[C] S) :=
    Module.Finite.base_change C R₂ S
  letI : Module.Finite R₂ (S ⊗[C] R₂) :=
    Module.Finite.equiv eSwap.toLinearEquiv
  let eNorm : S ⊗[C] R₂ ≃+* B :=
    finiteFieldConstantExtensionIntegralClosureRingEquiv C S N
  letI : Algebra R₂ B :=
    exactConstantExtensionFiniteNormalizationAlgebra C S N
  letI : SMul R₂ B := Algebra.toSMul
  letI : Module R₂ B := Algebra.toModule
  let eNormR₂ : S ⊗[C] R₂ ≃ₐ[R₂] B :=
    { eNorm with
      commutes' := fun r => by
        change eNorm (1 ⊗ₜ[C] r) =
          finiteFieldConstantExtensionIntegralClosureRingEquiv C S N
            (1 ⊗ₜ[C] r)
        rfl }
  letI : Module.Finite R₂ B :=
    Module.Finite.equiv eNormR₂.toLinearEquiv
  letI : Module.IsTorsionFree R₂ B := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]
    change Function.Injective
      (eNorm.toRingHom.comp
        (Algebra.TensorProduct.includeRight
          (R := C) (A := S) (B := R₂)).toRingHom)
    exact eNorm.injective.comp
      (Algebra.TensorProduct.includeRight_injective
        (R := C) (A := S) (B := R₂) (algebraMap C S).injective)
  have hR₂BL :
      (algebraMap R₂ L) =
        (algebraMap B L).comp (algebraMap R₂ B) := by
    ext r
    change (1 : S) ⊗ₜ[C] (r : N) =
      (((finiteFieldConstantExtensionIntegralClosureRingEquiv
          C S N) (1 ⊗ₜ[C] r) : B) : L)
    exact
      (finiteFieldConstantExtensionIntegralClosureRingEquiv_tmul
        C S N 1 r).symm
  letI : IsScalarTower R₂ B L :=
    IsScalarTower.of_algebraMap_eq' hR₂BL
  letI : IsScalarTower C[X] R₂ B :=
    IsScalarTower.of_algebraMap_eq' (by
      apply DFunLike.ext _ _
      intro p
      apply Subtype.ext
      calc
        algebraMap B L (algebraMap C[X] B p) =
            algebraMap B L
              (algebraMap S[X] B (algebraMap C[X] S[X] p)) := rfl
        _ = algebraMap S[X] L (algebraMap C[X] S[X] p) :=
          (IsScalarTower.algebraMap_apply S[X] B L _).symm
        _ = algebraMap C[X] L p :=
          (IsScalarTower.algebraMap_apply C[X] S[X] L p).symm
        _ = algebraMap R₂ L (algebraMap C[X] R₂ p) :=
          IsScalarTower.algebraMap_apply C[X] R₂ L p
        _ = algebraMap B L
            (algebraMap R₂ B (algebraMap C[X] R₂ p)) :=
          IsScalarTower.algebraMap_apply R₂ B L _)
  letI : Module.Finite C[X] R₂ :=
    IsIntegralClosure.finite C[X] (RatFunc C) N R₂
  letI : Module.IsTorsionFree C[X] N := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]
    change Function.Injective
      ((algebraMap (RatFunc C) N).comp
        (algebraMap C[X] (RatFunc C)))
    exact (algebraMap (RatFunc C) N).injective.comp
      (RatFunc.algebraMap_injective C)
  letI : Module.IsTorsionFree C[X] R₂ :=
    IsIntegralClosure.isTorsionFree C[X] N
  letI : Module.Free C[X] R₂ :=
    Module.free_of_finite_type_torsion_free'
  letI : Module.Finite C[X] B := Module.Finite.trans R₂ B
  letI : Module.IsTorsionFree C[X] B := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]
    intro p q hpq
    have hinj : Function.Injective (algebraMap C[X] L) := by
      change Function.Injective
        ((algebraMap (RatFunc C) L).comp
          (algebraMap C[X] (RatFunc C)))
      exact (algebraMap (RatFunc C) L).injective.comp
        (RatFunc.algebraMap_injective C)
    apply hinj
    simpa only [IsScalarTower.algebraMap_apply C[X] B L]
      using congrArg (algebraMap B L) hpq
  letI : FaithfulSMul C[X] B := by
    rw [faithfulSMul_iff_algebraMap_injective]
    exact Module.isTorsionFree_iff_algebraMap_injective.mp
      (show Module.IsTorsionFree C[X] B from inferInstance)
  letI : IsScalarTower S[X] F₁ L :=
    IsScalarTower.of_algebraMap_eq' (by
      apply DFunLike.ext _ _
      intro p
      change algebraMap S[X] L p = f₁ (algebraMap S[X] (RatFunc S) p)
      exact (ratFuncToExactConstantExtension_algebraMap C S N hExact p).symm)
  letI : Algebra.IsSeparable (RatFunc C) F₂ := inferInstance
  letI : Algebra.IsSeparable F₁ L := inferInstance
  letI : IsIntegralClosure B S[X] L := inferInstance
  letI : IsFractionRing B L :=
    IsIntegralClosure.isFractionRing_of_finite_extension S[X] F₁ L B
  letI : Algebra C[X] (FractionRing C[X]) :=
    finiteDifferentCanonicalFractionRingAlgebra C[X]
  letI : SMul C[X] (FractionRing C[X]) := Algebra.toSMul
  letI : IsFractionRing C[X] (FractionRing C[X]) :=
    finiteDifferentCanonicalFractionRing C[X]
  letI : Algebra B (FractionRing B) :=
    finiteDifferentCanonicalFractionRingAlgebra B
  letI : SMul B (FractionRing B) := Algebra.toSMul
  letI : IsFractionRing B (FractionRing B) :=
    finiteDifferentCanonicalFractionRing B
  letI : Algebra C[X] (FractionRing B) :=
    RingHom.toAlgebra
      ((algebraMap B (FractionRing B)).comp (algebraMap C[X] B))
  letI : SMul C[X] (FractionRing B) := Algebra.toSMul
  letI : IsScalarTower C[X] B (FractionRing B) :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : FaithfulSMul C[X] (FractionRing B) := by
    rw [faithfulSMul_iff_algebraMap_injective]
    change Function.Injective
      ((algebraMap B (FractionRing B)).comp (algebraMap C[X] B))
    exact (IsFractionRing.injective B (FractionRing B)).comp
      (FaithfulSMul.algebraMap_injective C[X] B)
  letI : Algebra (FractionRing C[X]) (FractionRing B) :=
    FractionRing.liftAlgebra C[X] (FractionRing B)
  letI : SMul (FractionRing C[X]) (FractionRing B) := Algebra.toSMul
  letI : IsScalarTower C[X] (FractionRing C[X]) (FractionRing B) :=
    FractionRing.isScalarTower_liftAlgebra C[X] (FractionRing B)
  letI : Algebra.IsSeparable (FractionRing C[X]) (FractionRing B) := by
    refine Algebra.IsSeparable.of_equiv_equiv
      (FractionRing.algEquiv C[X] (RatFunc C)).symm.toRingEquiv
      (FractionRing.algEquiv B L).symm.toRingEquiv ?_
    ext z
    exact IsFractionRing.algEquiv_commutes
      (FractionRing.algEquiv C[X] (RatFunc C)).symm
      (FractionRing.algEquiv B L).symm z
  letI : IsDedekindDomain B :=
    IsIntegralClosure.isDedekindDomain S[X] F₁ L B
  letI : IsDedekindDomain R₂ :=
    IsIntegralClosure.isDedekindDomain C[X] (RatFunc C) N R₂
  letI : Module.Finite S[X] B :=
    IsIntegralClosure.finite S[X] F₁ L B
  letI : Module.IsTorsionFree S[X] B :=
    IsIntegralClosure.isTorsionFree S[X] L
  have hranges :=
    exactConstantExtension_rationalFunctionRanges_linearDisjoint C S N hExact
  have hdisjoint : F₁.LinearDisjoint F₂ := by
    exact hranges.1
  have hsup : F₁ ⊔ F₂ = ⊤ := by
    exact hranges.2
  have hcoprime :
      IsCoprime
        ((differentIdeal C[X] S[X]).map (algebraMap S[X] B))
        ((differentIdeal C[X] R₂).map (algebraMap R₂ B)) := by
    rw [finiteFieldPolynomial_differentIdeal_eq_top C S]
    rw [Ideal.map_top]
    apply Ideal.isCoprime_iff_sup_eq.mpr
    exact top_sup_eq
      (Ideal.map (algebraMap R₂ B) (differentIdeal C[X] R₂))
  letI : IsScalarTower C[X] F₂ L :=
    IsScalarTower.of_algebraMap_eq' rfl
  exact IsDedekindDomain.differentIdeal_eq_map_differentIdeal
    (K := RatFunc C) (L := L) (F₁ := F₁) (F₂ := F₂)
    C[X] B S[X] R₂ hdisjoint hsup hcoprime

end

end BGS.HasseWeil
