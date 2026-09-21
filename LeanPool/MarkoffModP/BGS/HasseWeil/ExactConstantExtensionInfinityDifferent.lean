/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.HasseWeil.ExactConstantExtensionFiniteDifferent
import LeanPool.MarkoffModP.BGS.HasseWeil.FiniteFieldInfinityDifferent

/-!
# The infinity different after exact constant extension

For an exact finite extension of constants, the old infinity normalization
maps into the new infinity normalization through the canonical embedding of
the original function field. The two rational-function subfields remain
linearly disjoint, while the coefficient extension of infinity valuation
rings has unit different. The linear-disjoint different theorem therefore
identifies the new infinity different with the extension of the old one.
-/

open scoped Polynomial TensorProduct

namespace BGS.HasseWeil

open BGS.CorvajaZannier

noncomputable section


variable (C S N : Type*) [Field C] [Field S] [Field N]
  [Algebra (RatFunc C) N] [FiniteDimensional (RatFunc C) N]
  [Algebra.IsSeparable (RatFunc C) N]
  [Algebra C S] [FiniteDimensional C S] [IsGalois C S]

local instance exactConstantExtensionInfinityDifferentBaseConstantAlgebra : Algebra C N :=
  RingHom.toAlgebra ((algebraMap (RatFunc C) N).comp
    (algebraMap C (RatFunc C)))

local instance exactConstantExtensionInfinityDifferentDecidableEqBaseRatFunc :
    DecidableEq (RatFunc C) := Classical.decEq _
local instance exactConstantExtensionInfinityDifferentDecidableEqExtendedRatFunc :
    DecidableEq (RatFunc S) := Classical.decEq _

@[reducible] private noncomputable def
    exactConstantExtensionInfinityDifferentCanonicalFractionRingAlgebra
    (R : Type*) [CommRing R] [IsDomain R] :
    Algebra R (FractionRing R) := inferInstance

private theorem exactConstantExtensionInfinityDifferentCanonicalFractionRing
    (R : Type*) [CommRing R] [IsDomain R] :
    letI := exactConstantExtensionInfinityDifferentCanonicalFractionRingAlgebra R
    IsFractionRing R (FractionRing R) := by
  letI := exactConstantExtensionInfinityDifferentCanonicalFractionRingAlgebra R
  infer_instance

variable (hExact : algebraicClosure C N =
  (⊥ : IntermediateField C N))

private noncomputable def
    exactConstantExtensionInfinityDifferentNormalizationRingHom
    [Fintype C] [Finite S] :
    let L := ExactConstantExtension C N S
    letI : Field L := exactConstantExtensionField C N S hExact
    letI : Algebra (RatFunc C) L :=
      exactConstantExtensionBaseAlgebra C (RatFunc C) N S
    letI : Algebra N L := exactConstantExtensionAlgebra C N S
    letI : Algebra (RatFunc S) L :=
      ratFuncExactConstantExtensionAlgebra C S N hExact
    letI : Algebra (RatFuncInfinityIntegers C) (RatFunc C) :=
      Algebra.ofSubsemiring (RatFuncInfinityIntegers C)
    letI : Algebra (RatFuncInfinityIntegers S) (RatFunc S) :=
      Algebra.ofSubsemiring (RatFuncInfinityIntegers S)
    letI : Algebra (RatFuncInfinityIntegers C) N :=
      Algebra.ofSubsemiring (RatFuncInfinityIntegers C)
    letI : Algebra (RatFuncInfinityIntegers C) L :=
      Algebra.ofSubsemiring (RatFuncInfinityIntegers C)
    letI : Algebra (RatFuncInfinityIntegers S) L :=
      Algebra.ofSubsemiring (RatFuncInfinityIntegers S)
    letI : Algebra (RatFuncInfinityIntegers C)
        (RatFuncInfinityIntegers S) := RingHom.toAlgebra (ratFuncInfinityIntegersRingHom C S)
    RatFuncInfinityIntegralClosure C N →+*
      RatFuncInfinityIntegralClosure S L := by
  let L := ExactConstantExtension C N S
  letI : Field L := exactConstantExtensionField C N S hExact
  letI : Algebra (RatFunc C) L :=
    exactConstantExtensionBaseAlgebra C (RatFunc C) N S
  letI : SMul (RatFunc C) L := Algebra.toSMul
  letI : Module (RatFunc C) L := Algebra.toModule
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
  letI : Algebra (RatFuncInfinityIntegers C) (RatFunc C) :=
    Algebra.ofSubsemiring (RatFuncInfinityIntegers C)
  letI : SMul (RatFuncInfinityIntegers C) (RatFunc C) := Algebra.toSMul
  letI : Module (RatFuncInfinityIntegers C) (RatFunc C) := Algebra.toModule
  letI : Algebra (RatFuncInfinityIntegers S) (RatFunc S) :=
    Algebra.ofSubsemiring (RatFuncInfinityIntegers S)
  letI : SMul (RatFuncInfinityIntegers S) (RatFunc S) := Algebra.toSMul
  letI : Module (RatFuncInfinityIntegers S) (RatFunc S) := Algebra.toModule
  letI : Algebra (RatFuncInfinityIntegers C) N :=
    Algebra.ofSubsemiring (RatFuncInfinityIntegers C)
  letI : SMul (RatFuncInfinityIntegers C) N := Algebra.toSMul
  letI : Module (RatFuncInfinityIntegers C) N := Algebra.toModule
  letI : Algebra (RatFuncInfinityIntegers C) L :=
    Algebra.ofSubsemiring (RatFuncInfinityIntegers C)
  letI : SMul (RatFuncInfinityIntegers C) L := Algebra.toSMul
  letI : Module (RatFuncInfinityIntegers C) L := Algebra.toModule
  letI : Algebra (RatFuncInfinityIntegers S) L :=
    Algebra.ofSubsemiring (RatFuncInfinityIntegers S)
  letI : SMul (RatFuncInfinityIntegers S) L := Algebra.toSMul
  letI : Module (RatFuncInfinityIntegers S) L := Algebra.toModule
  letI : Algebra (RatFuncInfinityIntegers C)
      (RatFuncInfinityIntegers S) := RingHom.toAlgebra (ratFuncInfinityIntegersRingHom C S)
  letI : SMul (RatFuncInfinityIntegers C)
      (RatFuncInfinityIntegers S) := Algebra.toSMul
  letI : Module (RatFuncInfinityIntegers C)
      (RatFuncInfinityIntegers S) := Algebra.toModule
  letI : Module.Finite (RatFuncInfinityIntegers C)
      (RatFuncInfinityIntegers S) :=
    ratFuncInfinityIntegers_coefficient_moduleFinite C S
  letI : IsScalarTower (RatFuncInfinityIntegers C)
      (RatFuncInfinityIntegers S) L :=
    IsScalarTower.of_algebraMap_eq' (by
      ext z
      change algebraMap (RatFunc C) L z.1 =
        algebraMap (RatFunc S) L
          (ratFuncCoefficientAlgHom C S z.1)
      exact DFunLike.congr_fun
        (rationalBase_algebraMap_eq C S N hExact) z.1)
  letI : IsScalarTower (RatFuncInfinityIntegers C) N L :=
    IsScalarTower.of_algebraMap_eq' (by
      ext z
      change algebraMap (RatFunc C) L z.1 =
        algebraMap N L (algebraMap (RatFunc C) N z.1)
      exact IsScalarTower.algebraMap_apply (RatFunc C) N L z.1)
  let f : N →ₐ[RatFuncInfinityIntegers C] L :=
    IsScalarTower.toAlgHom (RatFuncInfinityIntegers C) N L
  let e : integralClosure (RatFuncInfinityIntegers C) L ≃+*
      integralClosure (RatFuncInfinityIntegers S) L :=
    integralClosureRingEquivOfIntegralTower
      (RatFuncInfinityIntegers C) (RatFuncInfinityIntegers S) L
  exact e.toRingHom.comp f.mapIntegralClosure.toRingHom

/-- The original infinity normalization acts on the infinity normalization
after exact constant extension through the canonical embedding of the
original function field. -/
@[reducible] noncomputable def
    exactConstantExtensionInfinityNormalizationAlgebra
    [Fintype C] [Finite S] :
    let L := ExactConstantExtension C N S
    letI : Field L := exactConstantExtensionField C N S hExact
    letI : Algebra (RatFunc C) L :=
      exactConstantExtensionBaseAlgebra C (RatFunc C) N S
    letI : Algebra N L := exactConstantExtensionAlgebra C N S
    letI : Algebra (RatFunc S) L :=
      ratFuncExactConstantExtensionAlgebra C S N hExact
    letI : Algebra (RatFuncInfinityIntegers C) (RatFunc C) :=
      Algebra.ofSubsemiring (RatFuncInfinityIntegers C)
    letI : Algebra (RatFuncInfinityIntegers S) (RatFunc S) :=
      Algebra.ofSubsemiring (RatFuncInfinityIntegers S)
    letI : Algebra (RatFuncInfinityIntegers C) N :=
      Algebra.ofSubsemiring (RatFuncInfinityIntegers C)
    letI : Algebra (RatFuncInfinityIntegers C)
        (RatFuncInfinityIntegers S) := RingHom.toAlgebra (ratFuncInfinityIntegersRingHom C S)
    Algebra (RatFuncInfinityIntegralClosure C N)
      (RatFuncInfinityIntegralClosure S L) :=
  RingHom.toAlgebra
    (exactConstantExtensionInfinityDifferentNormalizationRingHom C S N hExact)

omit [FiniteDimensional (RatFunc C) N]
    [Algebra.IsSeparable (RatFunc C) N] in
/-- The infinity-normalization algebra map is the ambient embedding of the
original function field into the exact constant extension. -/
theorem exactConstantExtensionInfinityNormalizationAlgebra_coe
    [Fintype C] [Finite S]
    (x :
      let L := ExactConstantExtension C N S
      letI : Field L := exactConstantExtensionField C N S hExact
      letI : Algebra (RatFunc C) L :=
        exactConstantExtensionBaseAlgebra C (RatFunc C) N S
      letI : Algebra N L := exactConstantExtensionAlgebra C N S
      letI : Algebra (RatFunc S) L :=
        ratFuncExactConstantExtensionAlgebra C S N hExact
      letI : Algebra (RatFuncInfinityIntegers C) (RatFunc C) :=
        Algebra.ofSubsemiring (RatFuncInfinityIntegers C)
      letI : Algebra (RatFuncInfinityIntegers S) (RatFunc S) :=
        Algebra.ofSubsemiring (RatFuncInfinityIntegers S)
      letI : Algebra (RatFuncInfinityIntegers C) N :=
        Algebra.ofSubsemiring (RatFuncInfinityIntegers C)
      RatFuncInfinityIntegralClosure C N) :
    let L := ExactConstantExtension C N S
    letI : Field L := exactConstantExtensionField C N S hExact
    letI : Algebra (RatFunc C) L :=
      exactConstantExtensionBaseAlgebra C (RatFunc C) N S
    letI : Algebra N L := exactConstantExtensionAlgebra C N S
    letI : Algebra (RatFunc S) L :=
      ratFuncExactConstantExtensionAlgebra C S N hExact
    letI : Algebra (RatFuncInfinityIntegers C) (RatFunc C) :=
      Algebra.ofSubsemiring (RatFuncInfinityIntegers C)
    letI : Algebra (RatFuncInfinityIntegers S) (RatFunc S) :=
      Algebra.ofSubsemiring (RatFuncInfinityIntegers S)
    letI : Algebra (RatFuncInfinityIntegers C) N :=
      Algebra.ofSubsemiring (RatFuncInfinityIntegers C)
    letI : Algebra (RatFuncInfinityIntegers C)
        (RatFuncInfinityIntegers S) := RingHom.toAlgebra (ratFuncInfinityIntegersRingHom C S)
    letI : Algebra (RatFuncInfinityIntegralClosure C N)
        (RatFuncInfinityIntegralClosure S L) :=
      exactConstantExtensionInfinityNormalizationAlgebra C S N hExact
    ((algebraMap (RatFuncInfinityIntegralClosure C N)
        (RatFuncInfinityIntegralClosure S L) x :
      RatFuncInfinityIntegralClosure S L) : L) =
      algebraMap N L x.1 := by
  rfl

/-- Changing the infinity coefficient valuation ring from `C` to `S` does
not change the integral closure inside an exact constant extension.  The
underlying ring equivalence is the identity on the ambient function field. -/
noncomputable def exactConstantExtensionInfinityNormalizationBaseChangeRingEquiv
    [Fintype C] [Finite S] :
    let L := ExactConstantExtension C N S
    letI : Field L := exactConstantExtensionField C N S hExact
    letI : Algebra (RatFunc C) L :=
      exactConstantExtensionBaseAlgebra C (RatFunc C) N S
    letI : Algebra (RatFunc S) L :=
      ratFuncExactConstantExtensionAlgebra C S N hExact
    RatFuncInfinityIntegralClosure C L ≃+*
      RatFuncInfinityIntegralClosure S L := by
  let L := ExactConstantExtension C N S
  let A := RatFuncInfinityIntegers C
  let R₁ := RatFuncInfinityIntegers S
  letI : Field L := exactConstantExtensionField C N S hExact
  letI : Algebra (RatFunc C) L :=
    exactConstantExtensionBaseAlgebra C (RatFunc C) N S
  letI : SMul (RatFunc C) L := Algebra.toSMul
  letI : Module (RatFunc C) L := Algebra.toModule
  letI : Algebra (RatFunc S) L :=
    ratFuncExactConstantExtensionAlgebra C S N hExact
  letI : SMul (RatFunc S) L := Algebra.toSMul
  letI : Module (RatFunc S) L := Algebra.toModule
  letI : Algebra A (RatFunc C) := Algebra.ofSubsemiring A
  letI : SMul A (RatFunc C) := Algebra.toSMul
  letI : Module A (RatFunc C) := Algebra.toModule
  letI : Algebra R₁ (RatFunc S) := Algebra.ofSubsemiring R₁
  letI : SMul R₁ (RatFunc S) := Algebra.toSMul
  letI : Module R₁ (RatFunc S) := Algebra.toModule
  letI : Algebra A L := Algebra.ofSubsemiring A
  letI : SMul A L := Algebra.toSMul
  letI : Module A L := Algebra.toModule
  letI : Algebra R₁ L := Algebra.ofSubsemiring R₁
  letI : SMul R₁ L := Algebra.toSMul
  letI : Module R₁ L := Algebra.toModule
  letI : Algebra A R₁ :=
    RingHom.toAlgebra (ratFuncInfinityIntegersRingHom C S)
  letI : SMul A R₁ := Algebra.toSMul
  letI : Module A R₁ := Algebra.toModule
  letI : Module.Finite A R₁ :=
    ratFuncInfinityIntegers_coefficient_moduleFinite C S
  letI : Algebra.IsIntegral A R₁ := by infer_instance
  letI : IsScalarTower A R₁ L :=
    IsScalarTower.of_algebraMap_eq' (by
      ext z
      change algebraMap (RatFunc C) L z.1 =
        algebraMap (RatFunc S) L (ratFuncCoefficientAlgHom C S z.1)
      exact DFunLike.congr_fun
        (rationalBase_algebraMap_eq C S N hExact) z.1)
  exact integralClosureRingEquivOfIntegralTower A R₁ L

/-- The infinity-normalization base-change equivalence preserves the ambient
function-field element. -/
theorem exactConstantExtensionInfinityNormalizationBaseChangeRingEquiv_coe
    [Fintype C] [Finite S]
    (x :
      let L := ExactConstantExtension C N S
      letI : Field L := exactConstantExtensionField C N S hExact
      letI : Algebra (RatFunc C) L :=
        exactConstantExtensionBaseAlgebra C (RatFunc C) N S
      letI : Algebra (RatFunc S) L :=
        ratFuncExactConstantExtensionAlgebra C S N hExact
      RatFuncInfinityIntegralClosure C L) :
    let L := ExactConstantExtension C N S
    letI : Field L := exactConstantExtensionField C N S hExact
    letI : Algebra (RatFunc C) L :=
      exactConstantExtensionBaseAlgebra C (RatFunc C) N S
    letI : Algebra (RatFunc S) L :=
      ratFuncExactConstantExtensionAlgebra C S N hExact
    (((exactConstantExtensionInfinityNormalizationBaseChangeRingEquiv
        C S N hExact) x : RatFuncInfinityIntegralClosure S L) : L) = x := by
  rfl

/-- In an exact finite constant extension, the infinity different of the
extended normalization is the extension of the original infinity different. -/
theorem exactConstantExtension_infinityDifferent_eq_map
    [Fintype C] [Finite S] :
    let L := ExactConstantExtension C N S
    let A := RatFuncInfinityIntegers C
    let R₁ := RatFuncInfinityIntegers S
    letI : Field L := exactConstantExtensionField C N S hExact
    letI : Algebra (RatFunc C) L :=
      exactConstantExtensionBaseAlgebra C (RatFunc C) N S
    letI : Algebra N L := exactConstantExtensionAlgebra C N S
    letI : Algebra (RatFunc S) L :=
      ratFuncExactConstantExtensionAlgebra C S N hExact
    letI : SMul (RatFunc S) L := Algebra.toSMul
    letI : Module (RatFunc S) L := Algebra.toModule
    letI : Algebra A (RatFunc C) := Algebra.ofSubsemiring (RatFuncInfinityIntegers C)
    letI : SMul A (RatFunc C) := Algebra.toSMul
    letI : Module A (RatFunc C) := Algebra.toModule
    letI : Algebra R₁ (RatFunc S) := Algebra.ofSubsemiring (RatFuncInfinityIntegers S)
    letI : SMul R₁ (RatFunc S) := Algebra.toSMul
    letI : Module R₁ (RatFunc S) := Algebra.toModule
    letI : IsFractionRing A (RatFunc C) :=
      IsFractionRing.of_algEquiv (ratFuncInfinityFractionRingEquiv C)
    letI : IsFractionRing R₁ (RatFunc S) :=
      IsFractionRing.of_algEquiv (ratFuncInfinityFractionRingEquiv S)
    letI : Algebra A N :=
      Algebra.ofSubsemiring A
    letI : SMul A N := Algebra.toSMul
    letI : Module A N := Algebra.toModule
    letI : IsScalarTower A (RatFunc C) N :=
      IsScalarTower.of_algebraMap_eq' rfl
    letI : Algebra A R₁ := RingHom.toAlgebra (ratFuncInfinityIntegersRingHom C S)
    letI : Algebra R₁ L :=
      Algebra.ofSubsemiring R₁
    letI : SMul R₁ L := Algebra.toSMul
    letI : Module R₁ L := Algebra.toModule
    letI : IsScalarTower R₁ (RatFunc S) L :=
      IsScalarTower.of_algebraMap_eq' rfl
    let R₂ := RatFuncInfinityIntegralClosure C N
    let B := RatFuncInfinityIntegralClosure S L
    letI : IsIntegralClosure R₂ A N :=
      integralClosure.isIntegralClosure A N
    letI : IsIntegralClosure B R₁ L :=
      integralClosure.isIntegralClosure R₁ L
    letI : FiniteDimensional (RatFunc S) L :=
      finiteDimensional_over_extendedRatFunc C S N hExact
    letI : Algebra.IsSeparable (RatFunc S) L :=
      isSeparable_over_extendedRatFunc C S N hExact
    letI : IsDedekindDomain R₂ :=
      integralClosure.isDedekindDomain A (RatFunc C) N
    letI : IsDedekindDomain B :=
      integralClosure.isDedekindDomain R₁ (RatFunc S) L
    letI : Algebra R₂ B :=
      exactConstantExtensionInfinityNormalizationAlgebra C S N hExact
    differentIdeal R₁ B =
      Ideal.map (algebraMap R₂ B) (differentIdeal A R₂) := by
  let L := ExactConstantExtension C N S
  let A := RatFuncInfinityIntegers C
  let R₁ := RatFuncInfinityIntegers S
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
  letI : Algebra A (RatFunc C) := Algebra.ofSubsemiring (RatFuncInfinityIntegers C)
  letI : SMul A (RatFunc C) := Algebra.toSMul
  letI : Module A (RatFunc C) := Algebra.toModule
  letI : IsFractionRing A (RatFunc C) :=
    IsFractionRing.of_algEquiv (ratFuncInfinityFractionRingEquiv C)
  letI : Algebra R₁ (RatFunc S) := Algebra.ofSubsemiring (RatFuncInfinityIntegers S)
  letI : SMul R₁ (RatFunc S) := Algebra.toSMul
  letI : Module R₁ (RatFunc S) := Algebra.toModule
  letI : IsFractionRing R₁ (RatFunc S) :=
    IsFractionRing.of_algEquiv (ratFuncInfinityFractionRingEquiv S)
  letI : Algebra A R₁ := RingHom.toAlgebra (ratFuncInfinityIntegersRingHom C S)
  letI : SMul A R₁ := Algebra.toSMul
  letI : Module A R₁ := Algebra.toModule
  letI : Module.Finite A R₁ :=
    ratFuncInfinityIntegers_coefficient_moduleFinite C S
  letI : Module.IsTorsionFree A R₁ := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]
    change Function.Injective (ratFuncInfinityIntegersRingHom C S)
    exact ratFuncInfinityIntegersRingHom_injective C S
  letI : Algebra.IsIntegral A R₁ := by infer_instance
  letI : Algebra A N :=
    Algebra.ofSubsemiring A
  letI : SMul A N := Algebra.toSMul
  letI : Module A N := Algebra.toModule
  letI : IsScalarTower A (RatFunc C) N :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra A L :=
    Algebra.ofSubsemiring A
  letI : SMul A L := Algebra.toSMul
  letI : Module A L := Algebra.toModule
  letI : IsScalarTower A (RatFunc C) L :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra R₁ L :=
    Algebra.ofSubsemiring R₁
  letI : SMul R₁ L := Algebra.toSMul
  letI : Module R₁ L := Algebra.toModule
  letI : DistribMulAction R₁ L := Module.toDistribMulAction
  letI : MulAction R₁ L := DistribMulAction.toMulAction
  letI : IsScalarTower R₁ (RatFunc S) L :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower A R₁ L :=
    IsScalarTower.of_algebraMap_eq' (by
      ext z
      change algebraMap (RatFunc C) L z.1 =
        algebraMap (RatFunc S) L (ratFuncCoefficientAlgHom C S z.1)
      exact DFunLike.congr_fun
        (rationalBase_algebraMap_eq C S N hExact) z.1)
  let R₂ := RatFuncInfinityIntegralClosure C N
  let B := RatFuncInfinityIntegralClosure S L
  letI := Subalgebra.algebra R₂
  letI : SMul A R₂ := Algebra.toSMul
  letI : Module A R₂ := Algebra.toModule
  letI : Algebra R₂ N := Algebra.ofSubsemiring R₂
  letI : SMul R₂ N := Algebra.toSMul
  letI : Module R₂ N := Algebra.toModule
  letI : IsScalarTower A R₂ N :=
    IsScalarTower.of_algebraMap_eq' (by ext z; rfl)
  letI := Subalgebra.algebra B
  letI : SMul R₁ B := Algebra.toSMul
  letI : Module R₁ B := Algebra.toModule
  letI : Algebra B L := Algebra.ofSubsemiring B
  letI : SMul B L := Algebra.toSMul
  letI : Module B L := Algebra.toModule
  letI : IsScalarTower R₁ B L :=
    IsScalarTower.of_algebraMap_eq' (by ext z; rfl)
  letI : IsIntegralClosure R₂ A N :=
    integralClosure.isIntegralClosure A N
  letI : IsIntegralClosure B R₁ L :=
    integralClosure.isIntegralClosure R₁ L
  letI : IsDomain R₂ := inferInstance
  letI : IsDomain B := inferInstance
  letI : Module.IsTorsionFree R₁ L := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]
    exact (algebraMap (RatFunc S) L).injective.comp
      (IsFractionRing.injective R₁ (RatFunc S))
  letI : FiniteDimensional (RatFunc S) L :=
    finiteDimensional_over_extendedRatFunc C S N hExact
  letI : Algebra.IsSeparable (RatFunc S) L :=
    isSeparable_over_extendedRatFunc C S N hExact
  let eNL := exactConstantExtensionLinearEquiv C N S
  letI : Module.Finite N (N ⊗[C] S) := Module.Finite.base_change C N S
  letI : Module.Finite N L := Module.Finite.equiv eNL
  letI : FiniteDimensional (RatFunc C) L := Module.Finite.trans N L
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
  letI : Algebra R₁ F₁ :=
    RingHom.toAlgebra
      (e₁.toRingEquiv.toRingHom.comp (algebraMap R₁ (RatFunc S)))
  letI : SMul R₁ F₁ := Algebra.toSMul
  letI : Module R₁ F₁ := Algebra.toModule
  let e₁inf : RatFunc S ≃ₐ[R₁] F₁ :=
    { e₁.toRingEquiv with commutes' := fun _ => rfl }
  letI : IsFractionRing R₁ F₁ := IsFractionRing.of_algEquiv e₁inf
  letI : Module.IsTorsionFree R₁ F₁ := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]
    exact IsFractionRing.injective R₁ F₁
  letI : IsScalarTower R₁ F₁ L :=
    IsScalarTower.of_algebraMap_eq' (by
      ext z
      change algebraMap R₁ L z = f₁ (algebraMap R₁ (RatFunc S) z)
      rfl)
  letI : Algebra R₂ F₂ :=
    RingHom.toAlgebra
      (e₂.toRingEquiv.toRingHom.comp (algebraMap R₂ N))
  letI : SMul R₂ F₂ := Algebra.toSMul
  letI : Module R₂ F₂ := Algebra.toModule
  let e₂norm : N ≃ₐ[R₂] F₂ :=
    { e₂.toRingEquiv with commutes' := fun _ => rfl }
  letI : Algebra R₂ L :=
    RingHom.toAlgebra ((algebraMap F₂ L).comp (algebraMap R₂ F₂))
  letI : SMul R₂ L := Algebra.toSMul
  letI : Module R₂ L := Algebra.toModule
  letI : IsScalarTower R₂ F₂ L := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsFractionRing R₂ N :=
    IsIntegralClosure.isFractionRing_of_finite_extension A (RatFunc C) N R₂
  letI : IsFractionRing R₂ F₂ := IsFractionRing.of_algEquiv e₂norm
  letI : Module.IsTorsionFree R₂ L := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]
    exact (algebraMap F₂ L).injective.comp
      (IsFractionRing.injective R₂ F₂)
  letI : Algebra A F₂ := IntermediateField.algebra' F₂
  letI : SMul A F₂ := Algebra.toSMul
  letI : IsScalarTower A R₂ F₂ :=
    IsScalarTower.of_algebraMap_eq' (by
      ext z
      change algebraMap (RatFunc C) L z.1 =
        algebraMap N L (algebraMap (RatFunc C) N z.1)
      exact IsScalarTower.algebraMap_apply (RatFunc C) N L z.1)
  letI : IsScalarTower A F₂ L := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower A R₂ L :=
    IsScalarTower.of_algebraMap_eq' (by
      ext z
      change algebraMap A L z =
        algebraMap F₂ L (algebraMap R₂ F₂ (algebraMap A R₂ z))
      rw [← IsScalarTower.algebraMap_apply A R₂ F₂]
      exact IsScalarTower.algebraMap_apply A F₂ L z)
  letI : IsLocalization
      (Algebra.algebraMapSubmonoid R₂ (nonZeroDivisors A)) N :=
    IsIntegralClosure.isLocalization A (RatFunc C) N R₂
  letI : IsLocalization
      (Algebra.algebraMapSubmonoid R₂ (nonZeroDivisors A)) F₂ :=
    IsLocalization.isLocalization_of_algEquiv _ e₂norm
  letI : Algebra R₂ B :=
    exactConstantExtensionInfinityNormalizationAlgebra C S N hExact
  letI : SMul R₂ B := Algebra.toSMul
  letI : Module R₂ B := Algebra.toModule
  letI : IsScalarTower R₂ B L :=
    IsScalarTower.of_algebraMap_eq' (by
      ext x
      exact exactConstantExtensionInfinityNormalizationAlgebra_coe
        C S N hExact x)
  letI : IsScalarTower A R₂ B :=
    IsScalarTower.of_algebraMap_eq' (by
      ext z
      calc
        ((algebraMap A B z : B) : L) = algebraMap A L z := rfl
        _ = algebraMap R₂ L (algebraMap A R₂ z) :=
          IsScalarTower.algebraMap_apply A R₂ L z
        _ = algebraMap B L (algebraMap R₂ B (algebraMap A R₂ z)) :=
          IsScalarTower.algebraMap_apply R₂ B L _)
  letI : Module.Finite A R₂ :=
    IsIntegralClosure.finite A (RatFunc C) N R₂
  letI : Module.IsTorsionFree A R₂ :=
    IsIntegralClosure.isTorsionFree A N
  letI : Module.Free A R₂ := Module.free_of_finite_type_torsion_free'
  letI : IsDedekindDomain R₂ :=
    integralClosure.isDedekindDomain A (RatFunc C) N
  letI : IsDedekindDomain B :=
    integralClosure.isDedekindDomain R₁ (RatFunc S) L
  letI : IsIntegralClosure B R₂ L := by
    refine ⟨?_, ?_⟩
    · exact fun x y h => Subtype.ext h
    · intro x
      constructor
      · intro hx
        have hxA : IsIntegral A x := isIntegral_trans (R := A) x hx
        have hxR₁ : IsIntegral R₁ x := hxA.tower_top
        exact ⟨⟨x, hxR₁⟩, rfl⟩
      · rintro ⟨y, rfl⟩
        have hyA : IsIntegral A (y : L) :=
          isIntegral_trans (R := A) (y : L) y.2
        exact hyA.tower_top
  letI : Module.Finite R₂ B :=
    IsIntegralClosure.finite R₂ F₂ L B
  letI : Module.IsTorsionFree R₂ B :=
    IsIntegralClosure.isTorsionFree R₂ L
  letI : Module.Finite R₁ B :=
    IsIntegralClosure.finite R₁ F₁ L B
  letI : Module.IsTorsionFree R₁ B :=
    IsIntegralClosure.isTorsionFree R₁ L
  letI : Module.Finite A B := Module.Finite.trans R₂ B
  letI : Module.IsTorsionFree A B := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]
    have hR₂B : Function.Injective (algebraMap R₂ B) :=
      Module.isTorsionFree_iff_algebraMap_injective.mp
        (show Module.IsTorsionFree R₂ B from inferInstance)
    have hAR₂ : Function.Injective (algebraMap A R₂) :=
      Module.isTorsionFree_iff_algebraMap_injective.mp
        (show Module.IsTorsionFree A R₂ from inferInstance)
    exact hR₂B.comp hAR₂
  letI : IsIntegralClosure B R₁ L := inferInstance
  letI : IsFractionRing B L :=
    IsIntegralClosure.isFractionRing_of_finite_extension R₁ F₁ L B
  letI : Algebra.IsSeparable (RatFunc C) F₂ := inferInstance
  letI : Algebra.IsSeparable F₁ L := inferInstance
  letI : Algebra A (FractionRing A) := exactConstantExtensionInfinityDifferentCanonicalFractionRingAlgebra A
  letI : SMul A (FractionRing A) := Algebra.toSMul
  letI : IsFractionRing A (FractionRing A) := exactConstantExtensionInfinityDifferentCanonicalFractionRing A
  letI : Algebra B (FractionRing B) := exactConstantExtensionInfinityDifferentCanonicalFractionRingAlgebra B
  letI : SMul B (FractionRing B) := Algebra.toSMul
  letI : IsFractionRing B (FractionRing B) := exactConstantExtensionInfinityDifferentCanonicalFractionRing B
  letI : Algebra A (FractionRing B) :=
    RingHom.toAlgebra
      ((algebraMap B (FractionRing B)).comp (algebraMap A B))
  letI : SMul A (FractionRing B) := Algebra.toSMul
  letI : IsScalarTower A B (FractionRing B) :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : FaithfulSMul A (FractionRing B) := by
    rw [faithfulSMul_iff_algebraMap_injective]
    exact (IsFractionRing.injective B (FractionRing B)).comp
      (Module.isTorsionFree_iff_algebraMap_injective.mp
        (show Module.IsTorsionFree A B from inferInstance))
  letI : Algebra (FractionRing A) (FractionRing B) :=
    FractionRing.liftAlgebra A (FractionRing B)
  letI : SMul (FractionRing A) (FractionRing B) := Algebra.toSMul
  letI : IsScalarTower A (FractionRing A) (FractionRing B) :=
    FractionRing.isScalarTower_liftAlgebra A (FractionRing B)
  letI : Algebra.IsSeparable (FractionRing A) (FractionRing B) := by
    refine Algebra.IsSeparable.of_equiv_equiv
      (ratFuncInfinityFractionRingEquiv C).symm.toRingEquiv
      (FractionRing.algEquiv B L).symm.toRingEquiv ?_
    ext z
    exact IsFractionRing.algEquiv_commutes
      (ratFuncInfinityFractionRingEquiv C).symm
      (FractionRing.algEquiv B L).symm z
  have hranges :=
    exactConstantExtension_rationalFunctionRanges_linearDisjoint C S N hExact
  have hdisjoint : F₁.LinearDisjoint F₂ := hranges.1
  have hsup : F₁ ⊔ F₂ = ⊤ := hranges.2
  have hcoprime :
      IsCoprime
        ((differentIdeal A R₁).map (algebraMap R₁ B))
        ((differentIdeal A R₂).map (algebraMap R₂ B)) := by
    rw [ratFuncInfinityIntegers_coefficient_differentIdeal_eq_top C S]
    rw [Ideal.map_top]
    apply Ideal.isCoprime_iff_sup_eq.mpr
    exact top_sup_eq
      (Ideal.map (algebraMap R₂ B) (differentIdeal A R₂))
  exact IsDedekindDomain.differentIdeal_eq_map_differentIdeal
    (K := RatFunc C) (L := L) (F₁ := F₁) (F₂ := F₂)
    A B R₁ R₂ hdisjoint hsup hcoprime

end

end BGS.HasseWeil
