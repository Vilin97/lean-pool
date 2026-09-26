/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.HasseWeil.ExactConstantExtensionFiniteDifferent
public import LeanPool.MarkoffModP.BGS.HasseWeil.FiniteFieldInfinityDifferent

/-!
# The infinity different after exact constant extension

For an exact finite extension of constants, the old infinity normalization
maps into the new infinity normalization through the canonical embedding of
the original function field. The two rational-function subfields remain
linearly disjoint, while the coefficient extension of infinity valuation
rings has unit different. The linear-disjoint different theorem therefore
identifies the new infinity different with the extension of the old one.
-/

@[expose] public section

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

variable (hExact : algebraicClosure C N =
  (⊥ : IntermediateField C N))

/-- The ambient constant-extension embedding restricts to the infinity integral closures. -/
noncomputable def exactConstantExtensionInfinityDifferentNormalizationRingHom
    [Fintype C] [Finite S] :
    let L := ExactConstantExtension C N S
    let : Field L := exactConstantExtensionField C N S hExact
    let : Algebra (RatFunc C) L :=
      exactConstantExtensionBaseAlgebra C (RatFunc C) N S
    let : Algebra N L := exactConstantExtensionAlgebra C N S
    let : Algebra (RatFunc S) L :=
      ratFuncExactConstantExtensionAlgebra C S N hExact
    let : Algebra (RatFuncInfinityIntegers C) (RatFunc C) :=
      Algebra.ofSubsemiring (RatFuncInfinityIntegers C)
    let : Algebra (RatFuncInfinityIntegers S) (RatFunc S) :=
      Algebra.ofSubsemiring (RatFuncInfinityIntegers S)
    let : Algebra (RatFuncInfinityIntegers C) N :=
      Algebra.ofSubsemiring (RatFuncInfinityIntegers C)
    let : Algebra (RatFuncInfinityIntegers C) L :=
      Algebra.ofSubsemiring (RatFuncInfinityIntegers C)
    let : Algebra (RatFuncInfinityIntegers S) L :=
      Algebra.ofSubsemiring (RatFuncInfinityIntegers S)
    let : Algebra (RatFuncInfinityIntegers C)
        (RatFuncInfinityIntegers S) := RingHom.toAlgebra (ratFuncInfinityIntegersRingHom C S)
    RatFuncInfinityIntegralClosure C N →+*
      RatFuncInfinityIntegralClosure S L := by
  let L := ExactConstantExtension C N S
  let : Field L := exactConstantExtensionField C N S hExact
  let : Algebra (RatFunc C) L :=
    exactConstantExtensionBaseAlgebra C (RatFunc C) N S
  let : SMul (RatFunc C) L := Algebra.toSMul
  let : Module (RatFunc C) L := Algebra.toModule
  let : Algebra N L := exactConstantExtensionAlgebra C N S
  let : SMul N L := Algebra.toSMul
  let : Module N L := Algebra.toModule
  let : IsScalarTower (RatFunc C) N L :=
    exactConstantExtensionBaseTower C (RatFunc C) N S
  let : Algebra (RatFunc C) (RatFunc S) :=
    ratFuncCoefficientAlgebra C S
  let : SMul (RatFunc C) (RatFunc S) := Algebra.toSMul
  let : Module (RatFunc C) (RatFunc S) := Algebra.toModule
  let : Algebra (RatFunc S) L :=
    ratFuncExactConstantExtensionAlgebra C S N hExact
  let : SMul (RatFunc S) L := Algebra.toSMul
  let : Module (RatFunc S) L := Algebra.toModule
  let : Algebra (RatFuncInfinityIntegers C) (RatFunc C) :=
    Algebra.ofSubsemiring (RatFuncInfinityIntegers C)
  let : SMul (RatFuncInfinityIntegers C) (RatFunc C) := Algebra.toSMul
  let : Module (RatFuncInfinityIntegers C) (RatFunc C) := Algebra.toModule
  let : Algebra (RatFuncInfinityIntegers S) (RatFunc S) :=
    Algebra.ofSubsemiring (RatFuncInfinityIntegers S)
  let : SMul (RatFuncInfinityIntegers S) (RatFunc S) := Algebra.toSMul
  let : Module (RatFuncInfinityIntegers S) (RatFunc S) := Algebra.toModule
  let : Algebra (RatFuncInfinityIntegers C) N :=
    Algebra.ofSubsemiring (RatFuncInfinityIntegers C)
  let : SMul (RatFuncInfinityIntegers C) N := Algebra.toSMul
  let : Module (RatFuncInfinityIntegers C) N := Algebra.toModule
  let : Algebra (RatFuncInfinityIntegers C) L :=
    Algebra.ofSubsemiring (RatFuncInfinityIntegers C)
  let : SMul (RatFuncInfinityIntegers C) L := Algebra.toSMul
  let : Module (RatFuncInfinityIntegers C) L := Algebra.toModule
  let : Algebra (RatFuncInfinityIntegers S) L :=
    Algebra.ofSubsemiring (RatFuncInfinityIntegers S)
  let : SMul (RatFuncInfinityIntegers S) L := Algebra.toSMul
  let : Module (RatFuncInfinityIntegers S) L := Algebra.toModule
  let : Algebra (RatFuncInfinityIntegers C)
      (RatFuncInfinityIntegers S) := RingHom.toAlgebra (ratFuncInfinityIntegersRingHom C S)
  let : SMul (RatFuncInfinityIntegers C)
      (RatFuncInfinityIntegers S) := Algebra.toSMul
  let : Module (RatFuncInfinityIntegers C)
      (RatFuncInfinityIntegers S) := Algebra.toModule
  let : Module.Finite (RatFuncInfinityIntegers C)
      (RatFuncInfinityIntegers S) :=
    ratFuncInfinityIntegers_coefficient_moduleFinite C S
  let : IsScalarTower (RatFuncInfinityIntegers C)
      (RatFuncInfinityIntegers S) L :=
    IsScalarTower.of_algebraMap_eq' (by
      ext z
      change algebraMap (RatFunc C) L z.1 =
        algebraMap (RatFunc S) L
          (ratFuncCoefficientAlgHom C S z.1)
      exact DFunLike.congr_fun
        (rationalBase_algebraMap_eq C S N hExact) z.1)
  let : IsScalarTower (RatFuncInfinityIntegers C) N L :=
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
    let : Field L := exactConstantExtensionField C N S hExact
    let : Algebra (RatFunc C) L :=
      exactConstantExtensionBaseAlgebra C (RatFunc C) N S
    let : Algebra N L := exactConstantExtensionAlgebra C N S
    let : Algebra (RatFunc S) L :=
      ratFuncExactConstantExtensionAlgebra C S N hExact
    let : Algebra (RatFuncInfinityIntegers C) (RatFunc C) :=
      Algebra.ofSubsemiring (RatFuncInfinityIntegers C)
    let : Algebra (RatFuncInfinityIntegers S) (RatFunc S) :=
      Algebra.ofSubsemiring (RatFuncInfinityIntegers S)
    let : Algebra (RatFuncInfinityIntegers C) N :=
      Algebra.ofSubsemiring (RatFuncInfinityIntegers C)
    let : Algebra (RatFuncInfinityIntegers C)
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
      let : Field L := exactConstantExtensionField C N S hExact
      let : Algebra (RatFunc C) L :=
        exactConstantExtensionBaseAlgebra C (RatFunc C) N S
      let : Algebra N L := exactConstantExtensionAlgebra C N S
      let : Algebra (RatFunc S) L :=
        ratFuncExactConstantExtensionAlgebra C S N hExact
      let : Algebra (RatFuncInfinityIntegers C) (RatFunc C) :=
        Algebra.ofSubsemiring (RatFuncInfinityIntegers C)
      let : Algebra (RatFuncInfinityIntegers S) (RatFunc S) :=
        Algebra.ofSubsemiring (RatFuncInfinityIntegers S)
      let : Algebra (RatFuncInfinityIntegers C) N :=
        Algebra.ofSubsemiring (RatFuncInfinityIntegers C)
      RatFuncInfinityIntegralClosure C N) :
    let L := ExactConstantExtension C N S
    let : Field L := exactConstantExtensionField C N S hExact
    let : Algebra (RatFunc C) L :=
      exactConstantExtensionBaseAlgebra C (RatFunc C) N S
    let : Algebra N L := exactConstantExtensionAlgebra C N S
    let : Algebra (RatFunc S) L :=
      ratFuncExactConstantExtensionAlgebra C S N hExact
    let : Algebra (RatFuncInfinityIntegers C) (RatFunc C) :=
      Algebra.ofSubsemiring (RatFuncInfinityIntegers C)
    let : Algebra (RatFuncInfinityIntegers S) (RatFunc S) :=
      Algebra.ofSubsemiring (RatFuncInfinityIntegers S)
    let : Algebra (RatFuncInfinityIntegers C) N :=
      Algebra.ofSubsemiring (RatFuncInfinityIntegers C)
    let : Algebra (RatFuncInfinityIntegers C)
        (RatFuncInfinityIntegers S) := RingHom.toAlgebra (ratFuncInfinityIntegersRingHom C S)
    let : Algebra (RatFuncInfinityIntegralClosure C N)
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
    let : Field L := exactConstantExtensionField C N S hExact
    let : Algebra (RatFunc C) L :=
      exactConstantExtensionBaseAlgebra C (RatFunc C) N S
    let : Algebra (RatFunc S) L :=
      ratFuncExactConstantExtensionAlgebra C S N hExact
    RatFuncInfinityIntegralClosure C L ≃+*
      RatFuncInfinityIntegralClosure S L := by
  let L := ExactConstantExtension C N S
  let A := RatFuncInfinityIntegers C
  let R₁ := RatFuncInfinityIntegers S
  let : Field L := exactConstantExtensionField C N S hExact
  let : Algebra (RatFunc C) L :=
    exactConstantExtensionBaseAlgebra C (RatFunc C) N S
  let : SMul (RatFunc C) L := Algebra.toSMul
  let : Module (RatFunc C) L := Algebra.toModule
  let : Algebra (RatFunc S) L :=
    ratFuncExactConstantExtensionAlgebra C S N hExact
  let : SMul (RatFunc S) L := Algebra.toSMul
  let : Module (RatFunc S) L := Algebra.toModule
  let : Algebra A (RatFunc C) := Algebra.ofSubsemiring A
  let : SMul A (RatFunc C) := Algebra.toSMul
  let : Module A (RatFunc C) := Algebra.toModule
  let : Algebra R₁ (RatFunc S) := Algebra.ofSubsemiring R₁
  let : SMul R₁ (RatFunc S) := Algebra.toSMul
  let : Module R₁ (RatFunc S) := Algebra.toModule
  let : Algebra A L := Algebra.ofSubsemiring A
  let : SMul A L := Algebra.toSMul
  let : Module A L := Algebra.toModule
  let : Algebra R₁ L := Algebra.ofSubsemiring R₁
  let : SMul R₁ L := Algebra.toSMul
  let : Module R₁ L := Algebra.toModule
  let : Algebra A R₁ :=
    RingHom.toAlgebra (ratFuncInfinityIntegersRingHom C S)
  let : SMul A R₁ := Algebra.toSMul
  let : Module A R₁ := Algebra.toModule
  let : Module.Finite A R₁ :=
    ratFuncInfinityIntegers_coefficient_moduleFinite C S
  let : Algebra.IsIntegral A R₁ := by infer_instance
  let : IsScalarTower A R₁ L :=
    IsScalarTower.of_algebraMap_eq' (by
      ext z
      change algebraMap (RatFunc C) L z.1 =
        algebraMap (RatFunc S) L (ratFuncCoefficientAlgHom C S z.1)
      exact DFunLike.congr_fun
        (rationalBase_algebraMap_eq C S N hExact) z.1)
  exact integralClosureRingEquivOfIntegralTower A R₁ L

omit [FiniteDimensional (RatFunc C) N] [Algebra.IsSeparable (RatFunc C) N] in
/-- The infinity-normalization base-change equivalence preserves the ambient
function-field element. -/
theorem exactConstantExtensionInfinityNormalizationBaseChangeRingEquiv_coe
    [Fintype C] [Finite S]
    (x :
      let L := ExactConstantExtension C N S
      let : Field L := exactConstantExtensionField C N S hExact
      let : Algebra (RatFunc C) L :=
        exactConstantExtensionBaseAlgebra C (RatFunc C) N S
      let : Algebra (RatFunc S) L :=
        ratFuncExactConstantExtensionAlgebra C S N hExact
      RatFuncInfinityIntegralClosure C L) :
    let L := ExactConstantExtension C N S
    let : Field L := exactConstantExtensionField C N S hExact
    let : Algebra (RatFunc C) L :=
      exactConstantExtensionBaseAlgebra C (RatFunc C) N S
    let : Algebra (RatFunc S) L :=
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
    let : Field L := exactConstantExtensionField C N S hExact
    let : Algebra (RatFunc C) L :=
      exactConstantExtensionBaseAlgebra C (RatFunc C) N S
    let : Algebra N L := exactConstantExtensionAlgebra C N S
    let : Algebra (RatFunc S) L :=
      ratFuncExactConstantExtensionAlgebra C S N hExact
    let : SMul (RatFunc S) L := Algebra.toSMul
    let : Module (RatFunc S) L := Algebra.toModule
    let : Algebra A (RatFunc C) := Algebra.ofSubsemiring (RatFuncInfinityIntegers C)
    let : SMul A (RatFunc C) := Algebra.toSMul
    let : Module A (RatFunc C) := Algebra.toModule
    let : Algebra R₁ (RatFunc S) := Algebra.ofSubsemiring (RatFuncInfinityIntegers S)
    let : SMul R₁ (RatFunc S) := Algebra.toSMul
    let : Module R₁ (RatFunc S) := Algebra.toModule
    let : IsFractionRing A (RatFunc C) :=
      IsFractionRing.of_algEquiv (ratFuncInfinityFractionRingEquiv C)
    let : IsFractionRing R₁ (RatFunc S) :=
      IsFractionRing.of_algEquiv (ratFuncInfinityFractionRingEquiv S)
    let : Algebra A N :=
      Algebra.ofSubsemiring A
    let : SMul A N := Algebra.toSMul
    let : Module A N := Algebra.toModule
    let : IsScalarTower A (RatFunc C) N :=
      IsScalarTower.of_algebraMap_eq' rfl
    let : Algebra A R₁ := RingHom.toAlgebra (ratFuncInfinityIntegersRingHom C S)
    let : Algebra R₁ L :=
      Algebra.ofSubsemiring R₁
    let : SMul R₁ L := Algebra.toSMul
    let : Module R₁ L := Algebra.toModule
    let : IsScalarTower R₁ (RatFunc S) L :=
      IsScalarTower.of_algebraMap_eq' rfl
    let R₂ := RatFuncInfinityIntegralClosure C N
    let B := RatFuncInfinityIntegralClosure S L
    let : Algebra A R₂ := Subalgebra.algebra R₂
    let : SMul A R₂ := Algebra.toSMul
    let : Module A R₂ := Algebra.toModule
    let : Algebra R₁ B := Subalgebra.algebra B
    let : SMul R₁ B := Algebra.toSMul
    let : Module R₁ B := Algebra.toModule
    let : IsIntegralClosure R₂ A N :=
      integralClosure.isIntegralClosure A N
    let : IsIntegralClosure B R₁ L :=
      integralClosure.isIntegralClosure R₁ L
    let : FiniteDimensional (RatFunc S) L :=
      finiteDimensional_over_extendedRatFunc C S N hExact
    let : Algebra.IsSeparable (RatFunc S) L :=
      isSeparable_over_extendedRatFunc C S N hExact
    let : IsDedekindDomain R₂ :=
      integralClosure.isDedekindDomain A (RatFunc C) N
    let : IsDedekindDomain B :=
      integralClosure.isDedekindDomain R₁ (RatFunc S) L
    let : Module.IsTorsionFree A R₂ := IsIntegralClosure.isTorsionFree A N
    let : Module.IsTorsionFree R₁ B := IsIntegralClosure.isTorsionFree R₁ L
    let : Algebra R₂ B :=
      exactConstantExtensionInfinityNormalizationAlgebra C S N hExact
    differentIdeal R₁ B =
      Ideal.map (algebraMap R₂ B) (differentIdeal A R₂) := by
  intro L A R₁ model3 model4 model5 model6 model7 model8 model9
    model10 model11 model12 model13 model14 model15 model16 model17 model18 model19 model20 model21
    model22 model23 model24 model25 R₂ B model28 model29 model30 model31 model32 model33
    model34 model35 model36 model37 model38 model39 model40 model41 model42
  let : SMul (RatFunc C) L := Algebra.toSMul
  let : Module (RatFunc C) L := Algebra.toModule
  let : DistribMulAction (RatFunc C) L := Module.toDistribMulAction
  let : MulAction (RatFunc C) L := DistribMulAction.toMulAction
  let : SMul N L := Algebra.toSMul
  let : Module N L := Algebra.toModule
  let : IsScalarTower (RatFunc C) N L :=
    exactConstantExtensionBaseTower C (RatFunc C) N S
  let : Algebra (RatFunc C) (RatFunc S) :=
    ratFuncCoefficientAlgebra C S
  let : SMul (RatFunc C) (RatFunc S) := Algebra.toSMul
  let : Module (RatFunc C) (RatFunc S) := Algebra.toModule
  let : IsScalarTower (RatFunc C) (RatFunc S) L :=
    rationalBase_scalarTower C S N hExact
  let : SMul A R₁ := Algebra.toSMul
  let : Module A R₁ := Algebra.toModule
  let : Module.Finite A R₁ :=
    ratFuncInfinityIntegers_coefficient_moduleFinite C S
  let : Module.IsTorsionFree A R₁ := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]
    change Function.Injective (ratFuncInfinityIntegersRingHom C S)
    exact ratFuncInfinityIntegersRingHom_injective C S
  let : Algebra.IsIntegral A R₁ := by infer_instance
  let : Algebra A L :=
    Algebra.ofSubsemiring A
  let : SMul A L := Algebra.toSMul
  let : Module A L := Algebra.toModule
  let : IsScalarTower A (RatFunc C) L :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : DistribMulAction R₁ L := Module.toDistribMulAction
  let : MulAction R₁ L := DistribMulAction.toMulAction
  let : IsScalarTower A R₁ L :=
    IsScalarTower.of_algebraMap_eq' (by
      ext z
      change algebraMap (RatFunc C) L z.1 =
        algebraMap (RatFunc S) L (ratFuncCoefficientAlgHom C S z.1)
      exact DFunLike.congr_fun
        (rationalBase_algebraMap_eq C S N hExact) z.1)
  let : Algebra R₂ N := Algebra.ofSubsemiring R₂
  let : SMul R₂ N := Algebra.toSMul
  let : Module R₂ N := Algebra.toModule
  let : IsScalarTower A R₂ N :=
    IsScalarTower.of_algebraMap_eq' (by ext z; rfl)
  let : Algebra B L := Algebra.ofSubsemiring B
  let : SMul B L := Algebra.toSMul
  let : Module B L := Algebra.toModule
  let : IsScalarTower R₁ B L :=
    IsScalarTower.of_algebraMap_eq' (by ext z; rfl)
  let : IsIntegralClosure R₂ A N := integralClosure.isIntegralClosure A N
  let : IsIntegralClosure B R₁ L := integralClosure.isIntegralClosure R₁ L
  let : IsDomain R₂ := inferInstance
  let : IsDomain B := inferInstance
  let : Module.IsTorsionFree R₁ L := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]
    exact (algebraMap (RatFunc S) L).injective.comp
      (IsFractionRing.injective R₁ (RatFunc S))
  let eNL := exactConstantExtensionLinearEquiv C N S
  let : Module.Finite N (N ⊗[C] S) := Module.Finite.base_change C N S
  let : Module.Finite N L := Module.Finite.equiv eNL
  let : FiniteDimensional (RatFunc C) L := Module.Finite.trans N L
  let : Algebra.IsSeparable (RatFunc C) L :=
    isSeparable_exactConstantExtension_over_baseRatFunc C S N hExact
  let : Algebra R₂ L :=
    RingHom.toAlgebra ((algebraMap N L).comp (algebraMap R₂ N))
  let : SMul R₂ L := Algebra.toSMul
  let : Module R₂ L := Algebra.toModule
  let : IsScalarTower R₂ N L := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower A N L := IsScalarTower.of_algebraMap_eq (fun z => by
    change algebraMap (RatFunc C) L z.1 =
      algebraMap N L (algebraMap (RatFunc C) N z.1)
    exact IsScalarTower.algebraMap_apply (RatFunc C) N L z.1)
  let : IsScalarTower A R₂ L := IsScalarTower.of_algebraMap_eq (fun z => by
    change algebraMap A L z = algebraMap N L (algebraMap R₂ N (algebraMap A R₂ z))
    rw [← IsScalarTower.algebraMap_apply A R₂ N,
      ← IsScalarTower.algebraMap_apply A N L])
  let : IsFractionRing R₂ N :=
    IsIntegralClosure.isFractionRing_of_finite_extension A (RatFunc C) N R₂
  let : Module.IsTorsionFree R₂ L := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]
    exact (algebraMap N L).injective.comp (IsFractionRing.injective R₂ N)
  let : SMul R₂ B := Algebra.toSMul
  let : Module R₂ B := Algebra.toModule
  let : IsScalarTower R₂ B L := IsScalarTower.of_algebraMap_eq' (by
    ext x
    exact exactConstantExtensionInfinityNormalizationAlgebra_coe C S N hExact x)
  let : IsScalarTower A R₂ B := IsScalarTower.of_algebraMap_eq' (by
    ext z
    calc
      ((algebraMap A B z : B) : L) = algebraMap A L z := rfl
      _ = algebraMap R₂ L (algebraMap A R₂ z) :=
        IsScalarTower.algebraMap_apply A R₂ L z
      _ = algebraMap B L (algebraMap R₂ B (algebraMap A R₂ z)) :=
        IsScalarTower.algebraMap_apply R₂ B L _)
  let : Module.Finite A R₂ := IsIntegralClosure.finite A (RatFunc C) N R₂
  let : Module.Free A R₂ := Module.free_of_finite_type_torsion_free'
  have hranges := exactConstantExtension_rationalFunctionRanges_linearDisjoint C S N hExact
  have hcoprime : IsCoprime ((differentIdeal A R₁).map (algebraMap R₁ B))
      ((differentIdeal A R₂).map (algebraMap R₂ B)) := by
    rw [ratFuncInfinityIntegers_coefficient_differentIdeal_eq_top C S, Ideal.map_top]
    exact Ideal.isCoprime_iff_sup_eq.mpr (top_sup_eq _)
  exact different_eq_map_of_linearlyDisjoint_fieldRanges A R₁ R₂ B (RatFunc C) (RatFunc S) N L
    hranges.1 hranges.2 hcoprime

end

end BGS.HasseWeil
