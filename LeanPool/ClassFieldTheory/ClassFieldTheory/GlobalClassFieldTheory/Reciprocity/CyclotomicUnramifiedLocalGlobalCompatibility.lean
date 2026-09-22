/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.CyclotomicUnramifiedGeometricRestriction
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalNormResidueNaturality
/-!
# Cyclotomic unramified local--global compatibility

For an unramified finite abelian subextension of an abstract rational
fixed field, the actual global norm-residue homomorphism agrees on every
finite one-place idele class with the chosen local Artin homomorphism.
-/

open scoped IsMulCommutative NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open ClassFormation
open KummerTheory

@[reducible]
private def composeMonoidHom
    {M N P : Type*} [MulOne M] [MulOne N] [MulOne P]
    (f : M →* N) (g : N →* P) : M →* P :=
  g.comp f

attribute [local instance]
  rationalSeparableClosureAlgebra
  naturalityAbstractFixedFieldBaseQuotientFinite
  naturalityAbstractFixedFieldRelativeQuotientFinite
  naturalityAbstractFixedFieldFiniteDimensional
  naturalityAbstractRelativeFixedFieldFiniteDimensional
  naturalityAbstractFixedFieldRelativeScalarTower
  naturalityAbstractRelativeFixedFieldAbsoluteFiniteDimensional
  naturalityAbstractFixedFieldNumberField
  naturalityAbstractRelativeFixedFieldNumberField
  naturalityAbstractRelativeFixedFieldIsAbelianGalois

/-- The finite ideles of an abstract fixed field carry the restricted-product group structure. -/
@[reducible]
noncomputable local instance
    abstractFixedFieldFiniteIdeleGroupGroup
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :
    Group
      (FiniteIdeleGroup
        (LocalClassFieldTheory.abstractFixedField
          ℚ (SeparableClosure ℚ) H.field)) :=
  RestrictedProduct.instGroupCoeOfSubgroupClass
    (fun v : IsDedekindDomain.HeightOneSpectrum
      (𝓞 (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field)) =>
      (v.adicCompletion
        (LocalClassFieldTheory.abstractFixedField
          ℚ (SeparableClosure ℚ) H.field))ˣ)

/-- The ideles of an abstract fixed field carry the product group structure. -/
@[reducible]
noncomputable local instance
    abstractFixedFieldIdeleGroupGroup
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :
    Group
      (IdeleGroup
        (LocalClassFieldTheory.abstractFixedField
          ℚ (SeparableClosure ℚ) H.field)) :=
  Prod.instGroup

/-- The idele classes of an abstract fixed field carry the quotient group structure. -/
@[reducible]
noncomputable local instance
    abstractFixedFieldIdeleClassGroupGroup
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :
    Group
      (IdeleClassGroup
        (LocalClassFieldTheory.abstractFixedField
          ℚ (SeparableClosure ℚ) H.field)) :=
  QuotientGroup.Quotient.group
    (IdeleGroup.principalSubgroup
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field))

private theorem
    restrictNormalHom_comp_infiniteGlobalArtinMonoidHom_of_tower
    (K E Ω : Type) [Field K] [NumberField K]
    [Field E] [NumberField E] [Algebra K E]
    [IsAbelianGalois K E]
    [Field Ω] [Algebra K Ω] [Algebra E Ω]
    [IsScalarTower K E Ω] [IsAbelianGalois K Ω] :
    (AlgEquiv.restrictNormalHom E).comp
        (infiniteGlobalArtinMonoidHom K Ω).toMonoidHom =
      globalArtinMonoidHom (K := K) (L := E) := by
  apply MonoidHom.ext
  intro a
  let j : E →ₐ[K] Ω := IsScalarTower.toAlgHom K E Ω
  let G : FiniteGaloisIntermediateField K Ω :=
    { toIntermediateField := j.fieldRange
      finiteDimensional :=
        j.equivFieldRange.toLinearEquiv.finiteDimensional
      isGalois := IsGalois.of_algEquiv j.equivFieldRange }
  let _ : FiniteDimensional K G := G.finiteDimensional
  let _ : NumberField G :=
    NumberField.of_module_finite K G
  let _ : IsAbelianGalois K G :=
    IsAbelianGalois.of_algHom G.toIntermediateField.val
  let _ : Algebra E G :=
    j.equivFieldRange.toRingHom.toAlgebra
  let _ : SMul E G := Algebra.toSMul
  let _ : IsScalarTower K E G :=
    IsScalarTower.of_algHom j.equivFieldRange.toAlgHom
  let _ : IsScalarTower K G Ω :=
    IntermediateField.isScalarTower_mid G.toIntermediateField
  let _ : IsScalarTower E G Ω :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hProjection :
      AlgEquiv.restrictNormalHom G
          (infiniteGlobalArtinMonoidHom K Ω a) =
        globalArtinMonoidHom (K := K) (L := G) a :=
    restrictNormalHom_infiniteGlobalArtinMonoidHom K Ω a G
  calc
    AlgEquiv.restrictNormalHom E
          (infiniteGlobalArtinMonoidHom K Ω a) =
        AlgEquiv.restrictNormalHom E
          (AlgEquiv.restrictNormalHom G
            (infiniteGlobalArtinMonoidHom K Ω a)) :=
      IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply E G
        (infiniteGlobalArtinMonoidHom K Ω a)
    _ = AlgEquiv.restrictNormalHom E
          (globalArtinMonoidHom (K := K) (L := G) a) :=
      congrArg (AlgEquiv.restrictNormalHom E) hProjection
    _ = globalArtinMonoidHom (K := K) (L := E) a :=
      DFunLike.congr_fun
        (globalArtinMonoidHom_restrict_tower
          (K := K) (L := G) (E := E)) a

private theorem
    abstractFixedFieldCyclotomicFiniteRestriction_comp_infiniteGlobalArtinMonoidHom
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension H.field)
    (hUnramified :
      L.toFiniteGaloisExtension.IsUnramified
        rationalCyclotomicDegreeData) :
    let F :=
      LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field
    let E :=
      LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) L.below
    let U :=
      LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ)
        (rationalCyclotomicFieldInertia_le H.field)
    letI _ : NumberField F :=
      cyclotomicUnramifiedGeometricBaseNumberField H
    letI _ : NumberField E :=
      cyclotomicUnramifiedGeometricRelativeNumberField H L
    letI _ : Algebra F E := E.algebra'
    letI _ : Algebra F U := U.algebra'
    letI _ : IsAbelianGalois F E :=
      cyclotomicUnramifiedGeometricRelativeIsAbelianGalois H L
    letI _ : IsAbelianGalois F U :=
      cyclotomicUnramifiedGeometricMaximalIsAbelianGalois H
    letI _ : Algebra E U :=
      abstractFixedFieldCyclotomicFiniteUnramifiedInclusionAlgebra
        H L hUnramified
    letI _ : @IsScalarTower F E U
        Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
      IsScalarTower.of_algHom
        (abstractFixedFieldCyclotomicFiniteUnramifiedInclusion
          H L hUnramified)
    (abstractFixedFieldCyclotomicFiniteRestrictionMonoidHom
        H L hUnramified).comp
        (infiniteGlobalArtinMonoidHom F U).toMonoidHom =
      globalArtinMonoidHom (K := F) (L := E) := by
  dsimp only
  let F :=
    LocalClassFieldTheory.abstractFixedField
      ℚ (SeparableClosure ℚ) H.field
  let E :=
    LocalClassFieldTheory.abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) L.below
  let U :=
    LocalClassFieldTheory.abstractRelativeFixedField
      ℚ (SeparableClosure ℚ)
      (rationalCyclotomicFieldInertia_le H.field)
  let fNumberField : NumberField F :=
    cyclotomicUnramifiedGeometricBaseNumberField H
  let eNumberField : NumberField E :=
    cyclotomicUnramifiedGeometricRelativeNumberField H L
  let fEAlgebra : Algebra F E := E.algebra'
  let fUAlgebra : Algebra F U := U.algebra'
  let fEIsAbelianGalois : IsAbelianGalois F E :=
    cyclotomicUnramifiedGeometricRelativeIsAbelianGalois H L
  let fUIsAbelianGalois : IsAbelianGalois F U :=
    cyclotomicUnramifiedGeometricMaximalIsAbelianGalois H
  let eUAlgebra : Algebra E U :=
    abstractFixedFieldCyclotomicFiniteUnramifiedInclusionAlgebra
      H L hUnramified
  let fEUTower : @IsScalarTower F E U
      Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    IsScalarTower.of_algHom
      (abstractFixedFieldCyclotomicFiniteUnramifiedInclusion
        H L hUnramified)
  calc
    (abstractFixedFieldCyclotomicFiniteRestrictionMonoidHom
        H L hUnramified).comp
        (infiniteGlobalArtinMonoidHom F U).toMonoidHom =
      (AlgEquiv.restrictNormalHom E).comp
        (infiniteGlobalArtinMonoidHom F U).toMonoidHom :=
      congrArg
        (fun f => f.comp
          (infiniteGlobalArtinMonoidHom F U).toMonoidHom)
        (abstractFixedFieldCyclotomicFiniteRestrictionMonoidHom_eq_restrictNormalHom
          H L hUnramified)
    _ = globalArtinMonoidHom (K := F) (L := E) :=
      restrictNormalHom_comp_infiniteGlobalArtinMonoidHom_of_tower
        F E U

private theorem
    abstractFixedFieldGlobalNormResidueMonoidHom_eq_cyclotomicRestrictionComp
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension H.field)
    (hUnramified :
      L.toFiniteGaloisExtension.IsUnramified
        rationalCyclotomicDegreeData) :
    let rhs :=
      composeMonoidHom
        (abstractFixedFieldCyclotomicIdeleClassArtinMonoidHom H)
        (abstractFixedFieldCyclotomicFiniteRestrictionMonoidHom
          H L hUnramified)
    abstractFixedFieldGlobalNormResidueMonoidHom H L = rhs := by
  dsimp only
  apply MonoidHom.ext
  intro c
  exact
    abstractFixedFieldGlobalNormResidueMonoidHom_eq_cyclotomicFiniteRestriction
      H L hUnramified c

private theorem
    abstractFixedFieldCyclotomicIdeleClassArtinMonoidHom_comp_finitePlaceIdeleClass
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (v : IsDedekindDomain.HeightOneSpectrum
      (𝓞 (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field))) :
    let F :=
      LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field
    let U :=
      LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ)
        (rationalCyclotomicFieldInertia_le H.field)
    letI _ : IsAbelianGalois F U :=
      abstractFixedFieldCyclotomic_isAbelianGalois H
    composeMonoidHom
        (IdeleGroup.finitePlaceIdeleClass v)
        (abstractFixedFieldCyclotomicIdeleClassArtinMonoidHom H) =
      composeMonoidHom
        (IdeleGroup.finitePlaceIdele v)
        (infiniteGlobalArtinMonoidHom F U).toMonoidHom := by
  dsimp only
  apply MonoidHom.ext
  intro x
  exact
    abstractFixedFieldCyclotomicIdeleClassArtinMonoidHom_mk
      H (IdeleGroup.finitePlaceIdele v x)

private theorem globalArtinMonoidHom_comp_finitePlaceIdele
    (K E : Type) [Field K] [NumberField K]
    [Field E] [NumberField E] [Algebra K E]
    [IsAbelianGalois K E]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    (globalArtinMonoidHom (K := K) (L := E)).comp
        (IdeleGroup.finitePlaceIdele v) =
      chosenFinitePlaceArtinMonoidHom
        (K := K) (L := E) v := by
  apply MonoidHom.ext
  intro x
  exact globalArtinMonoidHom_finitePlaceIdele
    (K := K) (L := E) v x

/-- The cyclotomic construction of fixed-field reciprocity satisfies
finite-place local--global compatibility on every finite unramified
abelian subextension. -/
theorem
    abstractFixedFieldGlobalNormResidueMonoidHom_comp_finitePlaceIdeleClass
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension H.field)
    (hUnramified :
      L.toFiniteGaloisExtension.IsUnramified
        rationalCyclotomicDegreeData)
    (v : IsDedekindDomain.HeightOneSpectrum
      (𝓞 (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field))) :
    let F :=
      LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field
    let E :=
      LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) L.below
    (abstractFixedFieldGlobalNormResidueMonoidHom H L).comp
        (IdeleGroup.finitePlaceIdeleClass v) =
      chosenFinitePlaceArtinMonoidHom
        (K := F) (L := E) v := by
  dsimp only
  let F :=
    LocalClassFieldTheory.abstractFixedField
      ℚ (SeparableClosure ℚ) H.field
  let E :=
    LocalClassFieldTheory.abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) L.below
  let U :=
    LocalClassFieldTheory.abstractRelativeFixedField
      ℚ (SeparableClosure ℚ)
      (rationalCyclotomicFieldInertia_le H.field)
  let fUIsAbelianGalois : IsAbelianGalois F U :=
    abstractFixedFieldCyclotomic_isAbelianGalois H
  let finiteIdele := IdeleGroup.finitePlaceIdele v
  let finiteIdeleClass := IdeleGroup.finitePlaceIdeleClass v
  let restriction :=
    abstractFixedFieldCyclotomicFiniteRestrictionMonoidHom
      H L hUnramified
  let ideleClassArtin :=
    abstractFixedFieldCyclotomicIdeleClassArtinMonoidHom H
  let infiniteArtin := infiniteGlobalArtinMonoidHom F U
  calc
    (abstractFixedFieldGlobalNormResidueMonoidHom H L).comp
          finiteIdeleClass =
        (restriction.comp ideleClassArtin).comp
          finiteIdeleClass :=
      congrArg
        (fun f => f.comp finiteIdeleClass)
        (abstractFixedFieldGlobalNormResidueMonoidHom_eq_cyclotomicRestrictionComp
          H L hUnramified)
    _ = restriction.comp
          (ideleClassArtin.comp finiteIdeleClass) := rfl
    _ = restriction.comp
          (infiniteArtin.toMonoidHom.comp finiteIdele) :=
      congrArg (fun f => restriction.comp f)
        (abstractFixedFieldCyclotomicIdeleClassArtinMonoidHom_comp_finitePlaceIdeleClass
          H v)
    _ = (restriction.comp infiniteArtin.toMonoidHom).comp
          finiteIdele := rfl
    _ = (globalArtinMonoidHom (K := F) (L := E)).comp
          finiteIdele :=
      congrArg (fun f => f.comp finiteIdele)
        (abstractFixedFieldCyclotomicFiniteRestriction_comp_infiniteGlobalArtinMonoidHom
          H L hUnramified)
    _ = chosenFinitePlaceArtinMonoidHom
          (K := F) (L := E) v :=
      globalArtinMonoidHom_comp_finitePlaceIdele F E v

/-- The canonical inclusion realization of a finite unramified abstract
fixed-field extension satisfies finite-place local--global compatibility. -/
theorem
    globalNormResidueMonoidHomOfEmbedding_comp_finitePlaceIdeleClass_of_abstractFixedFieldUnramified
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension H.field)
    (hUnramified :
      L.toFiniteGaloisExtension.IsUnramified
        rationalCyclotomicDegreeData)
    (v : IsDedekindDomain.HeightOneSpectrum
      (𝓞 (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field))) :
    let F :=
      LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field
    let E :=
      LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) L.below
    let j : E →ₐ[ℚ] SeparableClosure ℚ :=
      E.val.restrictScalars ℚ
    (globalNormResidueMonoidHomOfEmbedding F E j).comp
        (IdeleGroup.finitePlaceIdeleClass v) =
      chosenFinitePlaceArtinMonoidHom
        (K := F) (L := E) v := by
  dsimp only
  rw [
    globalNormResidueMonoidHomOfEmbedding_abstractFixedFieldInclusion
      H L]
  exact
    abstractFixedFieldGlobalNormResidueMonoidHom_comp_finitePlaceIdeleClass
      H L hUnramified v

end Reciprocity
end GlobalClassFieldTheory
