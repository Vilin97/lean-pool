/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.RayClassFieldRealization
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ArithmeticUnramifiedPrimeArtin
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalArtin
/-!
# Arithmetic prime Artin symbols on ray-class fixed fields

Arithmetic reciprocity on a ray-class fixed field agrees, at each ordinary
prime idèle, with the arithmetic global Artin symbol of that field.
-/

@[expose] public section

open scoped NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open NumberField IsDedekindDomain IdeleGroup Reciprocity

open scoped Classical in
private theorem arithmeticFinitePlacePrimeArtin_restrict_tower
    (K L E : Type) [Field K] [Field L] [Field E]
    [NumberField K] [NumberField L] [NumberField E]
    [Algebra K L] [Algebra K E] [Algebra E L] [IsScalarTower K E L]
    [IsAbelianGalois K L] [IsAbelianGalois K E]
    (v : HeightOneSpectrum (𝓞 K)) :
    AlgEquiv.restrictNormalHom E
        (arithmeticFinitePlacePrimeArtin (K := K) (L := L) v) =
      arithmeticFinitePlacePrimeArtin (K := K) (L := E) v := by
  rw [arithmeticFinitePlacePrimeArtin_eq_inv (K := K) (L := L) v,
    arithmeticFinitePlacePrimeArtin_eq_inv (K := K) (L := E) v, map_inv]
  simpa only [finitePlacePrimeArtin, MonoidHom.comp_apply] using
    congrArg Inv.inv
      (DFunLike.congr_fun
        (Reciprocity.globalArtinMonoidHom_restrict_tower
          (K := K) (L := L) (E := E))
        (IdeleGroup.finitePrimeIdele v))

open scoped Classical in
private theorem rayClassFieldGaloisEquivRayClassGroup_symm_mk
    {K : Type} [Field K] [NumberField K]
    (m : RayClass.Modulus K) (c : IdeleClassGroup K) :
    (rayClassFieldGaloisEquivRayClassGroup (K := K) m).symm
        (QuotientGroup.mk' m.congruenceSubgroup c) =
      globalNormResidueMonoidHom K (rayClassField K m) c := by
  apply (rayClassFieldGaloisEquivRayClassGroup (K := K) m).symm_apply_eq.mpr
  exact (rayClassFieldGaloisEquivRayClassGroup_globalNormResidue
    (K := K) m c).symm

open scoped Classical in
private theorem rayClassField_arithmeticFinitePlacePrimeArtin
    {K : Type} [Field K] [NumberField K]
    (m : RayClass.Modulus K)
    (v : HeightOneSpectrum (𝓞 K)) :
    (rayClassFieldGaloisEquivRayClassGroup (K := K) m).symm
        ((QuotientGroup.mk' m.congruenceSubgroup
          (QuotientGroup.mk' (IdeleGroup.principalSubgroup K)
            (IdeleGroup.finitePrimeIdele v)))⁻¹) =
      arithmeticFinitePlacePrimeArtin (K := K) (L := rayClassField K m) v := by
  let c : IdeleClassGroup K :=
    QuotientGroup.mk' (IdeleGroup.principalSubgroup K)
      (IdeleGroup.finitePrimeIdele v)
  have hgeo := rayClassFieldGaloisEquivRayClassGroup_symm_mk m c
  have hnormprime :
      Reciprocity.arithmeticGlobalNormResidueMonoidHom K (rayClassField K m) c =
        arithmeticFinitePlacePrimeArtin (K := K) (L := rayClassField K m) v := by
    simpa only [c, arithmeticFinitePlacePrimeArtin, MonoidHom.comp_apply] using
      DFunLike.congr_fun
        (Reciprocity.arithmeticGlobalNormResidueMonoidHom_comp_ideleClassQuotient_eq_globalArtin
          (K := K) (L := rayClassField K m))
        (IdeleGroup.finitePrimeIdele v)
  change (rayClassFieldGaloisEquivRayClassGroup (K := K) m).symm
      ((QuotientGroup.mk' m.congruenceSubgroup c)⁻¹) = _
  rw [map_inv, hgeo]
  exact (Reciprocity.arithmeticGlobalNormResidueMonoidHom_apply
    K (rayClassField K m) c).symm.trans hnormprime

open scoped Classical in
private theorem rayClassSubgroup_restrict_transport
    {K : Type} [Field K] [NumberField K]
    (m : RayClass.Modulus K)
    (H : Subgroup (RayClass.RayClassGroup m))
    (σ : rayClassField K m ≃ₐ[K] rayClassField K m) :
    let F := rayClassSubgroupFixedField (K := K) m H
    let E := rayClassSubgroupSubextension (K := K) m H
    let α : F ≃ₐ[K] E :=
      IntermediateField.equivMap F (rayClassFieldEmbedding K m)
    let f : E →ₐ[K] rayClassField K m :=
      (IntermediateField.val F).comp α.symm.toAlgHom
    let _ : Algebra E (rayClassField K m) := f.toRingHom.toAlgebra
    let _ : IsScalarTower K E (rayClassField K m) :=
      IsScalarTower.of_algebraMap_eq fun x => (f.commutes x).symm
    (AlgEquiv.autCongr α) (AlgEquiv.restrictNormalHom F σ) =
      AlgEquiv.restrictNormalHom E σ := by
  let F := rayClassSubgroupFixedField (K := K) m H
  let L := rayClassField K m
  let E := rayClassSubgroupSubextension (K := K) m H
  let α : F ≃ₐ[K] E :=
    IntermediateField.equivMap F (rayClassFieldEmbedding K m)
  let f : E →ₐ[K] L :=
    (IntermediateField.val F).comp α.symm.toAlgHom
  let : Algebra E L := f.toRingHom.toAlgebra
  let : IsScalarTower K E L :=
    IsScalarTower.of_algebraMap_eq fun x => (f.commutes x).symm
  change (AlgEquiv.autCongr α) (AlgEquiv.restrictNormalHom F σ) =
    AlgEquiv.restrictNormalHom E σ
  apply AlgEquiv.ext
  intro x
  apply f.injective
  change f (α ((AlgEquiv.restrictNormalHom F σ) (α.symm x))) =
    f ((AlgEquiv.restrictNormalHom E σ) x)
  calc
    f (α ((AlgEquiv.restrictNormalHom F σ) (α.symm x))) =
        F.val ((AlgEquiv.restrictNormalHom F σ) (α.symm x)) := by
          simp [f]
    _ = σ (F.val (α.symm x)) :=
      AlgEquiv.restrictNormalHom_apply F σ (α.symm x)
    _ = f ((AlgEquiv.restrictNormalHom E σ) x) := by
      exact (AlgEquiv.restrictNormal_commutes σ E x).symm

open scoped Classical in
/-- The fixed-field ray-class Artin map sends the ray class of an ordinary
prime idèle to the arithmetic global Artin element of the fixed field. -/
theorem rayClassSubgroupArtin_finitePrimeIdele
    {K : Type} [Field K] [NumberField K]
    (m : RayClass.Modulus K)
    (H : Subgroup (RayClass.RayClassGroup m))
    (v : HeightOneSpectrum (𝓞 K)) :
    rayClassSubgroupArtin (K := K) m H
        (QuotientGroup.mk' m.congruenceSubgroup
          (QuotientGroup.mk' (IdeleGroup.principalSubgroup K)
            (IdeleGroup.finitePrimeIdele v))) =
      arithmeticFinitePlacePrimeArtin (K := K)
        (L := rayClassSubgroupSubextension (K := K) m H) v := by
  let F := rayClassSubgroupFixedField (K := K) m H
  let L := rayClassField K m
  let E := rayClassSubgroupSubextension (K := K) m H
  let α : F ≃ₐ[K] E :=
    IntermediateField.equivMap F (rayClassFieldEmbedding K m)
  let e := rayClassFieldGaloisEquivRayClassGroup (K := K) m
  let c : IdeleClassGroup K :=
    QuotientGroup.mk' (IdeleGroup.principalSubgroup K)
      (IdeleGroup.finitePrimeIdele v)
  let q : RayClass.RayClassGroup m :=
    QuotientGroup.mk' m.congruenceSubgroup c
  let f : E →ₐ[K] L :=
    (IntermediateField.val F).comp α.symm.toAlgHom
  let : Algebra E L := f.toRingHom.toAlgebra
  let : IsScalarTower K E L :=
    IsScalarTower.of_algebraMap_eq fun x => (f.commutes x).symm
  have hprime :
      e.symm q⁻¹ = arithmeticFinitePlacePrimeArtin (K := K) (L := L) v := by
    simpa only [e, q, c, L] using
      rayClassField_arithmeticFinitePlacePrimeArtin m v
  change (AlgEquiv.autCongr α)
      (AlgEquiv.restrictNormalHom F (e.symm q⁻¹)) =
    arithmeticFinitePlacePrimeArtin (K := K) (L := E) v
  calc
    (AlgEquiv.autCongr α)
        (AlgEquiv.restrictNormalHom F (e.symm q⁻¹)) =
        (AlgEquiv.autCongr α)
          (AlgEquiv.restrictNormalHom F
            (arithmeticFinitePlacePrimeArtin (K := K) (L := L) v)) :=
      congrArg (fun σ : L ≃ₐ[K] L =>
        (AlgEquiv.autCongr α) (AlgEquiv.restrictNormalHom F σ)) hprime
    _ = AlgEquiv.restrictNormalHom E
          (arithmeticFinitePlacePrimeArtin (K := K) (L := L) v) :=
      rayClassSubgroup_restrict_transport m H
        (arithmeticFinitePlacePrimeArtin (K := K) (L := L) v)
    _ = arithmeticFinitePlacePrimeArtin (K := K) (L := E) v :=
      arithmeticFinitePlacePrimeArtin_restrict_tower K L E v

end GlobalClassFields
end GlobalClassFieldTheory
