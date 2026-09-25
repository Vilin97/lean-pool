/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.CyclotomicIdeleClassValuation
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.InfiniteGlobalArtin
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.MaximalUnramifiedReciprocity
/-!
# Cyclotomic Artin coordinates over abstract fixed fields

The cyclotomic degree datum on the rational absolute Galois group has
an actual maximal-unramified field over every finite abstract fixed
field.  This file identifies its genuine Galois group with
`Multiplicative ZHat`, using the normalized degree map, and supplies
the abelian Galois structure needed by the actual infinite global
Artin homomorphism.

These constructions are the source side of the comparison between
abstract finite reciprocity and the chosen local-factor product.  No
reciprocity comparison is assumed in their definitions.
-/

@[expose] public section

open scoped IsMulCommutative NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open ClassFormation
open KummerTheory

/-- Keep this module on the rational algebra structures used by the
cyclotomic fixed-field API.  Generic intermediate-field instances are
propositionally equal here but not definitionally interchangeable. -/
noncomputable local instance
    cyclotomicAbstractFixedFieldArtinSeparableClosureAlgebra :
    Algebra ℚ (SeparableClosure ℚ) :=
  DivisionRing.toRatAlgebra

/-- The rational cyclotomic field uses the canonical rational algebra structure of a division
ring. -/
noncomputable local instance
    cyclotomicAbstractFixedFieldArtinCyclotomicZHatFieldAlgebra :
    Algebra ℚ rationalCyclotomicZHatField :=
  DivisionRing.toRatAlgebra

/-- Cyclotomic field inertia is contained in the original abstract
field subgroup. -/
theorem rationalCyclotomicFieldInertia_le
    (H : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :
    (rationalCyclotomicDegreeData.fieldInertia H).toSubgroup ≤
      H.toSubgroup := by
  intro σ hσ
  exact hσ.1

/-- Viewing cyclotomic field inertia inside its ambient field subgroup
gives exactly the kernel of normalized degree. -/
theorem extensionSubgroup_rationalCyclotomicFieldInertia
    (H : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :
    CyclicCohomology.extensionSubgroup H
        (rationalCyclotomicDegreeData.fieldInertia H)
        (rationalCyclotomicFieldInertia_le H) =
      rationalCyclotomicDegreeData.fieldInertiaWithin H := by
  ext σ
  rw [
    mem_extensionSubgroup_iff,
    rationalCyclotomicDegreeData.mem_fieldInertiaWithin_iff,
    rationalCyclotomicDegreeData.mem_fieldInertia_iff]
  exact and_iff_right σ.2

/-- The actual Galois group of the cyclotomic maximal-unramified
extension of an abstract fixed field, in its normalized `ZHat`
coordinate. -/
noncomputable def abstractFixedFieldCyclotomicGalEquivZHat
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :
    let hI :=
      rationalCyclotomicFieldInertia_le H.field
    Gal(LocalClassFieldTheory.abstractRelativeFixedField
          ℚ (SeparableClosure ℚ) hI/LocalClassFieldTheory.abstractFixedField
          ℚ (SeparableClosure ℚ) H.field) ≃*
      Multiplicative ZHat := by
  let hI :=
    rationalCyclotomicFieldInertia_le H.field
  let hnormal :
      (CyclicCohomology.extensionSubgroup H.field
        (rationalCyclotomicDegreeData.fieldInertia H.field)
        hI).Normal := by
    rw [extensionSubgroup_rationalCyclotomicFieldInertia]
    infer_instance
  let qField :
      H.field.toSubgroup ⧸
          CyclicCohomology.extensionSubgroup H.field
            (rationalCyclotomicDegreeData.fieldInertia H.field)
            hI ≃*
        Gal(LocalClassFieldTheory.abstractRelativeFixedField
            ℚ (SeparableClosure ℚ) hI/LocalClassFieldTheory.abstractFixedField
            ℚ (SeparableClosure ℚ) H.field) :=
    LocalClassFieldTheory.abstractExtensionQuotientEquivGaloisGroup
      ℚ (SeparableClosure ℚ) H.field
      (rationalCyclotomicDegreeData.fieldInertia H.field)
      hI hnormal
  let qInertia :
      H.field.toSubgroup ⧸
          CyclicCohomology.extensionSubgroup H.field
            (rationalCyclotomicDegreeData.fieldInertia H.field)
            hI ≃*
        H.field.toSubgroup ⧸
          rationalCyclotomicDegreeData.fieldInertiaWithin H.field :=
    QuotientGroup.quotientMulEquivOfEq
      (extensionSubgroup_rationalCyclotomicFieldInertia H.field)
  exact
    qField.symm.trans
      (qInertia.trans
        (rationalCyclotomicDegreeData.maximalUnramifiedDegreeEquiv
          (H.toFiniteResidueAbstractField
            rationalCyclotomicDegreeData)))

/-- On an absolute-Galois representative fixing the lower field, the
actual cyclotomic Galois coordinate is its normalized degree. -/
@[simp]
theorem abstractFixedFieldCyclotomicGalEquivZHat_extensionClass
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (σ : H.field.toSubgroup) :
    let hI :=
      rationalCyclotomicFieldInertia_le H.field
    let hnormal :
        (CyclicCohomology.extensionSubgroup H.field
          (rationalCyclotomicDegreeData.fieldInertia H.field)
          hI).Normal := by
      rw [extensionSubgroup_rationalCyclotomicFieldInertia]
      infer_instance
    abstractFixedFieldCyclotomicGalEquivZHat H
        (LocalClassFieldTheory.abstractExtensionQuotientEquivGaloisGroup
          ℚ (SeparableClosure ℚ) H.field
          (rationalCyclotomicDegreeData.fieldInertia H.field)
          hI hnormal
          (QuotientGroup.mk σ)) =
      rationalCyclotomicDegreeData.normalizedDegree
        (H.toFiniteResidueAbstractField
          rationalCyclotomicDegreeData) σ := by
  let hI :=
    rationalCyclotomicFieldInertia_le H.field
  let hnormal :
      (CyclicCohomology.extensionSubgroup H.field
        (rationalCyclotomicDegreeData.fieldInertia H.field)
        hI).Normal := by
    rw [extensionSubgroup_rationalCyclotomicFieldInertia]
    infer_instance
  let qField :=
    LocalClassFieldTheory.abstractExtensionQuotientEquivGaloisGroup
      ℚ (SeparableClosure ℚ) H.field
      (rationalCyclotomicDegreeData.fieldInertia H.field)
      hI hnormal
  change
    (rationalCyclotomicDegreeData.maximalUnramifiedDegreeEquiv
      (H.toFiniteResidueAbstractField
        rationalCyclotomicDegreeData))
      (QuotientGroup.quotientMulEquivOfEq
        (extensionSubgroup_rationalCyclotomicFieldInertia H.field)
        (qField.symm (qField (QuotientGroup.mk σ)))) =
      rationalCyclotomicDegreeData.normalizedDegree
        (H.toFiniteResidueAbstractField
          rationalCyclotomicDegreeData) σ
  rw [qField.symm_apply_apply]
  rfl

/-- Quotient-level evaluation of the actual cyclotomic Galois
coordinate. -/
@[simp]
theorem abstractFixedFieldCyclotomicGalEquivZHat_quotientClass
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (q :
      H.field.toSubgroup ⧸
        rationalCyclotomicDegreeData.fieldInertiaWithin H.field) :
    let hI :=
      rationalCyclotomicFieldInertia_le H.field
    let hnormal :
        (CyclicCohomology.extensionSubgroup H.field
          (rationalCyclotomicDegreeData.fieldInertia H.field)
          hI).Normal := by
      rw [extensionSubgroup_rationalCyclotomicFieldInertia]
      infer_instance
    let qInertia :
        H.field.toSubgroup ⧸
            CyclicCohomology.extensionSubgroup H.field
              (rationalCyclotomicDegreeData.fieldInertia H.field)
              hI ≃*
          H.field.toSubgroup ⧸
            rationalCyclotomicDegreeData.fieldInertiaWithin H.field :=
      QuotientGroup.quotientMulEquivOfEq
        (extensionSubgroup_rationalCyclotomicFieldInertia H.field)
    abstractFixedFieldCyclotomicGalEquivZHat H
        (LocalClassFieldTheory.abstractExtensionQuotientEquivGaloisGroup
          ℚ (SeparableClosure ℚ) H.field
          (rationalCyclotomicDegreeData.fieldInertia H.field)
          hI hnormal
          (qInertia.symm q)) =
      rationalCyclotomicDegreeData.maximalUnramifiedDegreeEquiv
        (H.toFiniteResidueAbstractField
          rationalCyclotomicDegreeData) q := by
  let hI :=
    rationalCyclotomicFieldInertia_le H.field
  let hnormal :
      (CyclicCohomology.extensionSubgroup H.field
        (rationalCyclotomicDegreeData.fieldInertia H.field)
        hI).Normal := by
    rw [extensionSubgroup_rationalCyclotomicFieldInertia]
    infer_instance
  let qField :=
    LocalClassFieldTheory.abstractExtensionQuotientEquivGaloisGroup
      ℚ (SeparableClosure ℚ) H.field
      (rationalCyclotomicDegreeData.fieldInertia H.field)
      hI hnormal
  let qInertia :
      H.field.toSubgroup ⧸
          CyclicCohomology.extensionSubgroup H.field
            (rationalCyclotomicDegreeData.fieldInertia H.field)
            hI ≃*
        H.field.toSubgroup ⧸
          rationalCyclotomicDegreeData.fieldInertiaWithin H.field :=
    QuotientGroup.quotientMulEquivOfEq
      (extensionSubgroup_rationalCyclotomicFieldInertia H.field)
  change
    (rationalCyclotomicDegreeData.maximalUnramifiedDegreeEquiv
      (H.toFiniteResidueAbstractField
        rationalCyclotomicDegreeData))
      (qInertia
        (qField.symm
          (qField (qInertia.symm q)))) =
      rationalCyclotomicDegreeData.maximalUnramifiedDegreeEquiv
        (H.toFiniteResidueAbstractField
          rationalCyclotomicDegreeData) q
  rw [qField.symm_apply_apply, qInertia.apply_symm_apply]

/-- The extension fixed by cyclotomic field inertia is an actual
abelian Galois extension of the lower abstract fixed field. -/
theorem abstractFixedFieldCyclotomic_isAbelianGalois
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :
    let hI :=
      rationalCyclotomicFieldInertia_le H.field
    IsAbelianGalois
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field)
      (LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) hI) := by
  let hI :=
    rationalCyclotomicFieldInertia_le H.field
  let hnormal :
      (CyclicCohomology.extensionSubgroup H.field
        (rationalCyclotomicDegreeData.fieldInertia H.field)
        hI).Normal := by
    rw [extensionSubgroup_rationalCyclotomicFieldInertia]
    infer_instance
  let : IsGalois
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field)
      (LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) hI) :=
    LocalClassFieldTheory.abstractRelativeFixedField_isGalois
      ℚ (SeparableClosure ℚ) H.field
      (rationalCyclotomicDegreeData.fieldInertia H.field)
      hI hnormal
  let e :=
    abstractFixedFieldCyclotomicGalEquivZHat H
  exact
    { is_comm.comm := by
        intro σ τ
        apply e.injective
        simpa only [map_mul] using mul_comm (e σ) (e τ) }

/-- The rational cyclotomic `ZHat`-field embedded in the actual
maximal-unramified compositum of an abstract fixed field. -/
noncomputable def
    rationalCyclotomicZHatFieldEmbeddingInAbstractFixedFieldCompositum
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :
    let hI :=
      rationalCyclotomicFieldInertia_le H.field
    rationalCyclotomicZHatField →ₐ[ℚ]
      LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) hI := by
  let hI :=
    rationalCyclotomicFieldInertia_le H.field
  let J :=
    LocalClassFieldTheory.abstractFixedField
      ℚ (SeparableClosure ℚ)
      (rationalCyclotomicDegreeData.fieldInertia H.field)
  have hTJ :
      rationalCyclotomicZHatField ≤ J := by
    change
      rationalCyclotomicZHatField ≤
        LocalClassFieldTheory.abstractFixedField
          ℚ (SeparableClosure ℚ)
          (rationalCyclotomicDegreeData.fieldInertia H.field)
    rw [
      rationalCyclotomicDegreeData_fixedField_fieldInertia]
    exact le_sup_right
  exact IntermediateField.inclusion hTJ

noncomputable instance
    abstractFixedFieldCyclotomicCompositumAlgebra
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :
    let hI :=
      rationalCyclotomicFieldInertia_le H.field
    Algebra rationalCyclotomicZHatField
      (LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) hI) :=
  ((rationalCyclotomicZHatFieldEmbeddingInAbstractFixedFieldCompositum
    H).toRingHom).toAlgebra

instance abstractFixedFieldCyclotomicCompositum_scalarTower
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :
    let hI :=
      rationalCyclotomicFieldInertia_le H.field
    IsScalarTower ℚ rationalCyclotomicZHatField
      (LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) hI) :=
  IsScalarTower.of_algebraMap_eq'
    ((rationalCyclotomicZHatFieldEmbeddingInAbstractFixedFieldCompositum
      H).comp_algebraMap).symm

instance abstractFixedFieldCyclotomicCompositum_baseScalarTower
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :
    let hI :=
      rationalCyclotomicFieldInertia_le H.field
    IsScalarTower ℚ
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field)
      (LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) hI) := by
  let hI :=
    rationalCyclotomicFieldInertia_le H.field
  apply IsScalarTower.of_algebraMap_eq
  intro x
  apply Subtype.ext
  rfl

/-- Restriction from the actual maximal-unramified compositum of an
abstract fixed field to the rational cyclotomic factor. -/
noncomputable def abstractFixedFieldCyclotomicRestriction
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :
    let hI :=
      rationalCyclotomicFieldInertia_le H.field
    Gal(LocalClassFieldTheory.abstractRelativeFixedField
          ℚ (SeparableClosure ℚ) hI/LocalClassFieldTheory.abstractFixedField
          ℚ (SeparableClosure ℚ) H.field) →*
      Gal(rationalCyclotomicZHatField/ℚ) := by
  let hI :=
    rationalCyclotomicFieldInertia_le H.field
  exact
    IntermediateField.restrictRestrictAlgEquivMapHom
      ℚ rationalCyclotomicZHatField
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field)
      (LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) hI)

/-- On a quotient representative, cyclotomic restriction of the
actual relative automorphism is ordinary restriction of the same
ambient absolute-Galois automorphism. -/
theorem cyclotomicAbstractFixedFieldArtin_cyclotomicZHatFieldNormal :
    Normal ℚ rationalCyclotomicZHatField :=
  rationalCyclotomicZHatField_isNormal

attribute [local instance] cyclotomicAbstractFixedFieldArtin_cyclotomicZHatFieldNormal

@[simp]
theorem abstractFixedFieldCyclotomicRestriction_extensionClass
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (σ : H.field.toSubgroup) :
    let hI :=
      rationalCyclotomicFieldInertia_le H.field
    let hnormal :
        (CyclicCohomology.extensionSubgroup H.field
          (rationalCyclotomicDegreeData.fieldInertia H.field)
          hI).Normal := by
      rw [extensionSubgroup_rationalCyclotomicFieldInertia]
      infer_instance
    abstractFixedFieldCyclotomicRestriction H
        (LocalClassFieldTheory.abstractExtensionQuotientEquivGaloisGroup
          ℚ (SeparableClosure ℚ) H.field
          (rationalCyclotomicDegreeData.fieldInertia H.field)
          hI hnormal
          (QuotientGroup.mk σ)) =
      AlgEquiv.restrictNormalHom
        rationalCyclotomicZHatField σ.1 := by
  let hI :=
    rationalCyclotomicFieldInertia_le H.field
  let hnormal :
      (CyclicCohomology.extensionSubgroup H.field
        (rationalCyclotomicDegreeData.fieldInertia H.field)
        hI).Normal := by
    rw [extensionSubgroup_rationalCyclotomicFieldInertia]
    infer_instance
  let τ :=
    LocalClassFieldTheory.abstractExtensionQuotientEquivGaloisGroup
      ℚ (SeparableClosure ℚ) H.field
      (rationalCyclotomicDegreeData.fieldInertia H.field)
      hI hnormal
      (QuotientGroup.mk'
        (CyclicCohomology.extensionSubgroup H.field
          (rationalCyclotomicDegreeData.fieldInertia H.field) hI)
        σ)
  apply AlgEquiv.ext
  intro x
  apply Subtype.ext
  let U :=
    LocalClassFieldTheory.abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) hI
  have hrestrict :
      algebraMap rationalCyclotomicZHatField U
          ((abstractFixedFieldCyclotomicRestriction H τ) x) =
        τ (algebraMap rationalCyclotomicZHatField U x) := by
    change
      algebraMap rationalCyclotomicZHatField U
          ((AlgEquiv.restrictNormal
            (MulSemiringAction.toAlgEquiv ℚ U τ)
            rationalCyclotomicZHatField) x) =
        (MulSemiringAction.toAlgEquiv ℚ U τ)
          (algebraMap rationalCyclotomicZHatField U x)
    exact
      AlgEquiv.restrictNormal_commutes
        (MulSemiringAction.toAlgEquiv ℚ U τ)
        rationalCyclotomicZHatField x
  have halgebraMap_eq_embedding
      (z : rationalCyclotomicZHatField) :
      algebraMap rationalCyclotomicZHatField U z =
        (rationalCyclotomicZHatFieldEmbeddingInAbstractFixedFieldCompositum
          H z : U) := by
    rfl
  have hembedding_coe
      (z : rationalCyclotomicZHatField) :
      (((rationalCyclotomicZHatFieldEmbeddingInAbstractFixedFieldCompositum
          H z : U) : SeparableClosure ℚ)) =
        (z : SeparableClosure ℚ) := by
    rfl
  have halgebraMap_coe
      (z : rationalCyclotomicZHatField) :
      ((algebraMap rationalCyclotomicZHatField U z : U) :
          SeparableClosure ℚ) =
        (z : SeparableClosure ℚ) := by
    rw [halgebraMap_eq_embedding]
    exact hembedding_coe z
  have hambient :=
    LocalClassFieldTheory.abstractExtensionQuotientEquivGaloisGroup_mk_apply_val
        ℚ (SeparableClosure ℚ) H.field
        (rationalCyclotomicDegreeData.fieldInertia H.field)
        hI hnormal σ
        (rationalCyclotomicZHatFieldEmbeddingInAbstractFixedFieldCompositum
          H x)
  calc
    (((abstractFixedFieldCyclotomicRestriction H τ) x :
        rationalCyclotomicZHatField) :
        SeparableClosure ℚ) =
        ((τ
          (rationalCyclotomicZHatFieldEmbeddingInAbstractFixedFieldCompositum
            H x) :
          LocalClassFieldTheory.abstractRelativeFixedField
            ℚ (SeparableClosure ℚ) hI) :
          SeparableClosure ℚ) := by
      calc
        (((abstractFixedFieldCyclotomicRestriction H τ) x :
            rationalCyclotomicZHatField) : SeparableClosure ℚ) =
            ((algebraMap rationalCyclotomicZHatField U
              ((abstractFixedFieldCyclotomicRestriction H τ) x) : U) :
              SeparableClosure ℚ) :=
          (halgebraMap_coe
            ((abstractFixedFieldCyclotomicRestriction H τ) x)).symm
        _ = ((τ (algebraMap rationalCyclotomicZHatField U x) : U) :
            SeparableClosure ℚ) :=
          congrArg (fun y : U => (y : SeparableClosure ℚ)) hrestrict
        _ = ((τ
            (rationalCyclotomicZHatFieldEmbeddingInAbstractFixedFieldCompositum
              H x) : U) : SeparableClosure ℚ) := by
          rw [halgebraMap_eq_embedding]
    _ = σ.1 (x : SeparableClosure ℚ) := by
      calc
        ((τ
            (rationalCyclotomicZHatFieldEmbeddingInAbstractFixedFieldCompositum
              H x) : U) : SeparableClosure ℚ) =
            σ.1
              ((rationalCyclotomicZHatFieldEmbeddingInAbstractFixedFieldCompositum
                H x : U) : SeparableClosure ℚ) := by
          simpa only [τ, U] using hambient.symm
        _ = σ.1 (x : SeparableClosure ℚ) := by
          rw [hembedding_coe]
    _ =
        (((AlgEquiv.restrictNormalHom
          rationalCyclotomicZHatField σ.1) x :
          rationalCyclotomicZHatField) :
          SeparableClosure ℚ) := by
      exact
        (AlgEquiv.restrictNormal_commutes
          σ.1 rationalCyclotomicZHatField x).symm

/-- Raw cyclotomic restriction is residue-degree multiplication of
the normalized actual Galois coordinate. -/
theorem
    abstractFixedFieldCyclotomicRestriction_coordinate
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (τ :
      Gal(LocalClassFieldTheory.abstractRelativeFixedField
          ℚ (SeparableClosure ℚ)
          (rationalCyclotomicFieldInertia_le H.field)/LocalClassFieldTheory.abstractFixedField
          ℚ (SeparableClosure ℚ) H.field)) :
    Multiplicative.toAdd
        (rationalCyclotomicZHatFieldGalEquivZHat
          (abstractFixedFieldCyclotomicRestriction H τ)) =
      (H.residueDegree rationalCyclotomicDegreeData : ℕ) •
        Multiplicative.toAdd
          (abstractFixedFieldCyclotomicGalEquivZHat H τ) := by
  let hI :=
    rationalCyclotomicFieldInertia_le H.field
  let hnormal :
      (CyclicCohomology.extensionSubgroup H.field
        (rationalCyclotomicDegreeData.fieldInertia H.field)
        hI).Normal := by
    rw [extensionSubgroup_rationalCyclotomicFieldInertia]
    infer_instance
  let qField :=
    LocalClassFieldTheory.abstractExtensionQuotientEquivGaloisGroup
      ℚ (SeparableClosure ℚ) H.field
      (rationalCyclotomicDegreeData.fieldInertia H.field)
      hI hnormal
  obtain ⟨q, rfl⟩ := qField.surjective τ
  refine Quotient.inductionOn' q ?_
  intro σ
  rw [
    abstractFixedFieldCyclotomicRestriction_extensionClass,
    abstractFixedFieldCyclotomicGalEquivZHat_extensionClass]
  exact
    (rationalCyclotomicDegreeData.residueDegree_nsmul_normalizedDegree
        (H.toFiniteResidueAbstractField
          rationalCyclotomicDegreeData) σ).symm

/-- The canonical compositum of an abstract fixed field with a finite
layer of the rational cyclotomic `ZHat`-extension. -/
def abstractFixedFieldCyclotomicFiniteCompositum
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    IntermediateField ℚ (SeparableClosure ℚ) :=
  LocalClassFieldTheory.abstractFixedField
      ℚ (SeparableClosure ℚ) H.field ⊔
    IntermediateField.lift E.toIntermediateField

/-- The compositum of the fixed base with a finite cyclotomic layer has finite rational degree.
-/
theorem abstractFixedFieldCyclotomicFiniteCompositum_finiteDimensional
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    FiniteDimensional ℚ
      (abstractFixedFieldCyclotomicFiniteCompositum H E) := by
  let F :=
    LocalClassFieldTheory.abstractFixedField
      ℚ (SeparableClosure ℚ) H.field
  let : FiniteDimensional ℚ F :=
    LocalClassFieldTheory.abstractFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) H.field H.finite
  let : FiniteDimensional ℚ
      (IntermediateField.lift E.toIntermediateField) :=
    ((IntermediateField.liftAlgEquiv
      E.toIntermediateField).toLinearEquiv).finiteDimensional
  exact IntermediateField.finiteDimensional_sup
    F (IntermediateField.lift E.toIntermediateField)

attribute [instance] abstractFixedFieldCyclotomicFiniteCompositum_finiteDimensional

/-- The compositum of the fixed base with a finite cyclotomic layer is a number field. -/
theorem abstractFixedFieldCyclotomicFiniteCompositum_numberField
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    NumberField
      (abstractFixedFieldCyclotomicFiniteCompositum H E) :=
  NumberField.of_module_finite ℚ
    (abstractFixedFieldCyclotomicFiniteCompositum H E)

attribute [instance] abstractFixedFieldCyclotomicFiniteCompositum_numberField

/-- The lower abstract fixed field embedded into its finite
cyclotomic compositum. -/
noncomputable def
    abstractFixedFieldCyclotomicFiniteCompositumBaseEmbedding
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field →ₐ[ℚ]
      abstractFixedFieldCyclotomicFiniteCompositum H E :=
  IntermediateField.inclusion
    (show
      LocalClassFieldTheory.abstractFixedField
          ℚ (SeparableClosure ℚ) H.field ≤
        abstractFixedFieldCyclotomicFiniteCompositum H E from
      le_sup_left)

/-- The fixed field attached to a finite abstract field is a number
field.  Keeping this as the single file-local instance makes it
available while later theorem binders are elaborated. -/
theorem abstractFixedFieldCyclotomic_numberField
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :
    NumberField
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field) := by
  let : FiniteDimensional ℚ
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field) :=
    LocalClassFieldTheory.abstractFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) H.field H.finite
  exact
    NumberField.of_module_finite ℚ
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field)

attribute [local instance] abstractFixedFieldCyclotomic_numberField

/-- A finite rational cyclotomic layer embedded into its compositum
with the abstract fixed field. -/
noncomputable def
    abstractFixedFieldCyclotomicFiniteCompositumLayerEmbedding
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    E →ₐ[ℚ]
      abstractFixedFieldCyclotomicFiniteCompositum H E :=
  (IntermediateField.inclusion
      (show
        IntermediateField.lift E.toIntermediateField ≤
          abstractFixedFieldCyclotomicFiniteCompositum H E from
        le_sup_right)).comp
    (IntermediateField.liftAlgEquiv E.toIntermediateField).toAlgHom

noncomputable instance
    abstractFixedFieldCyclotomicFiniteCompositumBaseAlgebra
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    Algebra
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field)
      (abstractFixedFieldCyclotomicFiniteCompositum H E) :=
  RingHom.toAlgebra
    (AlgHom.toRingHom
      (abstractFixedFieldCyclotomicFiniteCompositumBaseEmbedding H E))

noncomputable instance
    abstractFixedFieldCyclotomicFiniteCompositumLayerAlgebra
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    Algebra E
      (abstractFixedFieldCyclotomicFiniteCompositum H E) :=
  RingHom.toAlgebra
    (AlgHom.toRingHom
      (abstractFixedFieldCyclotomicFiniteCompositumLayerEmbedding H E))

/-- The finite-layer action induced by its explicit embedding into the
finite compositum. -/
noncomputable instance
    abstractFixedFieldCyclotomicFiniteCompositumLayerSMul
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    SMul E
      (abstractFixedFieldCyclotomicFiniteCompositum H E) :=
  Algebra.toSMul
    (self :=
      abstractFixedFieldCyclotomicFiniteCompositumLayerAlgebra H E)

/-- The compositum's rational scalars factor through the fixed base embedding. -/
theorem abstractFixedFieldCyclotomicFiniteCompositum_baseScalarTower
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    IsScalarTower ℚ
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field)
      (abstractFixedFieldCyclotomicFiniteCompositum H E) :=
  IsScalarTower.of_algebraMap_eq'
    (AlgHom.comp_algebraMap
      (abstractFixedFieldCyclotomicFiniteCompositumBaseEmbedding H E)).symm

attribute [instance] abstractFixedFieldCyclotomicFiniteCompositum_baseScalarTower

/-- The compositum's rational scalars factor through its finite cyclotomic layer embedding. -/
theorem abstractFixedFieldCyclotomicFiniteCompositum_layerScalarTower
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    IsScalarTower ℚ E
      (abstractFixedFieldCyclotomicFiniteCompositum H E) :=
  IsScalarTower.of_algebraMap_eq'
    (AlgHom.comp_algebraMap
      (abstractFixedFieldCyclotomicFiniteCompositumLayerEmbedding H E)).symm

attribute [instance] abstractFixedFieldCyclotomicFiniteCompositum_layerScalarTower

/-- Inclusion of the finite cyclotomic compositum into the actual
maximal-unramified compositum. -/
noncomputable def
    abstractFixedFieldCyclotomicFiniteCompositumInclusion
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    let hI :=
      rationalCyclotomicFieldInertia_le H.field
    abstractFixedFieldCyclotomicFiniteCompositum H E →ₐ[ℚ]
      LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) hI := by
  let hI :=
    rationalCyclotomicFieldInertia_le H.field
  let J :=
    LocalClassFieldTheory.abstractFixedField
      ℚ (SeparableClosure ℚ)
      (rationalCyclotomicDegreeData.fieldInertia H.field)
  have hle :
      abstractFixedFieldCyclotomicFiniteCompositum H E ≤ J := by
    dsimp only [J]
    rw [
      rationalCyclotomicDegreeData_fixedField_fieldInertia H.field]
    exact
      sup_le_sup le_rfl
        (IntermediateField.lift_le E.toIntermediateField)
  exact IntermediateField.inclusion hle

/-- The same finite-compositum inclusion over the lower abstract fixed
field. -/
noncomputable def
    abstractFixedFieldCyclotomicFiniteCompositumInclusionOverBase
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    let hI :=
      rationalCyclotomicFieldInertia_le H.field
    abstractFixedFieldCyclotomicFiniteCompositum H E →ₐ[
      LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field]
      LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) hI := by
  let f :=
    abstractFixedFieldCyclotomicFiniteCompositumInclusion H E
  exact
    { f.toRingHom with
      commutes' := by
        intro x
        rfl }

/-- The finite cyclotomic compositum as an intermediate field of the
actual maximal-unramified extension. -/
noncomputable def abstractFixedFieldCyclotomicFiniteLayer
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    let hI :=
      rationalCyclotomicFieldInertia_le H.field
    IntermediateField
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field)
      (LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) hI) :=
  (abstractFixedFieldCyclotomicFiniteCompositumInclusionOverBase H E).fieldRange

/-- The base algebra on the finite field range, obtained from the
explicit base embedding followed by the field-range equivalence. -/
noncomputable instance
    abstractFixedFieldCyclotomicFiniteLayerBaseAlgebra
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    Algebra
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field)
      (abstractFixedFieldCyclotomicFiniteLayer H E) :=
  RingHom.toAlgebra
    ((AlgHom.toRingHom
      (AlgEquiv.toAlgHom
        (AlgHom.equivFieldRange
          (abstractFixedFieldCyclotomicFiniteCompositumInclusionOverBase
            H E)))).comp
      (AlgHom.toRingHom
        (abstractFixedFieldCyclotomicFiniteCompositumBaseEmbedding H E)))

/-- The scalar action belonging to the canonical base algebra on the
finite field range. -/
noncomputable instance
    abstractFixedFieldCyclotomicFiniteLayerBaseSMul
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    SMul
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field)
      (abstractFixedFieldCyclotomicFiniteLayer H E) :=
  Algebra.toSMul
    (self := abstractFixedFieldCyclotomicFiniteLayerBaseAlgebra H E)

/-- The module structure belonging to the canonical base algebra on
the finite field range. -/
noncomputable instance
    abstractFixedFieldCyclotomicFiniteLayerBaseModule
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    Module
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field)
      (abstractFixedFieldCyclotomicFiniteLayer H E) :=
  @Algebra.toModule
    (LocalClassFieldTheory.abstractFixedField
      ℚ (SeparableClosure ℚ) H.field)
    (abstractFixedFieldCyclotomicFiniteLayer H E)
    _ _
    (abstractFixedFieldCyclotomicFiniteLayerBaseAlgebra H E)

/-- The field-range equivalence rebuilt over the explicit base
algebras.  Its underlying ring equivalence is the canonical one. -/
noncomputable def
    abstractFixedFieldCyclotomicFiniteCompositumEquivFiniteLayer
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    abstractFixedFieldCyclotomicFiniteCompositum H E ≃ₐ[LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field]
      abstractFixedFieldCyclotomicFiniteLayer H E :=
  AlgEquiv.ofRingEquiv
    (f :=
      (AlgHom.equivFieldRange
        (abstractFixedFieldCyclotomicFiniteCompositumInclusionOverBase
          H E)).toRingEquiv)
    (fun _ => rfl)

/-- The image of the finite cyclotomic compositum has finite degree over the fixed base. -/
theorem abstractFixedFieldCyclotomicFiniteLayer_finiteDimensional
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    FiniteDimensional
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field)
      (abstractFixedFieldCyclotomicFiniteLayer H E) :=
  (abstractFixedFieldCyclotomicFiniteCompositumEquivFiniteLayer
    H E).toLinearEquiv.finiteDimensional

attribute [instance] abstractFixedFieldCyclotomicFiniteLayer_finiteDimensional

/-- The finite layer inside the relative fixed field is a number field. -/
theorem abstractFixedFieldCyclotomicFiniteLayer_numberField
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    NumberField
      (abstractFixedFieldCyclotomicFiniteLayer H E) :=
  NumberField.of_module_finite
    (LocalClassFieldTheory.abstractFixedField
      ℚ (SeparableClosure ℚ) H.field)
    (abstractFixedFieldCyclotomicFiniteLayer H E)

attribute [instance] abstractFixedFieldCyclotomicFiniteLayer_numberField

/-- The finite layer inside the relative fixed field is abelian Galois over the fixed base. -/
theorem abstractFixedFieldCyclotomicFiniteLayer_isAbelianGalois
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    IsAbelianGalois
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field)
      (abstractFixedFieldCyclotomicFiniteLayer H E) := by
  let hI :=
    rationalCyclotomicFieldInertia_le H.field
  let : IsAbelianGalois
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field)
      (LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) hI) :=
    abstractFixedFieldCyclotomic_isAbelianGalois H
  exact
    IsAbelianGalois.of_algHom
      ((abstractFixedFieldCyclotomicFiniteCompositumInclusionOverBase
          H E).comp
        (AlgEquiv.toAlgHom
          (AlgEquiv.symm
            (abstractFixedFieldCyclotomicFiniteCompositumEquivFiniteLayer
              H E))))

attribute [instance] abstractFixedFieldCyclotomicFiniteLayer_isAbelianGalois

/-- Rational scalars on the finite layer factor through its fixed base field. -/
theorem abstractFixedFieldCyclotomicFiniteLayer_baseScalarTower
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    IsScalarTower ℚ
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field)
      (abstractFixedFieldCyclotomicFiniteLayer H E) := by
  let hI :=
    rationalCyclotomicFieldInertia_le H.field
  apply IsScalarTower.of_algebraMap_eq
  intro x
  apply Subtype.ext
  change
    algebraMap ℚ
        (LocalClassFieldTheory.abstractRelativeFixedField
          ℚ (SeparableClosure ℚ) hI) x =
      algebraMap
        (LocalClassFieldTheory.abstractFixedField
          ℚ (SeparableClosure ℚ) H.field)
        (LocalClassFieldTheory.abstractRelativeFixedField
          ℚ (SeparableClosure ℚ) hI)
        (algebraMap ℚ
          (LocalClassFieldTheory.abstractFixedField
            ℚ (SeparableClosure ℚ) H.field) x)
  exact
    IsScalarTower.algebraMap_apply
      ℚ
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field)
      (LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) hI) x

attribute [instance] abstractFixedFieldCyclotomicFiniteLayer_baseScalarTower

/-- The finite rational layer embedded into its corresponding
intermediate field over the abstract fixed field. -/
noncomputable def
    abstractFixedFieldCyclotomicFiniteLayerEmbedding
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    E →ₐ[ℚ]
      abstractFixedFieldCyclotomicFiniteLayer H E := by
  exact
    (AlgEquiv.toAlgHom
      (AlgEquiv.restrictScalars ℚ
        (abstractFixedFieldCyclotomicFiniteCompositumEquivFiniteLayer
          H E))).comp
      (abstractFixedFieldCyclotomicFiniteCompositumLayerEmbedding H E)

noncomputable instance
    abstractFixedFieldCyclotomicFiniteLayerLayerAlgebra
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    Algebra E
      (abstractFixedFieldCyclotomicFiniteLayer H E) :=
  RingHom.toAlgebra
    (AlgHom.toRingHom
      (abstractFixedFieldCyclotomicFiniteLayerEmbedding H E))

/-- The finite-layer action on its actual image in the relative fixed
field. -/
noncomputable instance
    abstractFixedFieldCyclotomicFiniteLayerLayerSMul
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    SMul E
      (abstractFixedFieldCyclotomicFiniteLayer H E) :=
  Algebra.toSMul
    (self := abstractFixedFieldCyclotomicFiniteLayerLayerAlgebra H E)

/-- Rational scalars on the finite layer factor through its chosen cyclotomic field. -/
theorem abstractFixedFieldCyclotomicFiniteLayer_layerScalarTower
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    IsScalarTower ℚ E
      (abstractFixedFieldCyclotomicFiniteLayer H E) :=
  IsScalarTower.of_algebraMap_eq'
    (AlgHom.comp_algebraMap
      (abstractFixedFieldCyclotomicFiniteLayerEmbedding H E)).symm

attribute [instance] abstractFixedFieldCyclotomicFiniteLayer_layerScalarTower

/-- The finite cyclotomic layer as an object of the finite-Galois
inverse system of the actual maximal-unramified extension. -/
@[reducible]
noncomputable def
    abstractFixedFieldCyclotomicFiniteGaloisLayer
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    FiniteGaloisIntermediateField
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field)
      (LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ)
        (rationalCyclotomicFieldInertia_le H.field)) where
  toIntermediateField :=
    abstractFixedFieldCyclotomicFiniteLayer H E
  finiteDimensional :=
    abstractFixedFieldCyclotomicFiniteLayer_finiteDimensional H E
  isGalois :=
    (abstractFixedFieldCyclotomicFiniteLayer_isAbelianGalois H E).toIsGalois

/-- The explicit base algebra on a finite cyclotomic layer is the canonical
intermediate-field inclusion used by the finite Galois inverse system. -/
theorem abstractFixedFieldCyclotomicFiniteLayer_baseAlgebra_eq_algebra'
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    abstractFixedFieldCyclotomicFiniteLayerBaseAlgebra H E =
      (abstractFixedFieldCyclotomicFiniteGaloisLayer H E).algebra' := by
  apply Algebra.algebra_ext
  intro x
  apply Subtype.ext
  rfl

/-- The finite Galois layer uses its canonical inclusion into the full
relative fixed field for the upper scalar action. -/
theorem abstractFixedFieldCyclotomicFiniteGaloisLayer_scalarTower
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    IsScalarTower
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field)
      (abstractFixedFieldCyclotomicFiniteGaloisLayer H E).toIntermediateField
      (LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ)
        (rationalCyclotomicFieldInertia_le H.field)) := by
  let i :
      (abstractFixedFieldCyclotomicFiniteGaloisLayer
          H E).toIntermediateField →ₐ[
        LocalClassFieldTheory.abstractFixedField
          ℚ (SeparableClosure ℚ) H.field]
        LocalClassFieldTheory.abstractRelativeFixedField
          ℚ (SeparableClosure ℚ)
          (rationalCyclotomicFieldInertia_le H.field) :=
    { (abstractFixedFieldCyclotomicFiniteGaloisLayer
          H E).toIntermediateField.val.toRingHom with
      commutes' := by
        intro x
        rfl }
  exact
    IsScalarTower.of_algebraMap_eq'
      (AlgHom.comp_algebraMap i).symm

attribute [instance] abstractFixedFieldCyclotomicFiniteGaloisLayer_scalarTower

/-- The canonical inclusion of the finite cyclotomic layer into the
full abstract-fixed-field compositum. -/
private noncomputable def
    abstractFixedFieldCyclotomicFiniteLayerInclusion
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    abstractFixedFieldCyclotomicFiniteLayer H E →ₐ[
      LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field]
      LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ)
        (rationalCyclotomicFieldInertia_le H.field) :=
  IntermediateField.val
    (abstractFixedFieldCyclotomicFiniteLayer H E)

/-- The two embeddings of a finite rational cyclotomic layer into the
full abstract-fixed-field compositum agree. -/
private theorem
    abstractFixedFieldCyclotomicFiniteLayerEmbedding_inclusion
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField)
    (z : E) :
    abstractFixedFieldCyclotomicFiniteLayerInclusion H E
        (abstractFixedFieldCyclotomicFiniteLayerEmbedding H E z) =
      rationalCyclotomicZHatFieldEmbeddingInAbstractFixedFieldCompositum H
        (z : rationalCyclotomicZHatField) := by
  exact Subtype.ext rfl

/-- Restriction to `E` commutes pointwise with the restriction from the
full rational cyclotomic tower. -/
private theorem
    restrictNormalHom_abstractFixedFieldCyclotomicRestriction_apply
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField)
    [Normal ℚ E]
    (σ :
      Gal(LocalClassFieldTheory.abstractRelativeFixedField
          ℚ (SeparableClosure ℚ)
          (rationalCyclotomicFieldInertia_le H.field)/LocalClassFieldTheory.abstractFixedField
          ℚ (SeparableClosure ℚ) H.field))
    (z : E) :
    ((AlgEquiv.restrictNormalHom E
      (abstractFixedFieldCyclotomicRestriction H σ)) z :
        rationalCyclotomicZHatField) =
      (abstractFixedFieldCyclotomicRestriction H σ)
        (z : rationalCyclotomicZHatField) := by
  exact
    AlgEquiv.restrictNormal_commutes
      (abstractFixedFieldCyclotomicRestriction H σ) E z

/-- The raw cyclotomic restriction commutes with the canonical embedding
of the full rational cyclotomic tower. -/
private theorem
    abstractFixedFieldCyclotomicRestriction_embedding_apply
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (σ :
      Gal(LocalClassFieldTheory.abstractRelativeFixedField
          ℚ (SeparableClosure ℚ)
          (rationalCyclotomicFieldInertia_le H.field)/LocalClassFieldTheory.abstractFixedField
          ℚ (SeparableClosure ℚ) H.field))
    (z : rationalCyclotomicZHatField) :
    rationalCyclotomicZHatFieldEmbeddingInAbstractFixedFieldCompositum H
        (abstractFixedFieldCyclotomicRestriction H σ z) =
      σ
        (rationalCyclotomicZHatFieldEmbeddingInAbstractFixedFieldCompositum
          H z) := by
  let U :=
    LocalClassFieldTheory.abstractRelativeFixedField
      ℚ (SeparableClosure ℚ)
      (rationalCyclotomicFieldInertia_le H.field)
  exact
    AlgEquiv.restrictNormal_commutes
      (MulSemiringAction.toAlgEquiv ℚ U σ)
      rationalCyclotomicZHatField z

/-- Restriction to the finite compositum layer commutes with its
canonical inclusion into the full compositum. -/
private theorem
    restrictNormalHom_abstractFixedFieldCyclotomicFiniteLayer_apply
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField)
    [Normal
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field)
      (abstractFixedFieldCyclotomicFiniteLayer H E)]
    (σ :
      Gal(LocalClassFieldTheory.abstractRelativeFixedField
          ℚ (SeparableClosure ℚ)
          (rationalCyclotomicFieldInertia_le H.field)/LocalClassFieldTheory.abstractFixedField
          ℚ (SeparableClosure ℚ) H.field))
    (z : abstractFixedFieldCyclotomicFiniteLayer H E) :
    abstractFixedFieldCyclotomicFiniteLayerInclusion H E
        (AlgEquiv.restrictNormalHom
          (abstractFixedFieldCyclotomicFiniteLayer H E) σ z) =
      σ (abstractFixedFieldCyclotomicFiniteLayerInclusion H E z) := by
  let F :=
    LocalClassFieldTheory.abstractFixedField
      ℚ (SeparableClosure ℚ) H.field
  let U :=
    LocalClassFieldTheory.abstractRelativeFixedField
      ℚ (SeparableClosure ℚ)
      (rationalCyclotomicFieldInertia_le H.field)
  let P : IntermediateField F U :=
    abstractFixedFieldCyclotomicFiniteLayer H E
  exact
    AlgEquiv.restrictNormal_commutes
      (MulSemiringAction.toAlgEquiv F U σ) P z

/-- Restricting the finite-compositum action further to `E` commutes
with the explicit embedding of `E` into that finite layer. -/
private theorem
    abstractFixedFieldCyclotomicFiniteLayerEmbedding_restrict_apply
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField)
    [Normal ℚ E]
    [Normal
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field)
      (abstractFixedFieldCyclotomicFiniteLayer H E)]
    (σ :
      Gal(LocalClassFieldTheory.abstractRelativeFixedField
          ℚ (SeparableClosure ℚ)
          (rationalCyclotomicFieldInertia_le H.field)/LocalClassFieldTheory.abstractFixedField
          ℚ (SeparableClosure ℚ) H.field))
    (z : E) :
    abstractFixedFieldCyclotomicFiniteLayerEmbedding H E
        (IntermediateField.restrictRestrictAlgEquivMapHom
          ℚ E
          (LocalClassFieldTheory.abstractFixedField
            ℚ (SeparableClosure ℚ) H.field)
          (abstractFixedFieldCyclotomicFiniteLayer H E)
          (AlgEquiv.restrictNormalHom
            (abstractFixedFieldCyclotomicFiniteLayer H E) σ) z) =
      (AlgEquiv.restrictNormalHom
        (abstractFixedFieldCyclotomicFiniteLayer H E) σ)
        (abstractFixedFieldCyclotomicFiniteLayerEmbedding H E z) := by
  let F :=
    LocalClassFieldTheory.abstractFixedField
      ℚ (SeparableClosure ℚ) H.field
  let U :=
    LocalClassFieldTheory.abstractRelativeFixedField
      ℚ (SeparableClosure ℚ)
      (rationalCyclotomicFieldInertia_le H.field)
  let P : IntermediateField F U :=
    abstractFixedFieldCyclotomicFiniteLayer H E
  exact
    AlgEquiv.restrictNormal_commutes
      (MulSemiringAction.toAlgEquiv ℚ P
        (AlgEquiv.restrictNormalHom P σ)) E z

/-- The left finite-level restriction, after both canonical embeddings into
the full compositum, is the action of `σ` on the cyclotomic embedding. -/
private theorem
    restrictNormalHom_abstractFixedFieldCyclotomicRestriction_left_embedded
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField)
    [Normal ℚ E]
    (σ :
      Gal(LocalClassFieldTheory.abstractRelativeFixedField
          ℚ (SeparableClosure ℚ)
          (rationalCyclotomicFieldInertia_le H.field)/LocalClassFieldTheory.abstractFixedField
          ℚ (SeparableClosure ℚ) H.field))
    (x : E) :
    abstractFixedFieldCyclotomicFiniteLayerInclusion H E
        (abstractFixedFieldCyclotomicFiniteLayerEmbedding H E
          (AlgEquiv.restrictNormalHom E
            (abstractFixedFieldCyclotomicRestriction H σ) x)) =
      σ
        (rationalCyclotomicZHatFieldEmbeddingInAbstractFixedFieldCompositum H
          (x : rationalCyclotomicZHatField)) := by
  calc
    abstractFixedFieldCyclotomicFiniteLayerInclusion H E
          (abstractFixedFieldCyclotomicFiniteLayerEmbedding H E
            (AlgEquiv.restrictNormalHom E
              (abstractFixedFieldCyclotomicRestriction H σ) x)) =
        rationalCyclotomicZHatFieldEmbeddingInAbstractFixedFieldCompositum H
          (((AlgEquiv.restrictNormalHom E
            (abstractFixedFieldCyclotomicRestriction H σ) x) :
              rationalCyclotomicZHatField)) :=
      abstractFixedFieldCyclotomicFiniteLayerEmbedding_inclusion H E _
    _ = rationalCyclotomicZHatFieldEmbeddingInAbstractFixedFieldCompositum H
          (abstractFixedFieldCyclotomicRestriction H σ
            (x : rationalCyclotomicZHatField)) :=
      congrArg
        (rationalCyclotomicZHatFieldEmbeddingInAbstractFixedFieldCompositum H)
        (restrictNormalHom_abstractFixedFieldCyclotomicRestriction_apply
          H E σ x)
    _ = σ
          (rationalCyclotomicZHatFieldEmbeddingInAbstractFixedFieldCompositum
            H (x : rationalCyclotomicZHatField)) :=
      abstractFixedFieldCyclotomicRestriction_embedding_apply
        H σ (x : rationalCyclotomicZHatField)

/-- The right finite-level restriction, after both canonical embeddings into
the full compositum, is the same action of `σ`. -/
private theorem
    restrictNormalHom_abstractFixedFieldCyclotomicRestriction_right_embedded
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField)
    [Normal ℚ E]
    [Normal
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field)
      (abstractFixedFieldCyclotomicFiniteLayer H E)]
    (σ :
      Gal(LocalClassFieldTheory.abstractRelativeFixedField
          ℚ (SeparableClosure ℚ)
          (rationalCyclotomicFieldInertia_le H.field)/LocalClassFieldTheory.abstractFixedField
          ℚ (SeparableClosure ℚ) H.field))
    (x : E) :
    abstractFixedFieldCyclotomicFiniteLayerInclusion H E
        (abstractFixedFieldCyclotomicFiniteLayerEmbedding H E
          (IntermediateField.restrictRestrictAlgEquivMapHom
            ℚ E
            (LocalClassFieldTheory.abstractFixedField
              ℚ (SeparableClosure ℚ) H.field)
            (abstractFixedFieldCyclotomicFiniteLayer H E)
            (AlgEquiv.restrictNormalHom
              (abstractFixedFieldCyclotomicFiniteLayer H E) σ) x)) =
      σ
        (rationalCyclotomicZHatFieldEmbeddingInAbstractFixedFieldCompositum H
          (x : rationalCyclotomicZHatField)) := by
  calc
    abstractFixedFieldCyclotomicFiniteLayerInclusion H E
          (abstractFixedFieldCyclotomicFiniteLayerEmbedding H E
            (IntermediateField.restrictRestrictAlgEquivMapHom
              ℚ E
              (LocalClassFieldTheory.abstractFixedField
                ℚ (SeparableClosure ℚ) H.field)
              (abstractFixedFieldCyclotomicFiniteLayer H E)
              (AlgEquiv.restrictNormalHom
                (abstractFixedFieldCyclotomicFiniteLayer H E) σ) x)) =
        abstractFixedFieldCyclotomicFiniteLayerInclusion H E
          ((AlgEquiv.restrictNormalHom
            (abstractFixedFieldCyclotomicFiniteLayer H E) σ)
            (abstractFixedFieldCyclotomicFiniteLayerEmbedding H E x)) :=
      congrArg
        (abstractFixedFieldCyclotomicFiniteLayerInclusion H E)
        (abstractFixedFieldCyclotomicFiniteLayerEmbedding_restrict_apply
          H E σ x)
    _ = σ
          (abstractFixedFieldCyclotomicFiniteLayerInclusion H E
            (abstractFixedFieldCyclotomicFiniteLayerEmbedding H E x)) :=
      restrictNormalHom_abstractFixedFieldCyclotomicFiniteLayer_apply
        H E σ (abstractFixedFieldCyclotomicFiniteLayerEmbedding H E x)
    _ = σ
          (rationalCyclotomicZHatFieldEmbeddingInAbstractFixedFieldCompositum
            H (x : rationalCyclotomicZHatField)) :=
      congrArg σ
        (abstractFixedFieldCyclotomicFiniteLayerEmbedding_inclusion H E x)

/-- Pointwise form of finite-layer restriction compatibility. -/
private theorem
    restrictNormalHom_abstractFixedFieldCyclotomicRestriction_pointwise
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField)
    [Normal ℚ E]
    [Normal
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field)
      (abstractFixedFieldCyclotomicFiniteLayer H E)]
    (σ :
      Gal(LocalClassFieldTheory.abstractRelativeFixedField
          ℚ (SeparableClosure ℚ)
          (rationalCyclotomicFieldInertia_le H.field)/LocalClassFieldTheory.abstractFixedField
          ℚ (SeparableClosure ℚ) H.field))
    (x : E) :
    AlgEquiv.restrictNormalHom E
        (abstractFixedFieldCyclotomicRestriction H σ) x =
      IntermediateField.restrictRestrictAlgEquivMapHom
          ℚ E
          (LocalClassFieldTheory.abstractFixedField
            ℚ (SeparableClosure ℚ) H.field)
          (abstractFixedFieldCyclotomicFiniteLayer H E)
        (AlgEquiv.restrictNormalHom
          (abstractFixedFieldCyclotomicFiniteLayer H E) σ) x := by
  apply
    (abstractFixedFieldCyclotomicFiniteLayerEmbedding H E).injective
  apply
    (abstractFixedFieldCyclotomicFiniteLayerInclusion H E).injective
  exact
    (restrictNormalHom_abstractFixedFieldCyclotomicRestriction_left_embedded
      H E σ x).trans
      (restrictNormalHom_abstractFixedFieldCyclotomicRestriction_right_embedded
        H E σ x).symm

/-- Restricting through a finite layer commutes with restriction from
the full abstract-fixed-field compositum. -/
theorem
    restrictNormalHom_abstractFixedFieldCyclotomicRestriction
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField)
    (σ :
      Gal(LocalClassFieldTheory.abstractRelativeFixedField
          ℚ (SeparableClosure ℚ)
          (rationalCyclotomicFieldInertia_le H.field)/LocalClassFieldTheory.abstractFixedField
          ℚ (SeparableClosure ℚ) H.field)) :
    letI : Normal ℚ E := E.isGalois.to_normal
    AlgEquiv.restrictNormalHom E
        (abstractFixedFieldCyclotomicRestriction H σ) =
      IntermediateField.restrictRestrictAlgEquivMapHom
          ℚ E
          (LocalClassFieldTheory.abstractFixedField
            ℚ (SeparableClosure ℚ) H.field)
          (abstractFixedFieldCyclotomicFiniteLayer H E)
        (AlgEquiv.restrictNormalHom
          (abstractFixedFieldCyclotomicFiniteGaloisLayer H E)
          σ) := by
  let : Normal ℚ E := E.isGalois.to_normal
  let F :=
    LocalClassFieldTheory.abstractFixedField
      ℚ (SeparableClosure ℚ) H.field
  let U :=
    LocalClassFieldTheory.abstractRelativeFixedField
      ℚ (SeparableClosure ℚ)
      (rationalCyclotomicFieldInertia_le H.field)
  let T := rationalCyclotomicZHatField
  let P : IntermediateField F U :=
    abstractFixedFieldCyclotomicFiniteLayer H E
  let : Algebra T U :=
    abstractFixedFieldCyclotomicCompositumAlgebra H
  let : IsScalarTower ℚ T U :=
    abstractFixedFieldCyclotomicCompositum_scalarTower H
  let : Algebra E P :=
    abstractFixedFieldCyclotomicFiniteLayerLayerAlgebra H E
  let : IsScalarTower ℚ E P :=
    abstractFixedFieldCyclotomicFiniteLayer_layerScalarTower H E
  let : IsAbelianGalois F P := by
    change IsAbelianGalois F
      (abstractFixedFieldCyclotomicFiniteLayer H E)
    exact
      abstractFixedFieldCyclotomicFiniteLayer_isAbelianGalois H E
  let : Normal F P := IsGalois.to_normal
  apply AlgEquiv.ext
  intro x
  exact
    restrictNormalHom_abstractFixedFieldCyclotomicRestriction_pointwise
      H E σ x

section FiniteCoordinateHelpers

/-- Opaque three-step equality composition used to keep large dependent
finite-level coordinates out of endpoint proof normalization. -/
private theorem cyclotomicAbstractFixedFieldArtin_eqTransThree
    {α : Type} {a b c d : α}
    (hab : a = b) (hbc : b = c) (hcd : c = d) :
    a = d :=
  hab.trans (hbc.trans hcd)

private abbrev cyclotomicAbstractFixedFieldArtinCoordinateBase
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :=
  LocalClassFieldTheory.abstractFixedField
    ℚ (SeparableClosure ℚ) H.field

private abbrev cyclotomicAbstractFixedFieldArtinCoordinateRelative
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :=
  LocalClassFieldTheory.abstractRelativeFixedField
    ℚ (SeparableClosure ℚ)
    (rationalCyclotomicFieldInertia_le H.field)

private abbrev cyclotomicAbstractFixedFieldArtinCoordinateLayer
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    IntermediateField
      (cyclotomicAbstractFixedFieldArtinCoordinateBase H)
      (cyclotomicAbstractFixedFieldArtinCoordinateRelative H) :=
  abstractFixedFieldCyclotomicFiniteLayer H E

/-- The base field for an abstract fixed-field Artin coordinate carries its rational algebra
structure. -/
noncomputable local instance
    cyclotomicAbstractFixedFieldArtinCoordinateBaseAlgebra
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :
    Algebra ℚ
      (cyclotomicAbstractFixedFieldArtinCoordinateBase H) :=
  (cyclotomicAbstractFixedFieldArtinCoordinateBase H).algebra'

/-- The fixed base field of an Artin coordinate has finite degree over the rationals. -/
theorem cyclotomicAbstractFixedFieldArtinCoordinateBaseFiniteDimensional
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :
    FiniteDimensional ℚ
      (cyclotomicAbstractFixedFieldArtinCoordinateBase H) :=
  LocalClassFieldTheory.abstractFixedField_finiteDimensional
    ℚ (SeparableClosure ℚ) H.field H.finite

attribute [local instance] cyclotomicAbstractFixedFieldArtinCoordinateBaseFiniteDimensional

/-- The fixed base field of an Artin coordinate is a number field. -/
theorem cyclotomicAbstractFixedFieldArtinCoordinateBaseNumberField
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :
    NumberField
      (cyclotomicAbstractFixedFieldArtinCoordinateBase H) :=
  NumberField.of_module_finite ℚ
    (cyclotomicAbstractFixedFieldArtinCoordinateBase H)

attribute [local instance] cyclotomicAbstractFixedFieldArtinCoordinateBaseNumberField

/-- The rational separable closure is an algebra over the base field of an Artin coordinate. -/
noncomputable local instance
    cyclotomicAbstractFixedFieldArtinCoordinateBaseSeparableAlgebra
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :
    Algebra
      (cyclotomicAbstractFixedFieldArtinCoordinateBase H)
      (SeparableClosure ℚ) :=
  IntermediateField.toAlgebra
    (cyclotomicAbstractFixedFieldArtinCoordinateBase H)

/-- The relative cyclotomic field of an Artin coordinate is an algebra over its base field. -/
noncomputable local instance
    cyclotomicAbstractFixedFieldArtinCoordinateRelativeAlgebra
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :
    Algebra
      (cyclotomicAbstractFixedFieldArtinCoordinateBase H)
      (cyclotomicAbstractFixedFieldArtinCoordinateRelative H) :=
  (cyclotomicAbstractFixedFieldArtinCoordinateRelative H).algebra'

/-- Rational scalars act on the relative coordinate field through its fixed base field. -/
theorem cyclotomicAbstractFixedFieldArtinCoordinateRelativeScalarTower
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :
    IsScalarTower ℚ
      (cyclotomicAbstractFixedFieldArtinCoordinateBase H)
      (cyclotomicAbstractFixedFieldArtinCoordinateRelative H) :=
  abstractFixedFieldCyclotomicCompositum_baseScalarTower H

attribute [local instance] cyclotomicAbstractFixedFieldArtinCoordinateRelativeScalarTower

/-- The relative cyclotomic coordinate field is abelian Galois over its fixed base field. -/
theorem cyclotomicAbstractFixedFieldArtinCoordinateRelativeIsAbelianGalois
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :
    IsAbelianGalois
      (cyclotomicAbstractFixedFieldArtinCoordinateBase H)
      (cyclotomicAbstractFixedFieldArtinCoordinateRelative H) :=
  abstractFixedFieldCyclotomic_isAbelianGalois H

attribute [local instance] cyclotomicAbstractFixedFieldArtinCoordinateRelativeIsAbelianGalois

/-- A finite Galois cyclotomic coordinate carries its intermediate-field rational algebra
structure. -/
noncomputable local instance
    cyclotomicAbstractFixedFieldArtinCoordinateAlgebra
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    Algebra ℚ E :=
  E.toIntermediateField.algebra'

/-- Each finite rational cyclotomic coordinate is a number field. -/
theorem cyclotomicAbstractFixedFieldArtinCoordinateNumberField
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    NumberField E :=
  NumberField.of_module_finite ℚ E

attribute [local instance] cyclotomicAbstractFixedFieldArtinCoordinateNumberField

/-- Each finite rational cyclotomic coordinate is abelian Galois over the rationals. -/
theorem cyclotomicAbstractFixedFieldArtinCoordinateIsAbelianGalois
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    IsAbelianGalois ℚ E :=
  IsAbelianGalois.of_algHom E.toIntermediateField.val

attribute [local instance] cyclotomicAbstractFixedFieldArtinCoordinateIsAbelianGalois

/-- Each finite rational cyclotomic coordinate is normal over the rationals. -/
theorem cyclotomicAbstractFixedFieldArtinCoordinateNormal
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    Normal ℚ E :=
  E.isGalois.to_normal

attribute [local instance] cyclotomicAbstractFixedFieldArtinCoordinateNormal

/-- A finite cyclotomic coordinate layer is an algebra over the abstract fixed base field. -/
noncomputable local instance
    cyclotomicAbstractFixedFieldArtinCoordinateLayerBaseAlgebra
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    Algebra
      (cyclotomicAbstractFixedFieldArtinCoordinateBase H)
      (cyclotomicAbstractFixedFieldArtinCoordinateLayer H E) :=
  (abstractFixedFieldCyclotomicFiniteGaloisLayer H E).algebra'

/-- A finite cyclotomic coordinate layer carries its rational algebra structure. -/
noncomputable local instance
    cyclotomicAbstractFixedFieldArtinCoordinateLayerRatAlgebra
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    Algebra ℚ
      (cyclotomicAbstractFixedFieldArtinCoordinateLayer H E) :=
  DivisionRing.toRatAlgebra

/-- Rational scalars act on a finite coordinate layer through the fixed base field. -/
theorem cyclotomicAbstractFixedFieldArtinCoordinateLayerBaseScalarTower
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    IsScalarTower ℚ
      (cyclotomicAbstractFixedFieldArtinCoordinateBase H)
      (cyclotomicAbstractFixedFieldArtinCoordinateLayer H E) := by
  let hI := rationalCyclotomicFieldInertia_le H.field
  apply IsScalarTower.of_algebraMap_eq
  intro x
  apply Subtype.ext
  change
    algebraMap ℚ
        (LocalClassFieldTheory.abstractRelativeFixedField
          ℚ (SeparableClosure ℚ) hI) x =
      algebraMap
        (LocalClassFieldTheory.abstractFixedField
          ℚ (SeparableClosure ℚ) H.field)
        (LocalClassFieldTheory.abstractRelativeFixedField
          ℚ (SeparableClosure ℚ) hI)
        (algebraMap ℚ
          (LocalClassFieldTheory.abstractFixedField
            ℚ (SeparableClosure ℚ) H.field) x)
  exact
    IsScalarTower.algebraMap_apply
      ℚ
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field)
      (LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) hI) x

attribute [local instance] cyclotomicAbstractFixedFieldArtinCoordinateLayerBaseScalarTower

/-- The finite Galois coordinate layer over the fixed base is a number field. -/
theorem cyclotomicAbstractFixedFieldArtinCoordinateLayerNumberField
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    NumberField
      (abstractFixedFieldCyclotomicFiniteGaloisLayer H E) :=
  abstractFixedFieldCyclotomicFiniteLayer_numberField H E

attribute [local instance] cyclotomicAbstractFixedFieldArtinCoordinateLayerNumberField

/-- A finite cyclotomic coordinate layer is an algebra over the chosen cyclotomic field. -/
noncomputable local instance
    cyclotomicAbstractFixedFieldArtinCoordinateLayerAlgebra
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    Algebra E
      (cyclotomicAbstractFixedFieldArtinCoordinateLayer H E) :=
  abstractFixedFieldCyclotomicFiniteLayerLayerAlgebra H E

/-- The chosen cyclotomic field acts on its finite coordinate layer through the layer algebra. -/
noncomputable local instance
    cyclotomicAbstractFixedFieldArtinCoordinateLayerSMul
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    SMul E
      (cyclotomicAbstractFixedFieldArtinCoordinateLayer H E) :=
  abstractFixedFieldCyclotomicFiniteLayerLayerSMul H E

/-- Rational scalars act on a coordinate layer through its finite cyclotomic field. -/
theorem cyclotomicAbstractFixedFieldArtinCoordinateLayerScalarTower
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    IsScalarTower ℚ E
      (cyclotomicAbstractFixedFieldArtinCoordinateLayer H E) :=
  abstractFixedFieldCyclotomicFiniteLayer_layerScalarTower H E

attribute [local instance] cyclotomicAbstractFixedFieldArtinCoordinateLayerScalarTower

/-- The relative cyclotomic field is an algebra over each finite coordinate layer. -/
noncomputable local instance
    cyclotomicAbstractFixedFieldArtinCoordinateLayerRelativeAlgebra
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    Algebra
      (cyclotomicAbstractFixedFieldArtinCoordinateLayer H E)
      (cyclotomicAbstractFixedFieldArtinCoordinateRelative H) :=
  IntermediateField.toAlgebra
    (cyclotomicAbstractFixedFieldArtinCoordinateLayer H E)

/-- The fixed base acts on the relative coordinate field through each finite coordinate layer.
-/
theorem cyclotomicAbstractFixedFieldArtinCoordinateLayerRelativeScalarTower
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    IsScalarTower
      (cyclotomicAbstractFixedFieldArtinCoordinateBase H)
      (cyclotomicAbstractFixedFieldArtinCoordinateLayer H E)
      (cyclotomicAbstractFixedFieldArtinCoordinateRelative H) :=
  abstractFixedFieldCyclotomicFiniteGaloisLayer_scalarTower H E

attribute [local instance] cyclotomicAbstractFixedFieldArtinCoordinateLayerRelativeScalarTower

/-- Each finite coordinate layer is abelian Galois over the fixed base field. -/
theorem cyclotomicAbstractFixedFieldArtinCoordinateLayerIsAbelianGalois
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    IsAbelianGalois
      (cyclotomicAbstractFixedFieldArtinCoordinateBase H)
      (cyclotomicAbstractFixedFieldArtinCoordinateLayer H E) :=
  abstractFixedFieldCyclotomicFiniteLayer_isAbelianGalois H E

attribute [local instance] cyclotomicAbstractFixedFieldArtinCoordinateLayerIsAbelianGalois

/-- The full abstract Artin symbol whose finite coordinates are compared
below.  Naming this endpoint keeps its relative fixed-field data opaque. -/
private noncomputable def
    cyclotomicAbstractFixedFieldArtinAbstractEndpoint
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (a : IdeleGroup
      (cyclotomicAbstractFixedFieldArtinCoordinateBase H)) :
    Gal(rationalCyclotomicZHatField/ℚ) :=
  abstractFixedFieldCyclotomicRestriction H
    (infiniteGlobalArtinMonoidHom
      (cyclotomicAbstractFixedFieldArtinCoordinateBase H)
      (cyclotomicAbstractFixedFieldArtinCoordinateRelative H) a)

/-- The rational norm Artin symbol serving as the other full endpoint. -/
private noncomputable def
    cyclotomicAbstractFixedFieldArtinRationalEndpoint
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (a : IdeleGroup
      (cyclotomicAbstractFixedFieldArtinCoordinateBase H)) :
    Gal(rationalCyclotomicZHatField/ℚ) :=
  rationalCyclotomicZHatGlobalArtin
    (IdeleGroup.norm ℚ
      (cyclotomicAbstractFixedFieldArtinCoordinateBase H) a)

/-- The finite restriction map packaged together with its pointwise Artin
naturality law.  The map is inferred from the generic hom-level theorem, so
no concrete instance tower is compared after the opaque boundary. -/
private noncomputable def cyclotomicAbstractFixedFieldArtinCoordinateMapData
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    {f : Gal(abstractFixedFieldCyclotomicFiniteGaloisLayer H
      E/cyclotomicAbstractFixedFieldArtinCoordinateBase H) →*
        Gal(E/ℚ) //
      f.comp
          (@globalArtinMonoidHomOfNumberField
            (cyclotomicAbstractFixedFieldArtinCoordinateBase H)
            (abstractFixedFieldCyclotomicFiniteGaloisLayer H E)
            (inferInstance : Field
              (cyclotomicAbstractFixedFieldArtinCoordinateBase H))
            (cyclotomicAbstractFixedFieldArtinCoordinateBaseNumberField H)
            (inferInstance : Field
              (abstractFixedFieldCyclotomicFiniteGaloisLayer H E))
            (cyclotomicAbstractFixedFieldArtinCoordinateLayerBaseAlgebra H E)
            (cyclotomicAbstractFixedFieldArtinCoordinateLayerIsAbelianGalois H E)
            (cyclotomicAbstractFixedFieldArtinCoordinateLayerNumberField H E)) =
        (globalArtinMonoidHom (K := ℚ) (L := E)).comp
          (IdeleGroup.norm ℚ
            (cyclotomicAbstractFixedFieldArtinCoordinateBase H))} := by
  have hnat :=
    @globalArtinMonoidHomOfNumberField_norm_restriction
      ℚ E
      (cyclotomicAbstractFixedFieldArtinCoordinateBase H)
      (abstractFixedFieldCyclotomicFiniteGaloisLayer H E)
      inferInstance inferInstance
      inferInstance
      (cyclotomicAbstractFixedFieldArtinCoordinateNumberField E)
      (cyclotomicAbstractFixedFieldArtinCoordinateAlgebra E)
      (cyclotomicAbstractFixedFieldArtinCoordinateIsAbelianGalois E)
      inferInstance
      (cyclotomicAbstractFixedFieldArtinCoordinateBaseNumberField H)
      inferInstance
      (cyclotomicAbstractFixedFieldArtinCoordinateBaseAlgebra H)
      (cyclotomicAbstractFixedFieldArtinCoordinateLayerBaseAlgebra H E)
      (cyclotomicAbstractFixedFieldArtinCoordinateLayerRatAlgebra H E)
      (cyclotomicAbstractFixedFieldArtinCoordinateLayerBaseScalarTower H E)
      (cyclotomicAbstractFixedFieldArtinCoordinateLayerAlgebra H E)
      (cyclotomicAbstractFixedFieldArtinCoordinateLayerScalarTower H E)
      (cyclotomicAbstractFixedFieldArtinCoordinateLayerIsAbelianGalois H E)
      (cyclotomicAbstractFixedFieldArtinCoordinateLayerNumberField H E)
  exact
    ⟨(@AlgEquiv.restrictNormalHom
          ℚ inferInstance
          (abstractFixedFieldCyclotomicFiniteGaloisLayer H E)
          inferInstance
          (cyclotomicAbstractFixedFieldArtinCoordinateLayerRatAlgebra H E)
          E inferInstance
          (cyclotomicAbstractFixedFieldArtinCoordinateAlgebra E)
          (cyclotomicAbstractFixedFieldArtinCoordinateLayerAlgebra H E)
          (cyclotomicAbstractFixedFieldArtinCoordinateLayerScalarTower H E)
          (cyclotomicAbstractFixedFieldArtinCoordinateNormal E)).comp
        (@AlgEquiv.restrictScalarsHom
          ℚ
          (cyclotomicAbstractFixedFieldArtinCoordinateBase H)
          (abstractFixedFieldCyclotomicFiniteGaloisLayer H E)
          inferInstance inferInstance inferInstance
          (cyclotomicAbstractFixedFieldArtinCoordinateBaseAlgebra H)
          (cyclotomicAbstractFixedFieldArtinCoordinateLayerBaseAlgebra H E)
          (cyclotomicAbstractFixedFieldArtinCoordinateLayerRatAlgebra H E)
          (cyclotomicAbstractFixedFieldArtinCoordinateLayerBaseScalarTower H E)),
      hnat⟩

/-- The fixed restriction map from the relative finite layer to one rational
cyclotomic coordinate. -/
private noncomputable def cyclotomicAbstractFixedFieldArtinCoordinateMap
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    Gal(abstractFixedFieldCyclotomicFiniteGaloisLayer H
      E/cyclotomicAbstractFixedFieldArtinCoordinateBase H) →*
      Gal(E/ℚ) :=
  (cyclotomicAbstractFixedFieldArtinCoordinateMapData H E).1

/-- Naturality of the named coordinate map, kept at the hom level so later
pointwise rewrites match the opaque map without unfolding its data package. -/
private theorem cyclotomicAbstractFixedFieldArtinCoordinateMap_naturality
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    (cyclotomicAbstractFixedFieldArtinCoordinateMap H E).comp
        (globalArtinMonoidHom
          (K := cyclotomicAbstractFixedFieldArtinCoordinateBase H)
          (L := abstractFixedFieldCyclotomicFiniteGaloisLayer H E)) =
      (globalArtinMonoidHom (K := ℚ) (L := E)).comp
        (IdeleGroup.norm ℚ
          (cyclotomicAbstractFixedFieldArtinCoordinateBase H)) :=
  (cyclotomicAbstractFixedFieldArtinCoordinateMapData H E).2

/-- Pointwise identification of the named coordinate map with the concrete
two-stage restriction used by the abstract fixed-field comparison. -/
private theorem cyclotomicAbstractFixedFieldArtinCoordinateMap_apply
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField)
    (σ : Gal(abstractFixedFieldCyclotomicFiniteGaloisLayer H
      E/cyclotomicAbstractFixedFieldArtinCoordinateBase H)) :
    cyclotomicAbstractFixedFieldArtinCoordinateMap H E σ =
      @IntermediateField.restrictRestrictAlgEquivMapHom
        ℚ E
        (cyclotomicAbstractFixedFieldArtinCoordinateBase H)
        (abstractFixedFieldCyclotomicFiniteGaloisLayer H E)
        inferInstance inferInstance inferInstance inferInstance
        (cyclotomicAbstractFixedFieldArtinCoordinateAlgebra E)
        (cyclotomicAbstractFixedFieldArtinCoordinateBaseAlgebra H)
        (cyclotomicAbstractFixedFieldArtinCoordinateLayerRatAlgebra H E)
        (cyclotomicAbstractFixedFieldArtinCoordinateLayerAlgebra H E)
        (cyclotomicAbstractFixedFieldArtinCoordinateLayerBaseAlgebra H E)
        (cyclotomicAbstractFixedFieldArtinCoordinateLayerScalarTower H E)
        (cyclotomicAbstractFixedFieldArtinCoordinateLayerBaseScalarTower H E)
        (cyclotomicAbstractFixedFieldArtinCoordinateNormal E) σ :=
  rfl

/-- The relative projection, common rational finite value, and rational
infinite projection, with both comparison steps packaged by the generic
provider before this concrete tower becomes opaque. -/
private noncomputable def
    cyclotomicAbstractFixedFieldArtinCoordinateBridgeData
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (a : IdeleGroup
      (cyclotomicAbstractFixedFieldArtinCoordinateBase H))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :=
    @compRestrictNormalHomInfiniteGlobalArtinRationalCyclotomicDataOfNumberField
      (cyclotomicAbstractFixedFieldArtinCoordinateBase H)
      (cyclotomicAbstractFixedFieldArtinCoordinateRelative H)
      (inferInstance : Field
        (cyclotomicAbstractFixedFieldArtinCoordinateBase H))
      (cyclotomicAbstractFixedFieldArtinCoordinateBaseNumberField H)
      (inferInstance : Field
        (cyclotomicAbstractFixedFieldArtinCoordinateRelative H))
      (cyclotomicAbstractFixedFieldArtinCoordinateRelativeAlgebra H)
      (cyclotomicAbstractFixedFieldArtinCoordinateRelativeIsAbelianGalois H)
      a
      (abstractFixedFieldCyclotomicFiniteGaloisLayer H E)
      (cyclotomicAbstractFixedFieldArtinCoordinateLayerNumberField H E)
      E
      (cyclotomicAbstractFixedFieldArtinCoordinateNumberField E)
      (cyclotomicAbstractFixedFieldArtinCoordinateIsAbelianGalois E)
      (cyclotomicAbstractFixedFieldArtinCoordinateMap H E)
      (cyclotomicAbstractFixedFieldArtinCoordinateMap_naturality H E)

/-- The abstract endpoint after projection to one finite coordinate. -/
private noncomputable def
    cyclotomicAbstractFixedFieldArtinAbstractCoordinate
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (a : IdeleGroup
      (cyclotomicAbstractFixedFieldArtinCoordinateBase H))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    Gal(E/ℚ) :=
  AlgEquiv.restrictNormalHom E
    (cyclotomicAbstractFixedFieldArtinAbstractEndpoint H a)

/-- The relative infinite Artin symbol, restricted to a finite layer and
then mapped to the corresponding rational coordinate. -/
private noncomputable def
    cyclotomicAbstractFixedFieldArtinRestrictedLayerCoordinate
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (a : IdeleGroup
      (cyclotomicAbstractFixedFieldArtinCoordinateBase H))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    Gal(E/ℚ) :=
  (cyclotomicAbstractFixedFieldArtinCoordinateBridgeData H a E).1.1

/-- The finite relative Artin symbol mapped to one rational coordinate. -/
private noncomputable def
    cyclotomicAbstractFixedFieldArtinFiniteCoordinate
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (a : IdeleGroup
      (cyclotomicAbstractFixedFieldArtinCoordinateBase H))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    Gal(E/ℚ) :=
  (cyclotomicAbstractFixedFieldArtinCoordinateBridgeData H a E).1.2.1

/-- The finite rational Artin coordinate of the idele norm. -/
private noncomputable def
    cyclotomicAbstractFixedFieldArtinRationalCoordinate
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (a : IdeleGroup
      (cyclotomicAbstractFixedFieldArtinCoordinateBase H))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    Gal(E/ℚ) :=
  (cyclotomicAbstractFixedFieldArtinCoordinateBridgeData H a E).1.2.1

/-- Naturality of the finite global Artin map at the concrete cyclotomic
coordinate. -/
private theorem
    cyclotomicAbstractFixedFieldArtinCoordinateNaturality
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (a : IdeleGroup
      (cyclotomicAbstractFixedFieldArtinCoordinateBase H))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    cyclotomicAbstractFixedFieldArtinFiniteCoordinate H a E =
      cyclotomicAbstractFixedFieldArtinRationalCoordinate H a E := by
  rfl

/-- The rational endpoint after projection to one finite coordinate. -/
private noncomputable def
    cyclotomicAbstractFixedFieldArtinRationalEndpointCoordinate
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (a : IdeleGroup
      (cyclotomicAbstractFixedFieldArtinCoordinateBase H))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    Gal(E/ℚ) :=
  (cyclotomicAbstractFixedFieldArtinCoordinateBridgeData H a E).1.2.2

/-- The abstract restriction map projected to the concrete finite layer. -/
private theorem
    cyclotomicAbstractFixedFieldArtinCoordinateRestriction
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (a : IdeleGroup
      (cyclotomicAbstractFixedFieldArtinCoordinateBase H))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    cyclotomicAbstractFixedFieldArtinAbstractCoordinate H a E =
      cyclotomicAbstractFixedFieldArtinRestrictedLayerCoordinate H a E := by
  calc
    cyclotomicAbstractFixedFieldArtinAbstractCoordinate H a E =
        AlgEquiv.restrictNormalHom E
          (cyclotomicAbstractFixedFieldArtinAbstractEndpoint H a) := rfl
    _ = cyclotomicAbstractFixedFieldArtinCoordinateMap H E
          (AlgEquiv.restrictNormalHom
            (abstractFixedFieldCyclotomicFiniteGaloisLayer H E)
            (infiniteGlobalArtinMonoidHom
              (cyclotomicAbstractFixedFieldArtinCoordinateBase H)
              (cyclotomicAbstractFixedFieldArtinCoordinateRelative H) a)) :=
      (restrictNormalHom_abstractFixedFieldCyclotomicRestriction
          H E
            (infiniteGlobalArtinMonoidHom
              (cyclotomicAbstractFixedFieldArtinCoordinateBase H)
              (cyclotomicAbstractFixedFieldArtinCoordinateRelative H) a)).trans
        (cyclotomicAbstractFixedFieldArtinCoordinateMap_apply H E _).symm
    _ = cyclotomicAbstractFixedFieldArtinRestrictedLayerCoordinate H a E := rfl

/-- Restricting the infinite relative Artin symbol supplies exactly the
finite Artin coordinate. -/
private theorem
    cyclotomicAbstractFixedFieldArtinCoordinateLayerProjection
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (a : IdeleGroup
      (cyclotomicAbstractFixedFieldArtinCoordinateBase H))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    cyclotomicAbstractFixedFieldArtinRestrictedLayerCoordinate H a E =
      cyclotomicAbstractFixedFieldArtinFiniteCoordinate H a E :=
  (cyclotomicAbstractFixedFieldArtinCoordinateBridgeData H a E).2.1

/-- The rational cyclotomic Artin map projected to the same finite
coordinate. -/
private theorem
    cyclotomicAbstractFixedFieldArtinCoordinateRationalProjection
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (a : IdeleGroup
      (cyclotomicAbstractFixedFieldArtinCoordinateBase H))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    cyclotomicAbstractFixedFieldArtinRationalEndpointCoordinate H a E =
      cyclotomicAbstractFixedFieldArtinFiniteCoordinate H a E := by
  exact
    (cyclotomicAbstractFixedFieldArtinCoordinateBridgeData H a E).2.2.symm

/-- Equality of the two full endpoints at one opaque finite coordinate. -/
private theorem
    cyclotomicAbstractFixedFieldArtinFiniteCoordinateComparison
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (a : IdeleGroup
      (cyclotomicAbstractFixedFieldArtinCoordinateBase H))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    AlgEquiv.restrictNormalHom E
        (cyclotomicAbstractFixedFieldArtinAbstractEndpoint H a) =
      AlgEquiv.restrictNormalHom E
        (cyclotomicAbstractFixedFieldArtinRationalEndpoint H a) := by
  change
    cyclotomicAbstractFixedFieldArtinAbstractCoordinate H a E =
      cyclotomicAbstractFixedFieldArtinRationalEndpointCoordinate H a E
  exact
    cyclotomicAbstractFixedFieldArtin_eqTransThree
      (cyclotomicAbstractFixedFieldArtinCoordinateRestriction H a E)
      (cyclotomicAbstractFixedFieldArtinCoordinateLayerProjection H a E)
      (cyclotomicAbstractFixedFieldArtinCoordinateRationalProjection
        H a E).symm

/-- The finite-coordinate comparison assembled in the rational cyclotomic
inverse limit. -/
private theorem
    abstractFixedFieldCyclotomicRestriction_infiniteGlobalArtin_inverseLimit
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (a :
      IdeleGroup
        (cyclotomicAbstractFixedFieldArtinCoordinateBase H)) :
    cyclotomicAbstractFixedFieldArtinAbstractEndpoint H a =
      cyclotomicAbstractFixedFieldArtinRationalEndpoint H a := by
  apply
    (InfiniteGalois.continuousMulEquivToLimit
      ℚ rationalCyclotomicZHatField).injective
  apply Subtype.ext
  funext Eop
  exact
    cyclotomicAbstractFixedFieldArtinFiniteCoordinateComparison
      H a Eop.unop

end FiniteCoordinateHelpers

/-- The actual infinite global Artin map on an abstract fixed field
restricts to the rational cyclotomic Artin map of the ordinary idele
norm. -/
@[simp]
theorem
    abstractFixedFieldCyclotomicRestriction_infiniteGlobalArtinMonoidHom
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (a :
      IdeleGroup
        (LocalClassFieldTheory.abstractFixedField
          ℚ (SeparableClosure ℚ) H.field)) :
    let F :=
      LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field
    letI : FiniteDimensional ℚ F :=
      LocalClassFieldTheory.abstractFixedField_finiteDimensional
        ℚ (SeparableClosure ℚ) H.field H.finite
    letI : NumberField F :=
      NumberField.of_module_finite ℚ F
    let hI :=
      rationalCyclotomicFieldInertia_le H.field
    let U :=
      LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) hI
    letI : IsAbelianGalois F U :=
      abstractFixedFieldCyclotomic_isAbelianGalois H
    abstractFixedFieldCyclotomicRestriction H
        (infiniteGlobalArtinMonoidHom F U a) =
      rationalCyclotomicZHatGlobalArtin
        (IdeleGroup.norm ℚ F a) := by
  exact
    abstractFixedFieldCyclotomicRestriction_infiniteGlobalArtin_inverseLimit
      H a

/-- In the normalized actual Galois coordinate, the infinite global
Artin symbol is exactly the normalized cyclotomic idele value. -/
theorem
    abstractFixedFieldCyclotomicGalEquivZHat_infiniteGlobalArtinMonoidHom
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (a :
      IdeleGroup
        (LocalClassFieldTheory.abstractFixedField
          ℚ (SeparableClosure ℚ) H.field)) :
    let F :=
      LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field
    letI : FiniteDimensional ℚ F :=
      LocalClassFieldTheory.abstractFixedField_finiteDimensional
        ℚ (SeparableClosure ℚ) H.field H.finite
    letI : NumberField F :=
      NumberField.of_module_finite ℚ F
    let hI :=
      rationalCyclotomicFieldInertia_le H.field
    let U :=
      LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) hI
    letI : IsAbelianGalois F U :=
      abstractFixedFieldCyclotomic_isAbelianGalois H
    Multiplicative.toAdd
        (abstractFixedFieldCyclotomicGalEquivZHat H
          (infiniteGlobalArtinMonoidHom F U a)) =
      normalizedCyclotomicZHatIdeleValue F
        (Additive.ofMul a) := by
  let F :=
    LocalClassFieldTheory.abstractFixedField
      ℚ (SeparableClosure ℚ) H.field
  let : FiniteDimensional ℚ F :=
    LocalClassFieldTheory.abstractFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) H.field H.finite
  let : NumberField F :=
    NumberField.of_module_finite ℚ F
  let hI :=
    rationalCyclotomicFieldInertia_le H.field
  let U :=
    LocalClassFieldTheory.abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) hI
  let : IsAbelianGalois F U :=
    abstractFixedFieldCyclotomic_isAbelianGalois H
  apply
    zHatMulNat_injective
      (H.residueDegree rationalCyclotomicDegreeData).pos
  calc
    (H.residueDegree rationalCyclotomicDegreeData : ℕ) •
          Multiplicative.toAdd
            (abstractFixedFieldCyclotomicGalEquivZHat H
              (infiniteGlobalArtinMonoidHom F U a)) =
        Multiplicative.toAdd
          (rationalCyclotomicZHatFieldGalEquivZHat
            (abstractFixedFieldCyclotomicRestriction H
              (infiniteGlobalArtinMonoidHom F U a))) := by
      exact
        (abstractFixedFieldCyclotomicRestriction_coordinate H
          (infiniteGlobalArtinMonoidHom F U a)).symm
    _ =
        Multiplicative.toAdd
          (rationalCyclotomicZHatFieldGalEquivZHat
            (rationalCyclotomicZHatGlobalArtin
              (IdeleGroup.norm ℚ F a))) := by
      rw [
        abstractFixedFieldCyclotomicRestriction_infiniteGlobalArtinMonoidHom]
    _ =
        cyclotomicZHatNormComposite F
          (Additive.ofMul a) := by
      rfl
    _ =
        cyclotomicZHatIntersectionDegree F •
          normalizedCyclotomicZHatIdeleValue F
            (Additive.ofMul a) := by
      exact
        (cyclotomicZHatIntersectionDegree_nsmul_normalizedIdeleValue
          F (Additive.ofMul a)).symm
    _ =
        (H.residueDegree rationalCyclotomicDegreeData : ℕ) •
          normalizedCyclotomicZHatIdeleValue F
            (Additive.ofMul a) := by
      rw [
        cyclotomicZHatIntersectionDegree_abstractFixedField_eq_residueDegree
          H]

/-- Representative form of the actual cyclotomic Artin-coordinate
identity after descent of the normalized value to the idele class
group. -/
theorem
    abstractFixedFieldCyclotomicGalEquivZHat_infiniteGlobalArtinMonoidHom_mk
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (a :
      IdeleGroup
        (LocalClassFieldTheory.abstractFixedField
          ℚ (SeparableClosure ℚ) H.field)) :
    let F :=
      LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field
    letI : FiniteDimensional ℚ F :=
      LocalClassFieldTheory.abstractFixedField_finiteDimensional
        ℚ (SeparableClosure ℚ) H.field H.finite
    letI : NumberField F :=
      NumberField.of_module_finite ℚ F
    let hI :=
      rationalCyclotomicFieldInertia_le H.field
    let U :=
      LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) hI
    letI : IsAbelianGalois F U :=
      abstractFixedFieldCyclotomic_isAbelianGalois H
    Multiplicative.toAdd
        (abstractFixedFieldCyclotomicGalEquivZHat H
          (infiniteGlobalArtinMonoidHom F U a)) =
      normalizedCyclotomicZHatIdeleClassValueContinuous F
        (Additive.ofMul
          (QuotientGroup.mk'
            (IdeleGroup.principalSubgroup F) a)) := by
  have hSeparableClosureAlgebra :
      cyclotomicAbstractFixedFieldArtinSeparableClosureAlgebra =
        rationalSeparableClosureAlgebra :=
    Subsingleton.elim _ _
  cases hSeparableClosureAlgebra
  let F :=
    LocalClassFieldTheory.abstractFixedField
      ℚ (SeparableClosure ℚ) H.field
  let hI :=
    rationalCyclotomicFieldInertia_le H.field
  let U :=
    LocalClassFieldTheory.abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) hI
  let : IsAbelianGalois F U :=
    abstractFixedFieldCyclotomic_isAbelianGalois H
  calc
    Multiplicative.toAdd
        (abstractFixedFieldCyclotomicGalEquivZHat H
          (infiniteGlobalArtinMonoidHom F U a)) =
        normalizedCyclotomicZHatIdeleValue F
          (Additive.ofMul a) :=
      abstractFixedFieldCyclotomicGalEquivZHat_infiniteGlobalArtinMonoidHom
        H a
    _ =
        normalizedCyclotomicZHatIdeleClassValueContinuous F
          (Additive.ofMul
            (QuotientGroup.mk'
              (IdeleGroup.principalSubgroup F) a)) :=
      (normalizedCyclotomicZHatIdeleClassValueContinuous_mk
        (K := F) a).symm

/-- The genuine infinite global Artin symbol of the cyclotomic
maximal-unramified extension kills every principal idele of the
abstract fixed field. -/
theorem
    infiniteGlobalArtinMonoidHom_abstractFixedFieldCyclotomic_principalIdele
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (x :
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field)ˣ) :
    let F :=
      LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field
    letI : FiniteDimensional ℚ F :=
      LocalClassFieldTheory.abstractFixedField_finiteDimensional
        ℚ (SeparableClosure ℚ) H.field H.finite
    letI : NumberField F :=
      NumberField.of_module_finite ℚ F
    let hI :=
      rationalCyclotomicFieldInertia_le H.field
    let U :=
      LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) hI
    letI : IsAbelianGalois F U :=
      abstractFixedFieldCyclotomic_isAbelianGalois H
    infiniteGlobalArtinMonoidHom F U
        (IdeleGroup.principalIdele F x) =
      1 := by
  let F :=
    LocalClassFieldTheory.abstractFixedField
      ℚ (SeparableClosure ℚ) H.field
  let : FiniteDimensional ℚ F :=
    LocalClassFieldTheory.abstractFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) H.field H.finite
  let : NumberField F :=
    NumberField.of_module_finite ℚ F
  let hI :=
    rationalCyclotomicFieldInertia_le H.field
  let U :=
    LocalClassFieldTheory.abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) hI
  let : IsAbelianGalois F U :=
    abstractFixedFieldCyclotomic_isAbelianGalois H
  have hcoord :
      Multiplicative.toAdd
        (abstractFixedFieldCyclotomicGalEquivZHat H
          (infiniteGlobalArtinMonoidHom F U
            (IdeleGroup.principalIdele F x))) = 0 :=
    (abstractFixedFieldCyclotomicGalEquivZHat_infiniteGlobalArtinMonoidHom
      H (IdeleGroup.principalIdele F x)).trans
      (normalizedCyclotomicZHatIdeleValue_principalIdele_eq_zero F x)
  apply (abstractFixedFieldCyclotomicGalEquivZHat H).injective
  rw [map_one]
  apply Multiplicative.ext
  exact hcoord.trans toAdd_one.symm

/-- The genuine cyclotomic maximal-unramified Artin map descended to
the idele class group of an abstract fixed field. -/
noncomputable def abstractFixedFieldCyclotomicIdeleClassArtinMonoidHom
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :
    IdeleClassGroup
        (LocalClassFieldTheory.abstractFixedField
          ℚ (SeparableClosure ℚ) H.field) →*
      Gal(LocalClassFieldTheory.abstractRelativeFixedField
          ℚ (SeparableClosure ℚ)
          (rationalCyclotomicFieldInertia_le H.field)/LocalClassFieldTheory.abstractFixedField
          ℚ (SeparableClosure ℚ) H.field) := by
  let F :=
    LocalClassFieldTheory.abstractFixedField
      ℚ (SeparableClosure ℚ) H.field
  letI : FiniteDimensional ℚ F :=
    LocalClassFieldTheory.abstractFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) H.field H.finite
  letI : NumberField F :=
    NumberField.of_module_finite ℚ F
  let hI :=
    rationalCyclotomicFieldInertia_le H.field
  let U :=
    LocalClassFieldTheory.abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) hI
  letI : IsAbelianGalois F U :=
    abstractFixedFieldCyclotomic_isAbelianGalois H
  exact
    QuotientGroup.lift
      (IdeleGroup.principalSubgroup F)
      (infiniteGlobalArtinMonoidHom F U).toMonoidHom
      (by
        rintro _ ⟨x, rfl⟩
        exact
          infiniteGlobalArtinMonoidHom_abstractFixedFieldCyclotomic_principalIdele
            H x)

/-- Evaluation of the descended maximal-unramified Artin map on an
idele representative. -/
theorem abstractFixedFieldCyclotomicIdeleClassArtinMonoidHom_mk
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (a :
      IdeleGroup
        (LocalClassFieldTheory.abstractFixedField
          ℚ (SeparableClosure ℚ) H.field)) :
    let F :=
      LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field
    letI : FiniteDimensional ℚ F :=
      LocalClassFieldTheory.abstractFixedField_finiteDimensional
        ℚ (SeparableClosure ℚ) H.field H.finite
    letI : NumberField F :=
      NumberField.of_module_finite ℚ F
    let hI :=
      rationalCyclotomicFieldInertia_le H.field
    let U :=
      LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) hI
    letI : IsAbelianGalois F U :=
      abstractFixedFieldCyclotomic_isAbelianGalois H
    abstractFixedFieldCyclotomicIdeleClassArtinMonoidHom H
        (QuotientGroup.mk'
          (IdeleGroup.principalSubgroup F) a) =
      infiniteGlobalArtinMonoidHom F U a := by
  rw [abstractFixedFieldCyclotomicIdeleClassArtinMonoidHom]
  exact QuotientGroup.lift_mk _ _ _

/-- The descended genuine maximal-unramified Artin map is precisely
the normalized cyclotomic idele-class value in the actual Galois
coordinate. -/
theorem
    abstractFixedFieldCyclotomicGalEquivZHat_ideleClassArtinMonoidHom
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (c :
      IdeleClassGroup
        (LocalClassFieldTheory.abstractFixedField
          ℚ (SeparableClosure ℚ) H.field)) :
    let F :=
      LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field
    letI : FiniteDimensional ℚ F :=
      LocalClassFieldTheory.abstractFixedField_finiteDimensional
        ℚ (SeparableClosure ℚ) H.field H.finite
    letI : NumberField F :=
      NumberField.of_module_finite ℚ F
    abstractFixedFieldCyclotomicGalEquivZHat H
        (abstractFixedFieldCyclotomicIdeleClassArtinMonoidHom H c) =
      normalizedCyclotomicZHatIdeleClassValueContinuousMul F c := by
  let F :=
    LocalClassFieldTheory.abstractFixedField
      ℚ (SeparableClosure ℚ) H.field
  let : FiniteDimensional ℚ F :=
    LocalClassFieldTheory.abstractFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) H.field H.finite
  let : NumberField F :=
    NumberField.of_module_finite ℚ F
  have hSeparableClosureAlgebra :
      cyclotomicAbstractFixedFieldArtinSeparableClosureAlgebra =
        rationalSeparableClosureAlgebra :=
    Subsingleton.elim _ _
  cases hSeparableClosureAlgebra
  refine Quotient.inductionOn' c ?_
  intro a
  let hI :=
    rationalCyclotomicFieldInertia_le H.field
  let U :=
    LocalClassFieldTheory.abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) hI
  let : IsAbelianGalois F U :=
    abstractFixedFieldCyclotomic_isAbelianGalois H
  calc
    abstractFixedFieldCyclotomicGalEquivZHat H
        (abstractFixedFieldCyclotomicIdeleClassArtinMonoidHom H
          (QuotientGroup.mk'
            (IdeleGroup.principalSubgroup F) a)) =
        abstractFixedFieldCyclotomicGalEquivZHat H
          (infiniteGlobalArtinMonoidHom F U a) :=
      congrArg (abstractFixedFieldCyclotomicGalEquivZHat H)
        (abstractFixedFieldCyclotomicIdeleClassArtinMonoidHom_mk H a)
    _ =
        normalizedCyclotomicZHatIdeleClassValueContinuousMul F
          (QuotientGroup.mk'
            (IdeleGroup.principalSubgroup F) a) := by
      apply Multiplicative.ext
      exact
        abstractFixedFieldCyclotomicGalEquivZHat_infiniteGlobalArtinMonoidHom_mk
          H a

/-- The genuine chosen-local-factor Artin map to the cyclotomic
maximal-unramified extension is the abstract maximal-unramified
norm-residue symbol.  Both sides are characterized here by their
common normalized valuation coordinate, so no finite reciprocity
comparison is assumed. -/
theorem
    abstractFixedFieldCyclotomicIdeleClassArtin_eq_maximalUnramifiedNormResidue
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (a :
      ambientFixedAddSubgroup
        rationalIdeleClassRepresentation H.field) :
    let hI :=
      rationalCyclotomicFieldInertia_le H.field
    let hnormal :
        (CyclicCohomology.extensionSubgroup H.field
          (rationalCyclotomicDegreeData.fieldInertia H.field)
          hI).Normal := by
      rw [extensionSubgroup_rationalCyclotomicFieldInertia]
      infer_instance
    let qInertia :
        H.field.toSubgroup ⧸
            CyclicCohomology.extensionSubgroup H.field
              (rationalCyclotomicDegreeData.fieldInertia H.field)
              hI ≃*
          H.field.toSubgroup ⧸
            rationalCyclotomicDegreeData.fieldInertiaWithin H.field :=
      QuotientGroup.quotientMulEquivOfEq
        (extensionSubgroup_rationalCyclotomicFieldInertia H.field)
    abstractFixedFieldCyclotomicIdeleClassArtinMonoidHom H
        (Additive.toMul
          ((rationalAbstractFixedFieldIdeleClassEquivFixed H.field
              (hfinite := H.finite)).symm
            a)) =
      LocalClassFieldTheory.abstractExtensionQuotientEquivGaloisGroup
        ℚ (SeparableClosure ℚ) H.field
        (rationalCyclotomicDegreeData.fieldInertia H.field)
        hI hnormal
        (qInertia.symm
          (ValuationData.maximalUnramifiedNormResidueSymbol
            rationalCyclotomicIdeleClassValuationData H a).toMul) := by
  let F :=
    LocalClassFieldTheory.abstractFixedField
      ℚ (SeparableClosure ℚ) H.field
  let : FiniteDimensional ℚ F :=
    LocalClassFieldTheory.abstractFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) H.field H.finite
  let : NumberField F :=
    NumberField.of_module_finite ℚ F
  let hI :=
    rationalCyclotomicFieldInertia_le H.field
  let hnormal :
      (CyclicCohomology.extensionSubgroup H.field
        (rationalCyclotomicDegreeData.fieldInertia H.field)
        hI).Normal := by
    rw [extensionSubgroup_rationalCyclotomicFieldInertia]
    infer_instance
  let qInertia :
      H.field.toSubgroup ⧸
          CyclicCohomology.extensionSubgroup H.field
            (rationalCyclotomicDegreeData.fieldInertia H.field)
            hI ≃*
        H.field.toSubgroup ⧸
          rationalCyclotomicDegreeData.fieldInertiaWithin H.field :=
    QuotientGroup.quotientMulEquivOfEq
      (extensionSubgroup_rationalCyclotomicFieldInertia H.field)
  let c : IdeleClassGroup F :=
    Additive.toMul
      ((rationalAbstractFixedFieldIdeleClassEquivFixed H.field
          (hfinite := H.finite)).symm a)
  have hvaluation :
      ((rationalCyclotomicIdeleClassValuationData.valuationAt H a :
          rationalCyclotomicIdeleClassValuationData.valueGroup) : ZHat) =
        normalizedCyclotomicZHatIdeleClassValueContinuous F
          (Additive.ofMul c) := by
    simpa only [c, ofMul_toMul,
      (rationalAbstractFixedFieldIdeleClassEquivFixed H.field
        (hfinite := H.finite)).apply_symm_apply] using
      (rationalCyclotomicIdeleClassValuationData_valuationAt_fixed_apply
        H
        ((rationalAbstractFixedFieldIdeleClassEquivFixed H.field
          (hfinite := H.finite)).symm a))
  have hleft :
      Multiplicative.toAdd
        (abstractFixedFieldCyclotomicGalEquivZHat H
          (abstractFixedFieldCyclotomicIdeleClassArtinMonoidHom H c)) =
        normalizedCyclotomicZHatIdeleClassValueContinuous F
          (Additive.ofMul c) :=
    congrArg Multiplicative.toAdd
      (abstractFixedFieldCyclotomicGalEquivZHat_ideleClassArtinMonoidHom H c)
  have hright :
      ((rationalCyclotomicIdeleClassValuationData.valuationAt H a :
          rationalCyclotomicIdeleClassValuationData.valueGroup) : ZHat) =
        Multiplicative.toAdd
          (abstractFixedFieldCyclotomicGalEquivZHat H
            (LocalClassFieldTheory.abstractExtensionQuotientEquivGaloisGroup
              ℚ (SeparableClosure ℚ) H.field
              (rationalCyclotomicDegreeData.fieldInertia H.field)
              hI hnormal
              (qInertia.symm
                (ValuationData.maximalUnramifiedNormResidueSymbol
                  rationalCyclotomicIdeleClassValuationData H a).toMul))) := by
    rw [abstractFixedFieldCyclotomicGalEquivZHat_quotientClass]
    exact
      (ValuationData.maximalUnramifiedNormResidue_degree
        rationalCyclotomicIdeleClassValuationData H a).symm
  apply (abstractFixedFieldCyclotomicGalEquivZHat H).injective
  apply Multiplicative.ext
  exact hleft.trans (hvaluation.symm.trans hright)

/-- A prime idele class has genuine maximal-unramified Artin symbol
equal to the arithmetic Frobenius of its abstract fixed field. -/
theorem
    abstractFixedFieldCyclotomicIdeleClassArtinMonoidHom_prime
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (π :
      ambientFixedAddSubgroup
        rationalIdeleClassRepresentation H.field)
    (hπ :
      rationalCyclotomicIdeleClassValuationData.IsPrimeElement H π) :
    let hI :=
      rationalCyclotomicFieldInertia_le H.field
    let hnormal :
        (CyclicCohomology.extensionSubgroup H.field
          (rationalCyclotomicDegreeData.fieldInertia H.field)
          hI).Normal := by
      rw [extensionSubgroup_rationalCyclotomicFieldInertia]
      infer_instance
    let qInertia :
        H.field.toSubgroup ⧸
            CyclicCohomology.extensionSubgroup H.field
              (rationalCyclotomicDegreeData.fieldInertia H.field)
              hI ≃*
          H.field.toSubgroup ⧸
            rationalCyclotomicDegreeData.fieldInertiaWithin H.field :=
      QuotientGroup.quotientMulEquivOfEq
        (extensionSubgroup_rationalCyclotomicFieldInertia H.field)
    abstractFixedFieldCyclotomicIdeleClassArtinMonoidHom H
        (Additive.toMul
          ((rationalAbstractFixedFieldIdeleClassEquivFixed H.field
              (hfinite := H.finite)).symm
            π)) =
      LocalClassFieldTheory.abstractExtensionQuotientEquivGaloisGroup
        ℚ (SeparableClosure ℚ) H.field
        (rationalCyclotomicDegreeData.fieldInertia H.field)
        hI hnormal
        (qInertia.symm
          (rationalCyclotomicDegreeData.frobenius
            (H.toFiniteResidueAbstractField
              rationalCyclotomicDegreeData))) := by
  let F :=
    LocalClassFieldTheory.abstractFixedField
      ℚ (SeparableClosure ℚ) H.field
  let : FiniteDimensional ℚ F :=
    LocalClassFieldTheory.abstractFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) H.field H.finite
  let : NumberField F :=
    NumberField.of_module_finite ℚ F
  let hI :=
    rationalCyclotomicFieldInertia_le H.field
  let hnormal :
      (CyclicCohomology.extensionSubgroup H.field
        (rationalCyclotomicDegreeData.fieldInertia H.field)
        hI).Normal := by
    rw [extensionSubgroup_rationalCyclotomicFieldInertia]
    infer_instance
  let qInertia :
      H.field.toSubgroup ⧸
          CyclicCohomology.extensionSubgroup H.field
            (rationalCyclotomicDegreeData.fieldInertia H.field)
            hI ≃*
        H.field.toSubgroup ⧸
          rationalCyclotomicDegreeData.fieldInertiaWithin H.field :=
    QuotientGroup.quotientMulEquivOfEq
      (extensionSubgroup_rationalCyclotomicFieldInertia H.field)
  let c :
      IdeleClassGroup F :=
    Additive.toMul
      ((rationalAbstractFixedFieldIdeleClassEquivFixed H.field
          (hfinite := H.finite)).symm π)
  have hvalue :
      normalizedCyclotomicZHatIdeleClassValueContinuous F
          ((rationalAbstractFixedFieldIdeleClassEquivFixed H.field
              (hfinite := H.finite)).symm
            π) =
        1 := by
    calc
      normalizedCyclotomicZHatIdeleClassValueContinuous F
          ((rationalAbstractFixedFieldIdeleClassEquivFixed H.field
              (hfinite := H.finite)).symm
            π) =
          ((rationalCyclotomicIdeleClassValuationData.valuationAt H
              (rationalAbstractFixedFieldIdeleClassEquivFixed H.field
                (hfinite := H.finite)
                ((rationalAbstractFixedFieldIdeleClassEquivFixed H.field
                    (hfinite := H.finite)).symm
                  π)) :
              rationalCyclotomicIdeleClassValuationData.valueGroup) :
            ZHat) := by
        exact
          (rationalCyclotomicIdeleClassValuationData_valuationAt_fixed_apply
            H
            ((rationalAbstractFixedFieldIdeleClassEquivFixed H.field
                (hfinite := H.finite)).symm
              π)).symm
      _ =
          ((rationalCyclotomicIdeleClassValuationData.oneValue :
              rationalCyclotomicIdeleClassValuationData.valueGroup) :
            ZHat) := by
        rw [(rationalAbstractFixedFieldIdeleClassEquivFixed H.field
          (hfinite := H.finite)).apply_symm_apply]
        exact congrArg Subtype.val hπ
      _ = 1 :=
        rationalCyclotomicIdeleClassValuationData.oneValue_coe
  apply (abstractFixedFieldCyclotomicGalEquivZHat H).injective
  calc
    abstractFixedFieldCyclotomicGalEquivZHat H
        (abstractFixedFieldCyclotomicIdeleClassArtinMonoidHom H c) =
        normalizedCyclotomicZHatIdeleClassValueContinuousMul F c :=
      abstractFixedFieldCyclotomicGalEquivZHat_ideleClassArtinMonoidHom
        H c
    _ = Multiplicative.ofAdd (1 : ZHat) := by
      apply Multiplicative.ext
      exact hvalue
    _ =
        abstractFixedFieldCyclotomicGalEquivZHat H
          (LocalClassFieldTheory.abstractExtensionQuotientEquivGaloisGroup
            ℚ (SeparableClosure ℚ) H.field
            (rationalCyclotomicDegreeData.fieldInertia H.field)
            hI hnormal
            (qInertia.symm
              (rationalCyclotomicDegreeData.frobenius
                (H.toFiniteResidueAbstractField
                  rationalCyclotomicDegreeData)))) := by
      rw [
        abstractFixedFieldCyclotomicGalEquivZHat_quotientClass,
        rationalCyclotomicDegreeData.maximalUnramifiedDegreeEquiv_frobenius]

end Reciprocity
end GlobalClassFieldTheory
