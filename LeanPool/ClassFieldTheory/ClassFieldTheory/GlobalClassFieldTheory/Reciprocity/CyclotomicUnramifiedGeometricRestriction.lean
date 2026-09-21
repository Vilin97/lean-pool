/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.CyclotomicUnramifiedRestriction
/-!
# Geometric restriction from the cyclotomic unramified field

An abstractly unramified finite abelian subextension is contained in the
actual cyclotomic maximal-unramified fixed field.  This file realizes that
containment as an algebra tower and proves that the finite restriction
defined on quotient presentations is literally restriction of field
automorphisms.

The field-range form of the finite layer is also bundled in the finite
Galois inverse system.  Consequently the geometric restriction of the
infinite global Artin map is the ordinary finite global Artin map.
-/

open scoped IsMulCommutative NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open ClassFormation
open GlobalClassFields
open KummerTheory
open LocalClassFieldTheory

@[reducible]
noncomputable local instance
    cyclotomicUnramifiedGeometricRationalSeparableClosureAlgebra :
    Algebra ℚ (SeparableClosure ℚ) :=
  DivisionRing.toRatAlgebra

local instance cyclotomicUnramifiedGeometricBaseQuotientFinite
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :
    Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        CyclicCohomology.extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          H.field (le_baseField H.field)) :=
  H.finite

local instance cyclotomicUnramifiedGeometricRelativeQuotientFinite
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension H.field) :
    Finite
      (H.field.toSubgroup ⧸
        CyclicCohomology.extensionSubgroup
          H.field L.field L.below) :=
  L.finite

noncomputable local instance
    cyclotomicUnramifiedGeometricBaseFiniteDimensional
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :
    FiniteDimensional ℚ
      (abstractFixedField ℚ (SeparableClosure ℚ) H.field) :=
  abstractFixedField_finiteDimensional
    ℚ (SeparableClosure ℚ) H.field H.finite

noncomputable local instance
    cyclotomicUnramifiedGeometricRelativeFiniteDimensional
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension H.field) :
    FiniteDimensional
      (abstractFixedField ℚ (SeparableClosure ℚ) H.field)
      (abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) L.below) :=
  finiteAbelianSubextensionAbstractRelativeFixedFieldFiniteDimensional L

local instance
    cyclotomicUnramifiedGeometricRelativeScalarTower
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension H.field) :
    IsScalarTower ℚ
      (abstractFixedField ℚ (SeparableClosure ℚ) H.field)
      (abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) L.below) :=
  IsScalarTower.of_algebraMap_eq' rfl

noncomputable local instance
    cyclotomicUnramifiedGeometricRelativeAbsoluteFiniteDimensional
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension H.field) :
    FiniteDimensional ℚ
      (abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) L.below) :=
  FiniteDimensional.trans ℚ
    (abstractFixedField ℚ (SeparableClosure ℚ) H.field)
    (abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) L.below)

noncomputable local instance
    cyclotomicUnramifiedGeometricBaseNumberField
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :
    NumberField
      (abstractFixedField ℚ (SeparableClosure ℚ) H.field) :=
  NumberField.of_module_finite ℚ
    (abstractFixedField ℚ (SeparableClosure ℚ) H.field)

noncomputable local instance
    cyclotomicUnramifiedGeometricRelativeNumberField
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension H.field) :
    NumberField
      (abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) L.below) :=
  NumberField.of_module_finite ℚ
    (abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) L.below)

noncomputable local instance
    cyclotomicUnramifiedGeometricRelativeIsAbelianGalois
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension H.field) :
    IsAbelianGalois
      (abstractFixedField ℚ (SeparableClosure ℚ) H.field)
      (abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) L.below) :=
  finiteAbelianSubextensionAbstractRelativeFixedFieldIsAbelianGalois L

noncomputable local instance
    cyclotomicUnramifiedGeometricRelativeNormal
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension H.field) :
    Normal
      (abstractFixedField ℚ (SeparableClosure ℚ) H.field)
      (abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) L.below) :=
  (cyclotomicUnramifiedGeometricRelativeIsAbelianGalois
    H L).toIsGalois.to_normal

noncomputable local instance
    cyclotomicUnramifiedGeometricMaximalIsAbelianGalois
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :
    IsAbelianGalois
      (abstractFixedField ℚ (SeparableClosure ℚ) H.field)
      (abstractRelativeFixedField
        ℚ (SeparableClosure ℚ)
        (rationalCyclotomicFieldInertia_le H.field)) :=
  abstractFixedFieldCyclotomic_isAbelianGalois H

/-- An unramified finite fixed field lies in the cyclotomic
maximal-unramified fixed field. -/
theorem abstractFixedFieldCyclotomicFiniteUnramifiedField_le
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension H.field)
    (hUnramified :
      L.toFiniteGaloisExtension.IsUnramified
        rationalCyclotomicDegreeData) :
    abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) L.below ≤
      abstractRelativeFixedField
        ℚ (SeparableClosure ℚ)
        (rationalCyclotomicFieldInertia_le H.field) := by
  apply abstractFixedField_le
  exact
    (L.toFiniteGaloisExtension.isUnramified_iff_inertia_le
      rationalCyclotomicDegreeData).1 hUnramified

/-- The actual inclusion of an unramified finite fixed field into the
cyclotomic maximal-unramified field, over the common fixed base. -/
noncomputable def
    abstractFixedFieldCyclotomicFiniteUnramifiedInclusion
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension H.field)
    (hUnramified :
      L.toFiniteGaloisExtension.IsUnramified
        rationalCyclotomicDegreeData) :
    let F :=
      abstractFixedField ℚ (SeparableClosure ℚ) H.field
    let E :=
      abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) L.below
    let U :=
      abstractRelativeFixedField
        ℚ (SeparableClosure ℚ)
        (rationalCyclotomicFieldInertia_le H.field)
    E →ₐ[F] U := by
  dsimp only
  let F :=
    abstractFixedField ℚ (SeparableClosure ℚ) H.field
  let E :=
    abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) L.below
  let U :=
    abstractRelativeFixedField
      ℚ (SeparableClosure ℚ)
      (rationalCyclotomicFieldInertia_le H.field)
  let j : E →ₐ[ℚ] U :=
    IntermediateField.inclusion
      (abstractFixedFieldCyclotomicFiniteUnramifiedField_le
        H L hUnramified)
  exact
    { j.toRingHom with
      commutes' := fun _ => by
        apply Subtype.ext
        rfl }

/-- The algebra structure induced by the geometric inclusion of the
finite unramified fixed field into the cyclotomic maximal-unramified
field. -/
@[implicit_reducible]
noncomputable def
    abstractFixedFieldCyclotomicFiniteUnramifiedInclusionAlgebra
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension H.field)
    (hUnramified :
      L.toFiniteGaloisExtension.IsUnramified
        rationalCyclotomicDegreeData) :
    let E :=
      abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) L.below
    let U :=
      abstractRelativeFixedField
        ℚ (SeparableClosure ℚ)
        (rationalCyclotomicFieldInertia_le H.field)
    Algebra E U :=
  (abstractFixedFieldCyclotomicFiniteUnramifiedInclusion
    H L hUnramified).toRingHom.toAlgebra

/-- The scalar action belonging to the inclusion-induced algebra
structure.  Naming it prevents typeclass search from exploring the
unrelated intermediate-field algebra paths. -/
@[implicit_reducible]
noncomputable def
    abstractFixedFieldCyclotomicFiniteUnramifiedInclusionSMul
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension H.field)
    (hUnramified :
      L.toFiniteGaloisExtension.IsUnramified
        rationalCyclotomicDegreeData) :
    let E :=
      abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) L.below
    let U :=
      abstractRelativeFixedField
        ℚ (SeparableClosure ℚ)
        (rationalCyclotomicFieldInertia_le H.field)
    SMul E U :=
  Algebra.toSMul
    (self :=
      abstractFixedFieldCyclotomicFiniteUnramifiedInclusionAlgebra
        H L hUnramified)

/-- The scalar tower induced by the same geometric inclusion.  This
single construction is reused by restriction and Artin compatibility. -/
theorem
    abstractFixedFieldCyclotomicFiniteUnramifiedInclusionScalarTower
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension H.field)
    (hUnramified :
      L.toFiniteGaloisExtension.IsUnramified
        rationalCyclotomicDegreeData) :
    let F :=
      abstractFixedField ℚ (SeparableClosure ℚ) H.field
    let E :=
      abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) L.below
    let U :=
      abstractRelativeFixedField
        ℚ (SeparableClosure ℚ)
        (rationalCyclotomicFieldInertia_le H.field)
    letI _ : Algebra E U :=
      abstractFixedFieldCyclotomicFiniteUnramifiedInclusionAlgebra
        H L hUnramified
    letI _ : SMul E U :=
      abstractFixedFieldCyclotomicFiniteUnramifiedInclusionSMul
        H L hUnramified
    IsScalarTower F E U := by
  dsimp only
  let F :=
    abstractFixedField ℚ (SeparableClosure ℚ) H.field
  let E :=
    abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) L.below
  let U :=
    abstractRelativeFixedField
      ℚ (SeparableClosure ℚ)
      (rationalCyclotomicFieldInertia_le H.field)
  let _ : Algebra E U :=
    abstractFixedFieldCyclotomicFiniteUnramifiedInclusionAlgebra
      H L hUnramified
  let _ : SMul E U :=
    abstractFixedFieldCyclotomicFiniteUnramifiedInclusionSMul
      H L hUnramified
  exact IsScalarTower.of_algHom
    (abstractFixedFieldCyclotomicFiniteUnramifiedInclusion
      H L hUnramified)

/-- Normality of the extension subgroup defining the cyclotomic
maximal-unramified layer.  Naming it keeps the quotient equivalence and
its evaluation lemma on the same proof parameter. -/
private instance cyclotomicUnramifiedGeometricMaxExtensionNormal
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :
    (CyclicCohomology.extensionSubgroup H.field
        (rationalCyclotomicDegreeData.fieldInertia H.field)
        (rationalCyclotomicFieldInertia_le H.field)).Normal :=
  (extensionSubgroup_rationalCyclotomicFieldInertia H.field).symm ▸
    DegreeData.fieldInertiaWithin_normal
      rationalCyclotomicDegreeData H.field

/-- The quotient presentation of the cyclotomic maximal-unramified
Galois group used by geometric restriction. -/
private noncomputable abbrev
    cyclotomicUnramifiedGeometricMaxQuotientEquiv
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :
    H.field.toSubgroup ⧸
          CyclicCohomology.extensionSubgroup H.field
            (rationalCyclotomicDegreeData.fieldInertia H.field)
            (rationalCyclotomicFieldInertia_le H.field) ≃*
      Gal(
        abstractRelativeFixedField
            ℚ (SeparableClosure ℚ)
            (rationalCyclotomicFieldInertia_le H.field) /
          abstractFixedField ℚ (SeparableClosure ℚ) H.field) :=
  LocalClassFieldTheory.abstractExtensionQuotientEquivGaloisGroup
    ℚ (SeparableClosure ℚ) H.field
    (rationalCyclotomicDegreeData.fieldInertia H.field)
    (rationalCyclotomicFieldInertia_le H.field)
    (cyclotomicUnramifiedGeometricMaxExtensionNormal H)

/-- The equality of the two inertia subgroups, bundled once as the
quotient equivalence used by geometric restriction. -/
private noncomputable abbrev
    cyclotomicUnramifiedGeometricInertiaQuotientEquiv
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :
    H.field.toSubgroup ⧸
          CyclicCohomology.extensionSubgroup H.field
            (rationalCyclotomicDegreeData.fieldInertia H.field)
            (rationalCyclotomicFieldInertia_le H.field) ≃*
      H.field.toSubgroup ⧸
        rationalCyclotomicDegreeData.fieldInertiaWithin H.field :=
  by
    letI maxExtensionNormal :
        (CyclicCohomology.extensionSubgroup H.field
          (rationalCyclotomicDegreeData.fieldInertia H.field)
          (rationalCyclotomicFieldInertia_le H.field)).Normal :=
      cyclotomicUnramifiedGeometricMaxExtensionNormal H
    exact @QuotientGroup.quotientMulEquivOfEq
      _ _ _ _ maxExtensionNormal
      (DegreeData.fieldInertiaWithin_normal
        rationalCyclotomicDegreeData H.field)
      (extensionSubgroup_rationalCyclotomicFieldInertia H.field)

/-- The quotient presentation of the finite fixed-field Galois group
used throughout the geometric comparison. -/
private noncomputable abbrev
    cyclotomicUnramifiedGeometricFiniteQuotientEquiv
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension H.field) :
    L.toFiniteGaloisExtension.extensionQuotient ≃*
      Gal(
        abstractRelativeFixedField
            ℚ (SeparableClosure ℚ) L.below /
          abstractFixedField ℚ (SeparableClosure ℚ) H.field) :=
  L.toFiniteGaloisExtension.extensionQuotientMulEquiv.trans
    (LocalClassFieldTheory.abstractExtensionQuotientEquivGaloisGroup
      ℚ (SeparableClosure ℚ)
      H.field L.field L.below L.normal)

/-- The finite restriction in the geometric quotient coordinate. -/
private theorem cyclotomicUnramifiedGeometricRestriction_apply
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension H.field)
    (hUnramified :
      L.toFiniteGaloisExtension.IsUnramified rationalCyclotomicDegreeData)
    (σ : Gal(
      abstractRelativeFixedField ℚ (SeparableClosure ℚ)
          (rationalCyclotomicFieldInertia_le H.field) /
        abstractFixedField ℚ (SeparableClosure ℚ) H.field)) :
    abstractFixedFieldCyclotomicFiniteRestrictionMonoidHom
        H L hUnramified σ =
      (L.toFiniteGaloisExtension.extensionQuotientMulEquiv.trans
        (LocalClassFieldTheory.abstractExtensionQuotientEquivGaloisGroup
          ℚ (SeparableClosure ℚ)
          H.field L.field L.below L.normal))
        (DegreeData.finiteUnramifiedRestriction
          rationalCyclotomicDegreeData
          (H.toFiniteResidueAbstractField rationalCyclotomicDegreeData)
          L.toFiniteGaloisExtension hUnramified
          ((cyclotomicUnramifiedGeometricInertiaQuotientEquiv H)
            ((cyclotomicUnramifiedGeometricMaxQuotientEquiv H).symm σ))) := by
  let qMax := cyclotomicUnramifiedGeometricMaxQuotientEquiv H
  let qInertia := cyclotomicUnramifiedGeometricInertiaQuotientEquiv H
  let degreeEquiv :=
    rationalCyclotomicDegreeData.maximalUnramifiedDegreeEquiv
      (H.toFiniteResidueAbstractField rationalCyclotomicDegreeData)
  let finiteRestriction :=
    DegreeData.finiteUnramifiedRestriction
      rationalCyclotomicDegreeData
      (H.toFiniteResidueAbstractField rationalCyclotomicDegreeData)
      L.toFiniteGaloisExtension hUnramified
  have hCoordinate :=
    abstractFixedFieldCyclotomicGalEquivZHat_quotientClass H
      (qInertia (qMax.symm σ))
  have hCoordinate' :
      abstractFixedFieldCyclotomicGalEquivZHat H σ =
        degreeEquiv (qInertia (qMax.symm σ)) := by
    change
      abstractFixedFieldCyclotomicGalEquivZHat H
          (qMax (qInertia.symm (qInertia (qMax.symm σ)))) =
        degreeEquiv (qInertia (qMax.symm σ)) at hCoordinate
    rw [qInertia.symm_apply_apply] at hCoordinate
    exact (congrArg (abstractFixedFieldCyclotomicGalEquivZHat H)
      (qMax.apply_symm_apply σ)).symm.trans hCoordinate
  have hArg :
      degreeEquiv.symm
          (abstractFixedFieldCyclotomicGalEquivZHat H σ) =
        qInertia (qMax.symm σ) :=
    (congrArg degreeEquiv.symm hCoordinate').trans
      (degreeEquiv.symm_apply_apply _)
  calc
    _ = (L.toFiniteGaloisExtension.extensionQuotientMulEquiv.trans
        (LocalClassFieldTheory.abstractExtensionQuotientEquivGaloisGroup
          ℚ (SeparableClosure ℚ)
          H.field L.field L.below L.normal))
        (finiteRestriction
          (degreeEquiv.symm
            (abstractFixedFieldCyclotomicGalEquivZHat H σ))) :=
      abstractFixedFieldCyclotomicFiniteRestrictionMonoidHom_apply
        H L hUnramified σ
    _ = _ :=
      congrArg
        (fun q =>
          (L.toFiniteGaloisExtension.extensionQuotientMulEquiv.trans
            (LocalClassFieldTheory.abstractExtensionQuotientEquivGaloisGroup
              ℚ (SeparableClosure ℚ)
              H.field L.field L.below L.normal))
            (finiteRestriction q)) hArg

/-- On a representative of the maximal-unramified quotient, finite
restriction is restriction of the corresponding field automorphism. -/
private theorem cyclotomicUnramifiedGeometricRestriction_mk
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension H.field)
    (hUnramified :
      L.toFiniteGaloisExtension.IsUnramified rationalCyclotomicDegreeData)
    (τ : H.field.toSubgroup) :
    let F := abstractFixedField ℚ (SeparableClosure ℚ) H.field
    let E := abstractRelativeFixedField ℚ (SeparableClosure ℚ) L.below
    let U := abstractRelativeFixedField ℚ (SeparableClosure ℚ)
      (rationalCyclotomicFieldInertia_le H.field)
    letI _ : Algebra E U :=
      abstractFixedFieldCyclotomicFiniteUnramifiedInclusionAlgebra
        H L hUnramified
    letI _ : @IsScalarTower F E U
        Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
      IsScalarTower.of_algHom
        (abstractFixedFieldCyclotomicFiniteUnramifiedInclusion
          H L hUnramified)
    (cyclotomicUnramifiedGeometricFiniteQuotientEquiv H L)
      (DegreeData.finiteUnramifiedRestriction
        rationalCyclotomicDegreeData
        (H.toFiniteResidueAbstractField rationalCyclotomicDegreeData)
        L.toFiniteGaloisExtension hUnramified
        ((cyclotomicUnramifiedGeometricInertiaQuotientEquiv H)
          (QuotientGroup.mk τ))) =
      AlgEquiv.restrictNormalHom E
        ((cyclotomicUnramifiedGeometricMaxQuotientEquiv H)
          (QuotientGroup.mk τ)) := by
  dsimp only
  let F := abstractFixedField ℚ (SeparableClosure ℚ) H.field
  let E := abstractRelativeFixedField ℚ (SeparableClosure ℚ) L.below
  let hI := rationalCyclotomicFieldInertia_le H.field
  let U := abstractRelativeFixedField ℚ (SeparableClosure ℚ) hI
  let _ : Algebra E U :=
    abstractFixedFieldCyclotomicFiniteUnramifiedInclusionAlgebra
      H L hUnramified
  let _ : @IsScalarTower F E U
      Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    IsScalarTower.of_algHom
      (abstractFixedFieldCyclotomicFiniteUnramifiedInclusion
        H L hUnramified)
  let qMax := cyclotomicUnramifiedGeometricMaxQuotientEquiv H
  let qInertia := cyclotomicUnramifiedGeometricInertiaQuotientEquiv H
  let qFinite := cyclotomicUnramifiedGeometricFiniteQuotientEquiv H L
  let finiteRestriction :=
    DegreeData.finiteUnramifiedRestriction
      rationalCyclotomicDegreeData
      (H.toFiniteResidueAbstractField rationalCyclotomicDegreeData)
      L.toFiniteGaloisExtension hUnramified
  have hInertia :
      qInertia (QuotientGroup.mk τ) =
        (QuotientGroup.mk τ :
          H.field.toSubgroup ⧸
            rationalCyclotomicDegreeData.fieldInertiaWithin H.field) :=
    QuotientGroup.quotientMulEquivOfEq_mk
      (extensionSubgroup_rationalCyclotomicFieldInertia H.field) τ
  refine (congrArg (fun z => qFinite (finiteRestriction z)) hInertia).trans ?_
  have hFiniteRestriction :=
    DegreeData.finiteUnramifiedRestriction_mk
      rationalCyclotomicDegreeData
      (H.toFiniteResidueAbstractField rationalCyclotomicDegreeData)
      L.toFiniteGaloisExtension hUnramified τ
  refine (congrArg qFinite hFiniteRestriction).trans ?_
  apply AlgEquiv.ext
  intro x
  apply Subtype.ext
  have hE :=
    LocalClassFieldTheory.abstractExtensionQuotientEquivGaloisGroup_mk_apply_val
      ℚ (SeparableClosure ℚ)
      H.field L.field L.below L.normal τ x
  have hU :=
    LocalClassFieldTheory.abstractExtensionQuotientEquivGaloisGroup_mk_apply_val
      ℚ (SeparableClosure ℚ)
      H.field
      (rationalCyclotomicDegreeData.fieldInertia H.field)
      hI (cyclotomicUnramifiedGeometricMaxExtensionNormal H) τ
      (algebraMap E U x)
  change
    τ.1 ((algebraMap E U x : U).1) =
      (qMax (QuotientGroup.mk τ) (algebraMap E U x)).1 at hU
  have hInclusion :
      ((algebraMap E U x : U) : SeparableClosure ℚ) =
        (x : SeparableClosure ℚ) :=
    rfl
  have hτ := congrArg
    (fun y : SeparableClosure ℚ => τ.1 y) hInclusion.symm
  have hRestrict :=
    AlgEquiv.restrictNormal_commutes
      (qMax (QuotientGroup.mk τ)) E x
  have hRestrictVal := congrArg
    (fun y : U => (y : SeparableClosure ℚ)) hRestrict
  exact hE.symm.trans (hτ.trans (hU.trans hRestrictVal.symm))

/-- Geometric restriction on an arbitrary maximal-unramified quotient class. -/
private theorem cyclotomicUnramifiedGeometricRestriction_quotient
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension H.field)
    (hUnramified :
      L.toFiniteGaloisExtension.IsUnramified rationalCyclotomicDegreeData)
    (q : H.field.toSubgroup ⧸
      CyclicCohomology.extensionSubgroup H.field
        (rationalCyclotomicDegreeData.fieldInertia H.field)
        (rationalCyclotomicFieldInertia_le H.field)) :
    let F := abstractFixedField ℚ (SeparableClosure ℚ) H.field
    let E := abstractRelativeFixedField ℚ (SeparableClosure ℚ) L.below
    let U := abstractRelativeFixedField ℚ (SeparableClosure ℚ)
      (rationalCyclotomicFieldInertia_le H.field)
    letI _ : Algebra E U :=
      abstractFixedFieldCyclotomicFiniteUnramifiedInclusionAlgebra
        H L hUnramified
    letI _ : @IsScalarTower F E U
        Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
      IsScalarTower.of_algHom
        (abstractFixedFieldCyclotomicFiniteUnramifiedInclusion
          H L hUnramified)
    abstractFixedFieldCyclotomicFiniteRestrictionMonoidHom
        H L hUnramified
        ((cyclotomicUnramifiedGeometricMaxQuotientEquiv H) q) =
      AlgEquiv.restrictNormalHom E
        ((cyclotomicUnramifiedGeometricMaxQuotientEquiv H) q) := by
  dsimp only
  induction q using QuotientGroup.induction_on with
  | _ τ =>
      let qMax := cyclotomicUnramifiedGeometricMaxQuotientEquiv H
      let qInertia := cyclotomicUnramifiedGeometricInertiaQuotientEquiv H
      let qFinite := cyclotomicUnramifiedGeometricFiniteQuotientEquiv H L
      let finiteRestriction :=
        DegreeData.finiteUnramifiedRestriction
          rationalCyclotomicDegreeData
          (H.toFiniteResidueAbstractField rationalCyclotomicDegreeData)
          L.toFiniteGaloisExtension hUnramified
      have hProjection :
          qInertia (qMax.symm (qMax (QuotientGroup.mk τ))) =
            qInertia (QuotientGroup.mk τ) :=
        congrArg qInertia (qMax.symm_apply_apply (QuotientGroup.mk τ))
      calc
        _ = qFinite
            (finiteRestriction
              (qInertia (qMax.symm (qMax (QuotientGroup.mk τ))))) :=
          cyclotomicUnramifiedGeometricRestriction_apply
            H L hUnramified (qMax (QuotientGroup.mk τ))
        _ = qFinite
            (finiteRestriction (qInertia (QuotientGroup.mk τ))) :=
          congrArg (fun z => qFinite (finiteRestriction z)) hProjection
        _ = _ :=
          cyclotomicUnramifiedGeometricRestriction_mk H L hUnramified τ

/-- The quotient-defined restriction to a finite unramified
subextension is the genuine restriction of automorphisms of its
cyclotomic maximal-unramified overfield. -/
theorem
    abstractFixedFieldCyclotomicFiniteRestrictionMonoidHom_eq_restrictNormalHom
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension H.field)
    (hUnramified :
      L.toFiniteGaloisExtension.IsUnramified
        rationalCyclotomicDegreeData) :
    let F :=
      abstractFixedField ℚ (SeparableClosure ℚ) H.field
    let E :=
      abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) L.below
    let U :=
      abstractRelativeFixedField
        ℚ (SeparableClosure ℚ)
        (rationalCyclotomicFieldInertia_le H.field)
    letI _ : Algebra E U :=
      abstractFixedFieldCyclotomicFiniteUnramifiedInclusionAlgebra
        H L hUnramified
    letI _ : @IsScalarTower F E U
        Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
      IsScalarTower.of_algHom
        (abstractFixedFieldCyclotomicFiniteUnramifiedInclusion
          H L hUnramified)
    abstractFixedFieldCyclotomicFiniteRestrictionMonoidHom
        H L hUnramified =
      (AlgEquiv.restrictNormalHom E :
        (U ≃ₐ[F] U) →* (E ≃ₐ[F] E)) := by
  dsimp only
  apply MonoidHom.ext
  intro σ
  have hσ :
      (cyclotomicUnramifiedGeometricMaxQuotientEquiv H)
          ((cyclotomicUnramifiedGeometricMaxQuotientEquiv H).symm σ) = σ :=
    (cyclotomicUnramifiedGeometricMaxQuotientEquiv H).apply_symm_apply σ
  exact hσ ▸
    (cyclotomicUnramifiedGeometricRestriction_quotient
      H L hUnramified
      ((cyclotomicUnramifiedGeometricMaxQuotientEquiv H).symm σ))

/-- Restriction of the infinite Artin map along a finite abelian embedding.

The field-range coordinate is constructed only over abstract type variables.
This keeps concrete fixed-field terms out of definitional equality while the
two existing finite-coordinate compatibility theorems are composed. -/
private theorem
    restrictNormalHom_infiniteGlobalArtinMonoidHom_of_tower
    (K E Ω : Type) [Field K] [NumberField K]
    [Field E] [NumberField E] [Algebra K E]
    [IsAbelianGalois K E]
    [Field Ω] [Algebra K Ω] [Algebra E Ω]
    [IsScalarTower K E Ω] [IsAbelianGalois K Ω]
    (a : IdeleGroup K) :
    AlgEquiv.restrictNormalHom E
        (infiniteGlobalArtinMonoidHom K Ω a) =
      globalArtinMonoidHom (K := K) (L := E) a := by
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

/-- Pointwise form of restriction compatibility for the infinite Artin map.
This hides the equality of large automorphism structures before specializing
to concrete fixed fields. -/
private theorem
    restrictNormalHom_infiniteGlobalArtinMonoidHom_apply_of_tower
    (K E Ω : Type) [Field K] [NumberField K]
    [Field E] [NumberField E] [Algebra K E]
    [IsAbelianGalois K E]
    [Field Ω] [Algebra K Ω] [Algebra E Ω]
    [IsScalarTower K E Ω] [IsAbelianGalois K Ω]
    (a : IdeleGroup K) (x : E) :
    AlgEquiv.restrictNormalHom E
        (infiniteGlobalArtinMonoidHom K Ω a) x =
      globalArtinMonoidHom (K := K) (L := E) a x := by
  exact DFunLike.congr_fun
    (restrictNormalHom_infiniteGlobalArtinMonoidHom_of_tower K E Ω a) x

/-- After embedding the finite field into the overfield, pointwise restriction
compatibility is an equality in the common ambient field. -/
private theorem
    algebraMap_restrictNormalHom_infiniteGlobalArtinMonoidHom_apply_of_tower
    (K E Ω : Type) [Field K] [NumberField K]
    [Field E] [NumberField E] [Algebra K E]
    [IsAbelianGalois K E]
    [Field Ω] [Algebra K Ω] [Algebra E Ω]
    [IsScalarTower K E Ω] [IsAbelianGalois K Ω]
    (a : IdeleGroup K) (x : E) :
    algebraMap E Ω
        (AlgEquiv.restrictNormalHom E
          (infiniteGlobalArtinMonoidHom K Ω a) x) =
      algebraMap E Ω
        (globalArtinMonoidHom (K := K) (L := E) a x) := by
  exact congrArg (algebraMap E Ω)
    (restrictNormalHom_infiniteGlobalArtinMonoidHom_apply_of_tower
      K E Ω a x)

/-- Genuine restriction from the cyclotomic unramified overfield carries the
infinite Artin symbol to the finite Artin symbol. -/
private theorem
    abstractFixedFieldCyclotomicRestrictNormalHom_infiniteGlobalArtinMonoidHom
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension H.field)
    (hUnramified :
      L.toFiniteGaloisExtension.IsUnramified
        rationalCyclotomicDegreeData)
    (a : IdeleGroup
      (abstractFixedField ℚ (SeparableClosure ℚ) H.field)) :
    let F :=
      abstractFixedField ℚ (SeparableClosure ℚ) H.field
    let E :=
      abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) L.below
    let U :=
      abstractRelativeFixedField
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
    AlgEquiv.restrictNormalHom E
        (infiniteGlobalArtinMonoidHom F U a) =
      globalArtinMonoidHom (K := F) (L := E) a := by
  dsimp only
  let F :=
    abstractFixedField ℚ (SeparableClosure ℚ) H.field
  let E :=
    abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) L.below
  let U :=
    abstractRelativeFixedField
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
  apply AlgEquiv.ext
  intro x
  apply Subtype.ext
  have hAmbient :=
    @algebraMap_restrictNormalHom_infiniteGlobalArtinMonoidHom_apply_of_tower
      F E U
      (inferInstance : Field F) fNumberField
      (inferInstance : Field E) eNumberField fEAlgebra
      fEIsAbelianGalois
      (inferInstance : Field U) fUAlgebra eUAlgebra
      fEUTower fUIsAbelianGalois
      a x
  have hAmbientVal := congrArg
    (fun y : U => (y : SeparableClosure ℚ))
    hAmbient
  have hLeft :
      ((algebraMap E U
          ((AlgEquiv.restrictNormalHom E
            (infiniteGlobalArtinMonoidHom F U a)) x) : U) :
        SeparableClosure ℚ) =
        (((AlgEquiv.restrictNormalHom E
          (infiniteGlobalArtinMonoidHom F U a)) x : E) :
          SeparableClosure ℚ) := by
    rfl
  have hRight :
      ((algebraMap E U
          ((globalArtinMonoidHom (K := F) (L := E) a) x) : U) :
        SeparableClosure ℚ) =
        (((globalArtinMonoidHom (K := F) (L := E) a) x : E) :
          SeparableClosure ℚ) := by
    rfl
  rw [← hLeft, hAmbientVal, hRight]

/-- Applying the geometric finite restriction to the infinite global
Artin symbol gives the ordinary finite global Artin symbol. -/
theorem
    abstractFixedFieldCyclotomicFiniteRestriction_infiniteGlobalArtinMonoidHom
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension H.field)
    (hUnramified :
      L.toFiniteGaloisExtension.IsUnramified
        rationalCyclotomicDegreeData)
    (a : IdeleGroup
      (abstractFixedField ℚ (SeparableClosure ℚ) H.field)) :
    let F :=
      abstractFixedField ℚ (SeparableClosure ℚ) H.field
    let E :=
      abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) L.below
    let U :=
      abstractRelativeFixedField
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
    abstractFixedFieldCyclotomicFiniteRestrictionMonoidHom
        H L hUnramified
        (infiniteGlobalArtinMonoidHom F U a) =
      globalArtinMonoidHom (K := F) (L := E) a := by
  dsimp only
  let F :=
    abstractFixedField ℚ (SeparableClosure ℚ) H.field
  let E :=
    abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) L.below
  let U :=
    abstractRelativeFixedField
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
  apply AlgEquiv.ext
  intro x
  have hRestrictionValue := DFunLike.congr_fun
    (DFunLike.congr_fun
      (abstractFixedFieldCyclotomicFiniteRestrictionMonoidHom_eq_restrictNormalHom
        H L hUnramified)
      (infiniteGlobalArtinMonoidHom
        (abstractFixedField ℚ (SeparableClosure ℚ) H.field)
        (abstractRelativeFixedField ℚ (SeparableClosure ℚ)
          (rationalCyclotomicFieldInertia_le H.field))
        a))
    x
  have hArtinValue := DFunLike.congr_fun
    (abstractFixedFieldCyclotomicRestrictNormalHom_infiniteGlobalArtinMonoidHom
      H L hUnramified a)
    x
  exact hRestrictionValue.trans hArtinValue

end Reciprocity
end GlobalClassFieldTheory
