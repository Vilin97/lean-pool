/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.AbstractFixedFieldGlobalNormResidue
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.CyclotomicAbstractFixedFieldArtin
/-!
# Finite restriction of cyclotomic fixed-field reciprocity

For an unramified finite abelian subextension of an abstract fixed
number field, this file constructs the genuine restriction from the
cyclotomic maximal-unramified Galois group to the finite Galois group.
It then identifies the restriction of the chosen-local-factor
cyclotomic Artin map with the actual global norm-residue map.
-/

open scoped IsMulCommutative NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open ClassFormation
open KummerTheory

/-- The actual fixed field attached to `H` is a number field.  Keeping
this as one file-local instance makes it available while later idele-class
binders are elaborated. -/
noncomputable local instance
    cyclotomicUnramifiedRestriction_abstractFixedFieldNumberField
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

/-- The abelianized fixed-field quotient comparison sends the class of
an actual finite quotient element to the corresponding automorphism of
the concrete relative fixed field. -/
@[simp]
theorem
    abstractFixedFieldAbelianizedExtensionQuotientEquivGaloisGroup_of
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension H.field)
    (q : L.extensionQuotient) :
    abstractFixedFieldAbelianizedExtensionQuotientEquivGaloisGroup H L
        (Additive.ofMul (Abelianization.of q)) =
      Additive.ofMul
        ((L.extensionQuotientMulEquiv.trans
          (LocalClassFieldTheory.abstractExtensionQuotientEquivGaloisGroup
            ℚ (SeparableClosure ℚ)
            H.field L.field L.below L.normal)) q) := by
  let : IsMulCommutative L.extensionQuotient :=
    L.commutative
  apply Additive.toMul.injective
  change
    (L.extensionQuotientMulEquiv.trans
      (LocalClassFieldTheory.abstractExtensionQuotientEquivGaloisGroup
        ℚ (SeparableClosure ℚ)
        H.field L.field L.below L.normal))
      ((Abelianization.equivOfComm :
          L.extensionQuotient ≃*
            Abelianization L.extensionQuotient).symm
        (Abelianization.of q)) =
      (L.extensionQuotientMulEquiv.trans
        (LocalClassFieldTheory.abstractExtensionQuotientEquivGaloisGroup
          ℚ (SeparableClosure ℚ)
          H.field L.field L.below L.normal)) q
  exact congrArg
    (L.extensionQuotientMulEquiv.trans
      (LocalClassFieldTheory.abstractExtensionQuotientEquivGaloisGroup
        ℚ (SeparableClosure ℚ)
        H.field L.field L.below L.normal))
    ((Abelianization.equivOfComm :
      L.extensionQuotient ≃*
        Abelianization L.extensionQuotient).symm_apply_apply q)

/-- Genuine restriction from the cyclotomic maximal-unramified
extension of an abstract fixed field to a finite unramified abelian
subextension.  The construction uses the canonical quotient
presentations of both actual Galois groups. -/
noncomputable def abstractFixedFieldCyclotomicFiniteRestrictionMonoidHom
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
    let hI :=
      rationalCyclotomicFieldInertia_le H.field
    let U :=
      LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) hI
    Gal(U/F) →* Gal(E/F) := by
  dsimp only
  let qFinite :
      L.toFiniteGaloisExtension.extensionQuotient ≃*
        Gal(
          LocalClassFieldTheory.abstractRelativeFixedField
            ℚ (SeparableClosure ℚ) L.below/LocalClassFieldTheory.abstractFixedField
            ℚ (SeparableClosure ℚ) H.field) :=
    L.toFiniteGaloisExtension.extensionQuotientMulEquiv.trans
      (LocalClassFieldTheory.abstractExtensionQuotientEquivGaloisGroup
        ℚ (SeparableClosure ℚ)
        H.field L.field L.below L.normal)
  let finiteRestriction :=
    DegreeData.finiteUnramifiedRestriction
      rationalCyclotomicDegreeData
      (H.toFiniteResidueAbstractField rationalCyclotomicDegreeData)
      L.toFiniteGaloisExtension hUnramified
  let degreeEquiv :=
    rationalCyclotomicDegreeData.maximalUnramifiedDegreeEquiv
      (H.toFiniteResidueAbstractField rationalCyclotomicDegreeData)
  let galEquiv := abstractFixedFieldCyclotomicGalEquivZHat H
  exact
    @MonoidHom.comp _ _ _ _ _ _ qFinite.toMonoidHom
      (@MonoidHom.comp _ _ _ _ _ _ finiteRestriction
        (@MonoidHom.comp _ _ _ _ _ _
          degreeEquiv.symm.toMonoidHom galEquiv.toMonoidHom))

/-- Evaluate the finite cyclotomic restriction through its quotient coordinates. -/
theorem abstractFixedFieldCyclotomicFiniteRestrictionMonoidHom_apply
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension H.field)
    (hUnramified :
      L.toFiniteGaloisExtension.IsUnramified
        rationalCyclotomicDegreeData)
    (σ : Gal(
      LocalClassFieldTheory.abstractRelativeFixedField
          ℚ (SeparableClosure ℚ)
          (rationalCyclotomicFieldInertia_le H.field)/LocalClassFieldTheory.abstractFixedField
          ℚ (SeparableClosure ℚ) H.field)) :
    abstractFixedFieldCyclotomicFiniteRestrictionMonoidHom H L hUnramified σ =
      (L.toFiniteGaloisExtension.extensionQuotientMulEquiv.trans
        (LocalClassFieldTheory.abstractExtensionQuotientEquivGaloisGroup
          ℚ (SeparableClosure ℚ)
          H.field L.field L.below L.normal))
        (DegreeData.finiteUnramifiedRestriction
          rationalCyclotomicDegreeData
          (H.toFiniteResidueAbstractField rationalCyclotomicDegreeData)
          L.toFiniteGaloisExtension hUnramified
          ((rationalCyclotomicDegreeData.maximalUnramifiedDegreeEquiv
            (H.toFiniteResidueAbstractField
              rationalCyclotomicDegreeData)).symm
            (abstractFixedFieldCyclotomicGalEquivZHat H σ))) := by
  rfl

/-- In the canonical `ZHat` coordinate, the genuine cyclotomic Artin
symbol recovers the abstract maximal-unramified quotient class. -/
private theorem
    abstractFixedFieldCyclotomicIdeleClassArtin_fixed_coordinate
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (a :
      ambientFixedAddSubgroup
        rationalIdeleClassRepresentation H.field) :
    (rationalCyclotomicDegreeData.maximalUnramifiedDegreeEquiv
        (H.toFiniteResidueAbstractField
          rationalCyclotomicDegreeData)).symm
        (abstractFixedFieldCyclotomicGalEquivZHat H
          (abstractFixedFieldCyclotomicIdeleClassArtinMonoidHom H
            (Additive.toMul
              ((rationalAbstractFixedFieldIdeleClassEquivFixed H.field
                (hfinite := H.finite)).symm
                a)))) =
      (ClassFormation.ValuationData.maximalUnramifiedNormResidueSymbol
        rationalCyclotomicIdeleClassValuationData H a).toMul := by
  apply
    (rationalCyclotomicDegreeData.maximalUnramifiedDegreeEquiv
      (H.toFiniteResidueAbstractField
        rationalCyclotomicDegreeData)).injective
  refine ((rationalCyclotomicDegreeData.maximalUnramifiedDegreeEquiv
    (H.toFiniteResidueAbstractField rationalCyclotomicDegreeData)).apply_symm_apply
      (abstractFixedFieldCyclotomicGalEquivZHat H
        (abstractFixedFieldCyclotomicIdeleClassArtinMonoidHom H
          (Additive.toMul
            ((rationalAbstractFixedFieldIdeleClassEquivFixed H.field
              (hfinite := H.finite)).symm a))))).trans ?_
  exact (congrArg (abstractFixedFieldCyclotomicGalEquivZHat H)
    (abstractFixedFieldCyclotomicIdeleClassArtin_eq_maximalUnramifiedNormResidue
      H a)).trans
        (abstractFixedFieldCyclotomicGalEquivZHat_quotientClass H
          (ClassFormation.ValuationData.maximalUnramifiedNormResidueSymbol
            rationalCyclotomicIdeleClassValuationData H a).toMul)

/-- On a fixed-part idele class, finite restriction of the genuine
cyclotomic Artin symbol is the finite restriction of the
maximal-unramified norm-residue symbol. -/
theorem
    abstractFixedFieldCyclotomicFiniteRestriction_ideleClassArtin_fixed
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension H.field)
    (hUnramified :
      L.toFiniteGaloisExtension.IsUnramified
        rationalCyclotomicDegreeData)
    (a :
      ambientFixedAddSubgroup
        rationalIdeleClassRepresentation H.field) :
    abstractFixedFieldCyclotomicFiniteRestrictionMonoidHom
        H L hUnramified
        (abstractFixedFieldCyclotomicIdeleClassArtinMonoidHom H
          (Additive.toMul
            ((rationalAbstractFixedFieldIdeleClassEquivFixed H.field
              (hfinite := H.finite)).symm
              a))) =
      (L.extensionQuotientMulEquiv.trans
        (LocalClassFieldTheory.abstractExtensionQuotientEquivGaloisGroup
          ℚ (SeparableClosure ℚ)
          H.field L.field L.below L.normal))
        (DegreeData.finiteUnramifiedRestriction
          rationalCyclotomicDegreeData
          (H.toFiniteResidueAbstractField
            rationalCyclotomicDegreeData)
          L.toFiniteGaloisExtension hUnramified
          (ClassFormation.ValuationData.maximalUnramifiedNormResidueSymbol
            rationalCyclotomicIdeleClassValuationData H a).toMul) := by
  let qFinite :=
    L.toFiniteGaloisExtension.extensionQuotientMulEquiv.trans
      (LocalClassFieldTheory.abstractExtensionQuotientEquivGaloisGroup
        ℚ (SeparableClosure ℚ)
        H.field L.field L.below L.normal)
  let finiteRestriction :=
    DegreeData.finiteUnramifiedRestriction
      rationalCyclotomicDegreeData
      (H.toFiniteResidueAbstractField rationalCyclotomicDegreeData)
      L.toFiniteGaloisExtension hUnramified
  let degreeEquiv :=
    rationalCyclotomicDegreeData.maximalUnramifiedDegreeEquiv
      (H.toFiniteResidueAbstractField rationalCyclotomicDegreeData)
  let galEquiv := abstractFixedFieldCyclotomicGalEquivZHat H
  let c :=
    abstractFixedFieldCyclotomicIdeleClassArtinMonoidHom H
      (Additive.toMul
        ((rationalAbstractFixedFieldIdeleClassEquivFixed H.field
          (hfinite := H.finite)).symm a))
  calc
    abstractFixedFieldCyclotomicFiniteRestrictionMonoidHom
        H L hUnramified c =
      qFinite (finiteRestriction (degreeEquiv.symm (galEquiv c))) := rfl
    _ = qFinite
        (finiteRestriction
          (ClassFormation.ValuationData.maximalUnramifiedNormResidueSymbol
            rationalCyclotomicIdeleClassValuationData H a).toMul) :=
      congrArg (fun q ↦ qFinite (finiteRestriction q))
        (abstractFixedFieldCyclotomicIdeleClassArtin_fixed_coordinate H a)

/-- The actual fixed-field global norm-residue value on a fixed-part
class is the finite restriction of the maximal-unramified cyclotomic
symbol. -/
theorem
    abstractFixedFieldGlobalNormResidueMonoidHom_fixed_eq_finiteUnramifiedRestriction
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension H.field)
    (hUnramified :
      L.toFiniteGaloisExtension.IsUnramified
        rationalCyclotomicDegreeData)
    (a :
      ambientFixedAddSubgroup
        rationalIdeleClassRepresentation H.field) :
    abstractFixedFieldGlobalNormResidueMonoidHom H L
        (Additive.toMul
          ((rationalAbstractFixedFieldIdeleClassEquivFixed H.field
            (hfinite := H.finite)).symm
            a)) =
      (L.extensionQuotientMulEquiv.trans
        (LocalClassFieldTheory.abstractExtensionQuotientEquivGaloisGroup
          ℚ (SeparableClosure ℚ)
          H.field L.field L.below L.normal))
        (DegreeData.finiteUnramifiedRestriction
          rationalCyclotomicDegreeData
          (H.toFiniteResidueAbstractField
            rationalCyclotomicDegreeData)
          L.toFiniteGaloisExtension hUnramified
          (ClassFormation.ValuationData.maximalUnramifiedNormResidueSymbol
            rationalCyclotomicIdeleClassValuationData H a).toMul) := by
  let : Finite
      (H.field.toSubgroup ⧸
        CyclicCohomology.extensionSubgroup H.field L.field L.below) :=
    L.finite
  let : IsMulCommutative L.extensionQuotient :=
    L.commutative
  let q : L.extensionQuotient :=
    DegreeData.finiteUnramifiedRestriction
      rationalCyclotomicDegreeData
      (H.toFiniteResidueAbstractField rationalCyclotomicDegreeData)
      L.toFiniteGaloisExtension hUnramified
      (ClassFormation.ValuationData.maximalUnramifiedNormResidueSymbol
        rationalCyclotomicIdeleClassValuationData H a).toMul
  rw [abstractFixedFieldGlobalNormResidueMonoidHom_fixed_apply]
  change
    Additive.toMul
      (abstractFixedFieldAbelianizedExtensionQuotientEquivGaloisGroup H L
        (rationalCyclotomicDegreeData.normResidueSymbol
          rationalIdeleClassRepresentation
          rationalCyclotomicIdeleClassValuationData
          rationalIdeleClassRepresentation_satisfiesClassFieldAxiom
          H L.toFiniteGaloisExtension
          (finiteNormClass rationalIdeleClassRepresentation
            H.field L.field L.below a))) =
      _
  calc
    _ =
        Additive.toMul
          (abstractFixedFieldAbelianizedExtensionQuotientEquivGaloisGroup H L
            (Additive.ofMul (Abelianization.of q))) :=
      congrArg
        (fun z =>
          Additive.toMul
            (abstractFixedFieldAbelianizedExtensionQuotientEquivGaloisGroup
              H L z))
        (ClassFormation.ValuationData.normResidueSymbol_finiteNormClass_eq_maximalUnramifiedRestriction
          rationalCyclotomicIdeleClassValuationData
          rationalIdeleClassRepresentation_satisfiesClassFieldAxiom
          H L.toFiniteGaloisExtension hUnramified a)
    _ = _ := by
      rw [abstractFixedFieldAbelianizedExtensionQuotientEquivGaloisGroup_of]
      exact toMul_ofMul _

/-- Finite restriction of the genuine cyclotomic chosen-local-factor
Artin map is exactly the actual global norm-residue map for every
finite unramified abelian fixed-field extension. -/
theorem
    abstractFixedFieldGlobalNormResidueMonoidHom_eq_cyclotomicFiniteRestriction
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension H.field)
    (hUnramified :
      L.toFiniteGaloisExtension.IsUnramified
        rationalCyclotomicDegreeData)
    (c :
      IdeleClassGroup
        (LocalClassFieldTheory.abstractFixedField
          ℚ (SeparableClosure ℚ) H.field)) :
    abstractFixedFieldGlobalNormResidueMonoidHom H L c =
      abstractFixedFieldCyclotomicFiniteRestrictionMonoidHom
        H L hUnramified
        (abstractFixedFieldCyclotomicIdeleClassArtinMonoidHom H c) := by
  let e :=
    rationalAbstractFixedFieldIdeleClassEquivFixed H.field
      (hfinite := H.finite)
  let a :
      ambientFixedAddSubgroup
        rationalIdeleClassRepresentation H.field :=
    e (Additive.ofMul c)
  have hc :
      Additive.toMul (e.symm a) = c := by
    apply Additive.ofMul.injective
    change e.symm (e (Additive.ofMul c)) = Additive.ofMul c
    exact e.symm_apply_apply _
  calc
    abstractFixedFieldGlobalNormResidueMonoidHom H L c =
        abstractFixedFieldGlobalNormResidueMonoidHom H L
          (Additive.toMul (e.symm a)) := by rw [hc]
    _ =
        (L.extensionQuotientMulEquiv.trans
          (LocalClassFieldTheory.abstractExtensionQuotientEquivGaloisGroup
            ℚ (SeparableClosure ℚ)
            H.field L.field L.below L.normal))
          (DegreeData.finiteUnramifiedRestriction
            rationalCyclotomicDegreeData
            (H.toFiniteResidueAbstractField
              rationalCyclotomicDegreeData)
            L.toFiniteGaloisExtension hUnramified
            (ClassFormation.ValuationData.maximalUnramifiedNormResidueSymbol
              rationalCyclotomicIdeleClassValuationData H a).toMul) :=
      abstractFixedFieldGlobalNormResidueMonoidHom_fixed_eq_finiteUnramifiedRestriction
        H L hUnramified a
    _ =
        abstractFixedFieldCyclotomicFiniteRestrictionMonoidHom
          H L hUnramified
          (abstractFixedFieldCyclotomicIdeleClassArtinMonoidHom H
            (Additive.toMul (e.symm a))) :=
      (abstractFixedFieldCyclotomicFiniteRestriction_ideleClassArtin_fixed
        H L hUnramified a).symm
    _ =
        abstractFixedFieldCyclotomicFiniteRestrictionMonoidHom
          H L hUnramified
          (abstractFixedFieldCyclotomicIdeleClassArtinMonoidHom H c) :=
      congrArg
        (fun z =>
          abstractFixedFieldCyclotomicFiniteRestrictionMonoidHom
            H L hUnramified
            (abstractFixedFieldCyclotomicIdeleClassArtinMonoidHom H z))
        hc

end Reciprocity
end GlobalClassFieldTheory
