/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.NormTopology
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.IdeleClassDirectLimitNormQuotient
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.NormConductor
/-!
# The norm topology and the ordinary idele-class topology

On every actual fixed field inside the rational separable closure, the
canonical fixed-part model identifies each abstract finite norm subgroup
with the range of the corresponding ordinary idele-class norm.  Since the
latter is open, every abstract norm-open subgroup becomes open in the
ordinary idele-class topology after transport to the actual fixed field.
-/

open scoped NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open ClassFormation
open LocalClassFieldTheory

/-- Use the canonical quotient group structure before elaborating additive
norm-subgroup maps. -/
@[instance_reducible]
private noncomputable def normTopologyIdeleClassCommGroup
    (F : Type) [Field F] [NumberField F] :
    CommGroup (IdeleClassGroup F) :=
  QuotientGroup.Quotient.commGroup (IdeleGroup.principalSubgroup F)

attribute [local instance] normTopologyIdeleClassCommGroup

/-- The transport of an abstract fixed-part subgroup to the ordinary
idele-class group of the corresponding rational fixed field. -/
noncomputable def rationalTransportedNormSubgroup
    (K : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    [hKfinite : Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        CyclicCohomology.extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          K (le_baseField K))]
    (H : AddSubgroup
      (KummerTheory.ambientFixedAddSubgroup
        rationalIdeleClassRepresentation K)) :
    let F := abstractFixedField ℚ (SeparableClosure ℚ) K
    letI : FiniteDimensional ℚ F :=
      abstractFixedField_finiteDimensional
        ℚ (SeparableClosure ℚ) K hKfinite
    letI : NumberField F := NumberField.of_module_finite ℚ F
    AddSubgroup (Additive (IdeleClassGroup F)) := by
  let F := abstractFixedField ℚ (SeparableClosure ℚ) K
  letI : FiniteDimensional ℚ F :=
    abstractFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) K hKfinite
  letI : NumberField F := NumberField.of_module_finite ℚ F
  exact
    H.map
      (rationalAbstractFixedFieldIdeleClassEquivFixed
        K).symm.toAddMonoidHom

private theorem rationalNormOpenSubgroup_exists_finiteNormSubgroup
    (K : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (H : AddSubgroup
      (KummerTheory.ambientFixedAddSubgroup
        rationalIdeleClassRepresentation K))
    (hH : IsNormOpen rationalIdeleClassRepresentation K
      (H : Set
        (KummerTheory.ambientFixedAddSubgroup
          rationalIdeleClassRepresentation K))) :
    ∃ L : FiniteGaloisSubextension K,
      FiniteGaloisSubextension.normSubgroup
        rationalIdeleClassRepresentation L ≤ H := by
  exact
    (normTopology_addSubgroup_isOpen_iff
      rationalIdeleClassRepresentation K H).1 hH

private theorem isOpen_addSubgroup_of_eq
    {A : Type*} [AddGroup A] [TopologicalSpace A]
    (H H' : AddSubgroup A) (h : H = H')
    (hopen : IsOpen (H' : Set A)) :
    IsOpen (H : Set A) := by
  exact h.symm ▸ hopen

private theorem
    rationalFiniteNormSubgroup_map_eq_ordinaryIdeleClassNormRange
    (K : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    [hKfinite : Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        CyclicCohomology.extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          K (le_baseField K))]
    (L : FiniteGaloisSubextension K) :
    letI : Finite
        (K.toSubgroup ⧸
          CyclicCohomology.extensionSubgroup K L.field L.below) :=
      L.finite
    let F := abstractFixedField ℚ (SeparableClosure ℚ) K
    let E :=
      abstractRelativeFixedField ℚ (SeparableClosure ℚ) L.below
    letI :
        (CyclicCohomology.extensionSubgroup
          K L.field L.below).Normal :=
      L.normal
    letI : FiniteDimensional ℚ F :=
      abstractFixedField_finiteDimensional
        ℚ (SeparableClosure ℚ) K hKfinite
    letI : FiniteDimensional F E :=
      abstractRelativeFixedField_finiteDimensional
        ℚ (SeparableClosure ℚ) K L.field L.below hKfinite L.finite
    letI : IsScalarTower ℚ F E :=
      IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
    letI : FiniteDimensional ℚ E :=
      FiniteDimensional.trans ℚ F E
    letI : NumberField F := NumberField.of_module_finite ℚ F
    letI : NumberField E := NumberField.of_module_finite ℚ E
    letI : IsGalois F E :=
      abstractRelativeFixedField_isGalois
        ℚ (SeparableClosure ℚ) K L.field L.below L.normal
    (finiteNormSubgroup rationalIdeleClassRepresentation
        K L.field L.below).map
        (rationalAbstractFixedFieldIdeleClassEquivFixed
          K).symm.toAddMonoidHom =
      (_root_.ideleClassNorm F E).range.toAddSubgroup := by
  exact
    map_rationalFiniteNormSubgroup_eq_ordinaryIdeleClassNormRange_concrete
      (hKfinite := hKfinite) (hfinite := L.finite)
      K L.field L.below L.normal

private theorem rationalOrdinaryIdeleClassNormRange_isOpen
    (K : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    [hKfinite : Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        CyclicCohomology.extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          K (le_baseField K))]
    (L : FiniteGaloisSubextension K) :
    letI : Finite
        (K.toSubgroup ⧸
          CyclicCohomology.extensionSubgroup K L.field L.below) :=
      L.finite
    let F := abstractFixedField ℚ (SeparableClosure ℚ) K
    let E :=
      abstractRelativeFixedField ℚ (SeparableClosure ℚ) L.below
    letI :
        (CyclicCohomology.extensionSubgroup
          K L.field L.below).Normal :=
      L.normal
    letI : FiniteDimensional ℚ F :=
      abstractFixedField_finiteDimensional
        ℚ (SeparableClosure ℚ) K hKfinite
    letI : FiniteDimensional F E :=
      abstractRelativeFixedField_finiteDimensional
        ℚ (SeparableClosure ℚ) K L.field L.below hKfinite L.finite
    letI : IsScalarTower ℚ F E :=
      IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
    letI : FiniteDimensional ℚ E :=
      FiniteDimensional.trans ℚ F E
    letI : NumberField F := NumberField.of_module_finite ℚ F
    letI : NumberField E := NumberField.of_module_finite ℚ E
    letI : IsGalois F E :=
      abstractRelativeFixedField_isGalois
        ℚ (SeparableClosure ℚ) K L.field L.below L.normal
    IsOpen
      (((_root_.ideleClassNorm F E).range.toAddSubgroup :
        AddSubgroup (Additive (IdeleClassGroup F))) :
        Set (Additive (IdeleClassGroup F))) := by
  intro F E
  let : NumberField F := by
    let : FiniteDimensional ℚ F :=
      abstractFixedField_finiteDimensional
        ℚ (SeparableClosure ℚ) K hKfinite
    exact NumberField.of_module_finite ℚ F
  let : NumberField E := by
    let : FiniteDimensional F E :=
      abstractRelativeFixedField_finiteDimensional
        ℚ (SeparableClosure ℚ) K L.field L.below hKfinite L.finite
    exact NumberField.of_module_finite F E
  let : IsGalois F E :=
    abstractRelativeFixedField_isGalois
      ℚ (SeparableClosure ℚ) K L.field L.below L.normal
  exact
    GlobalClassFields.ideleClassNorm_range_isOpen
      (K := F) (L := E)

/-- Transporting a norm-open subgroup of the rational absolute
idele-class representation to the idele class group of its actual fixed
field produces an open subgroup for the ordinary idele-class topology. -/
theorem rationalNormOpenSubgroup_isOpen
    (K : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    [hKfinite : Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        CyclicCohomology.extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          K (le_baseField K))]
    (H : AddSubgroup
      (KummerTheory.ambientFixedAddSubgroup
        rationalIdeleClassRepresentation K))
    (hH : IsNormOpen rationalIdeleClassRepresentation K
      (H : Set
        (KummerTheory.ambientFixedAddSubgroup
          rationalIdeleClassRepresentation K))) :
    let F := abstractFixedField ℚ (SeparableClosure ℚ) K
    letI : FiniteDimensional ℚ F :=
      abstractFixedField_finiteDimensional
        ℚ (SeparableClosure ℚ) K hKfinite
    letI : NumberField F := NumberField.of_module_finite ℚ F
    IsOpen
      ((rationalTransportedNormSubgroup
          (hKfinite := hKfinite) K H :
        AddSubgroup (Additive (IdeleClassGroup F))) :
        Set (Additive (IdeleClassGroup F))) := by
  intro F
  let : NumberField F := by
    let : FiniteDimensional ℚ F :=
      abstractFixedField_finiteDimensional
        ℚ (SeparableClosure ℚ) K hKfinite
    exact NumberField.of_module_finite ℚ F
  let eK :
      Additive (IdeleClassGroup F) ≃+
        KummerTheory.ambientFixedAddSubgroup
          rationalIdeleClassRepresentation K :=
    rationalAbstractFixedFieldIdeleClassEquivFixed K
  rcases
      rationalNormOpenSubgroup_exists_finiteNormSubgroup K H hH with
    ⟨L, hLH⟩
  let : Finite
      (K.toSubgroup ⧸
        CyclicCohomology.extensionSubgroup K L.field L.below) :=
    L.finite
  let :
      (CyclicCohomology.extensionSubgroup
        K L.field L.below).Normal :=
    L.normal
  change
    IsOpen
      ((H.map eK.symm.toAddMonoidHom :
        AddSubgroup (Additive (IdeleClassGroup F))) :
        Set (Additive (IdeleClassGroup F)))
  apply AddSubgroup.isOpen_mono (AddSubgroup.map_mono hLH)
  have hnormMap :=
    rationalFiniteNormSubgroup_map_eq_ordinaryIdeleClassNormRange
      (hKfinite := hKfinite) K L
  have hopen :=
    rationalOrdinaryIdeleClassNormRange_isOpen
      (hKfinite := hKfinite) K L
  change
    IsOpen
      (((finiteNormSubgroup rationalIdeleClassRepresentation
          K L.field L.below).map
          eK.symm.toAddMonoidHom :
        AddSubgroup (Additive (IdeleClassGroup F))) :
        Set (Additive (IdeleClassGroup F)))
  exact
    isOpen_addSubgroup_of_eq _ _ hnormMap hopen

end Reciprocity
end GlobalClassFieldTheory
