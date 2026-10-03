/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteAbelianClassification
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.IdeleClassFormation
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClassFieldRealization
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.CyclotomicIdeleClassValuation
/-!
# The ordinary finite abelian class-field correspondence

The abstract finite abelian classification is formulated on the fixed
parts of the rational absolute idele-class representation.  For a finite
abstract base field, the canonical fixed-field comparison transports its
norm subgroups to the ordinary idele class group of the actual fixed
number field.

This file records that transported correspondence.  In particular, the
two lattice formulas are now equalities of ordinary determinant-norm
subgroups: composita correspond to intersections and intersection fields
correspond to products.
-/

@[expose] public section

open scoped NumberField

noncomputable
section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open ClassFormation
open KummerTheory
open LocalClassFieldTheory
open Reciprocity

/-- Fix the rational algebra structure used by every occurrence of the
absolute Galois group in this module. -/
noncomputable local instance
    finiteAbelianClassFieldCorrespondenceSeparableClosureAlgebra :
    Algebra ℚ (SeparableClosure ℚ) :=
  rationalSeparableClosureAlgebra

variable
    (K : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))

local instance ordinaryFixedFieldBaseQuotientFinite :
    Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        CyclicCohomology.extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          K.field (le_baseField K.field)) :=
  K.finite

noncomputable local instance ordinaryFixedFieldFiniteDimensional :
    FiniteDimensional ℚ
      (abstractFixedField ℚ (SeparableClosure ℚ) K.field) :=
  abstractFixedField_finiteDimensional
    ℚ (SeparableClosure ℚ) K.field K.finite

noncomputable local instance ordinaryFixedFieldNumberField :
    NumberField
      (abstractFixedField ℚ (SeparableClosure ℚ) K.field) :=
  NumberField.of_module_finite ℚ
    (abstractFixedField ℚ (SeparableClosure ℚ) K.field)

/-- The ordinary idele-class norm subgroup represented by a finite
abelian subextension of a rational absolute fixed field.

The definition transports the abstract norm subgroup through the
canonical equivalence from the ordinary idele class group of the actual
fixed field.  The theorem
`ordinaryIdeleClassNormSubgroup_eq_actualNormRange` below identifies it
with the genuine determinant-norm range of the represented extension. -/
noncomputable def ordinaryIdeleClassNormSubgroup
    (K : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension K.field) :
    AddSubgroup
      (Additive
        (IdeleClassGroup
          (abstractFixedField
            ℚ (SeparableClosure ℚ) K.field))) := by
  exact
    (L.normSubgroup rationalIdeleClassRepresentation).map
      (rationalAbstractFixedFieldIdeleClassEquivFixed
        K.field).symm.toAddMonoidHom

private theorem ordinaryIdeleClassNormSubgroup_eq_map
    (K : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension K.field) :
    ordinaryIdeleClassNormSubgroup K L =
      (L.normSubgroup rationalIdeleClassRepresentation).map
        (rationalAbstractFixedFieldIdeleClassEquivFixed
          K.field).symm.toAddMonoidHom :=
  rfl

/-- The transported subgroup is the genuine ordinary
determinant-norm range of the actual relative fixed-field extension. -/
theorem ordinaryIdeleClassNormSubgroup_eq_actualNormRange
    (K : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension K.field) :
    let F :=
      abstractFixedField ℚ (SeparableClosure ℚ) K.field
    let E :=
      abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) L.below
    letI hKfinite : Finite
        ((baseField
          (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
          CyclicCohomology.extensionSubgroup
            (baseField
              (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
            K.field (le_baseField K.field)) :=
      K.finite
    letI hLfinite : Finite
        (K.field.toSubgroup ⧸
          CyclicCohomology.extensionSubgroup K.field L.field L.below) :=
      L.finite
    letI : FiniteDimensional ℚ F :=
      abstractFixedField_finiteDimensional
        ℚ (SeparableClosure ℚ) K.field hKfinite
    letI : FiniteDimensional F E :=
      abstractRelativeFixedField_finiteDimensional
        ℚ (SeparableClosure ℚ)
        K.field L.field L.below hKfinite hLfinite
    letI : IsScalarTower ℚ F E :=
      IsScalarTower.of_algebraMap_eq' rfl
    letI : FiniteDimensional ℚ E :=
      FiniteDimensional.trans ℚ F E
    letI : NumberField F :=
      NumberField.of_module_finite ℚ F
    letI : NumberField E :=
      NumberField.of_module_finite ℚ E
    letI : IsAbelianGalois F E :=
      finiteAbelianSubextensionAbstractRelativeFixedFieldIsAbelianGalois L
    ordinaryIdeleClassNormSubgroup K L =
      (_root_.ideleClassNorm F E).range.toAddSubgroup := by
  exact
    (ordinaryIdeleClassNormSubgroup_eq_map K L).trans
      (map_rationalFiniteNormSubgroup_eq_ordinaryIdeleClassNormRange_concrete
        (hKfinite := K.finite) (hfinite := L.finite)
        K.field L.field L.below L.normal)

/-- Field inclusion is exactly reverse inclusion of the represented
ordinary determinant-norm subgroups. -/
theorem le_iff_ordinaryIdeleClassNormSubgroup_le
    (K : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L₁ L₂ : FiniteAbelianSubextension K.field) :
    L₁ ≤ L₂ ↔
      ordinaryIdeleClassNormSubgroup K L₂ ≤
        ordinaryIdeleClassNormSubgroup K L₁ := by
  let e :
      KummerTheory.ambientFixedAddSubgroup
          rationalIdeleClassRepresentation K.field ≃+
        Additive (IdeleClassGroup
          (abstractFixedField ℚ (SeparableClosure ℚ) K.field)) :=
    (rationalAbstractFixedFieldIdeleClassEquivFixed
      (hfinite := K.finite) K.field).symm
  let f :
      KummerTheory.ambientFixedAddSubgroup
          rationalIdeleClassRepresentation K.field →+
        Additive (IdeleClassGroup
          (abstractFixedField ℚ (SeparableClosure ℚ) K.field)) :=
    e.toAddMonoidHom
  have hf : Function.Injective f := e.injective
  let S₂ := L₂.normSubgroup rationalIdeleClassRepresentation
  let S₁ := L₁.normSubgroup rationalIdeleClassRepresentation
  have h₂ : ordinaryIdeleClassNormSubgroup K L₂ = S₂.map f :=
    ordinaryIdeleClassNormSubgroup_eq_map K L₂
  have h₁ : ordinaryIdeleClassNormSubgroup K L₁ = S₁.map f :=
    ordinaryIdeleClassNormSubgroup_eq_map K L₁
  have htransport :
      (S₂.map f ≤ S₁.map f) ↔
        (ordinaryIdeleClassNormSubgroup K L₂ ≤
          ordinaryIdeleClassNormSubgroup K L₁) :=
    Iff.of_eq (congrArg₂
      (fun A B : AddSubgroup (Additive (IdeleClassGroup
        (abstractFixedField ℚ (SeparableClosure ℚ) K.field))) => A ≤ B)
      h₂.symm h₁.symm)
  exact
    (FiniteAbelianSubextension.le_iff_normSubgroup_le
      rationalCyclotomicIdeleClassValuationData
      rationalIdeleClassRepresentation_satisfiesClassFieldAxiom
      K L₁ L₂).trans
        ((AddSubgroup.map_le_map_iff_of_injective hf).symm.trans htransport)

/-- A finite abelian subextension is uniquely determined by its
ordinary idele-class norm subgroup. -/
theorem ordinaryIdeleClassNormSubgroup_injective
    (K : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :
    Function.Injective
      (ordinaryIdeleClassNormSubgroup K) := by
  intro L₁ L₂ h
  apply le_antisymm
  · exact
      (le_iff_ordinaryIdeleClassNormSubgroup_le
        K L₁ L₂).2 h.ge
  · exact
      (le_iff_ordinaryIdeleClassNormSubgroup_le
        K L₂ L₁).2 h.le

/-- The ordinary norm subgroup of a compositum is the intersection of
the two ordinary norm subgroups. -/
theorem ordinaryIdeleClassNormSubgroup_compositum
    (K : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L₁ L₂ : FiniteAbelianSubextension K.field) :
    ordinaryIdeleClassNormSubgroup K (L₁.compositum L₂) =
      ordinaryIdeleClassNormSubgroup K L₁ ⊓
        ordinaryIdeleClassNormSubgroup K L₂ := by
  let e :
      Additive (IdeleClassGroup
        (abstractFixedField ℚ (SeparableClosure ℚ) K.field)) ≃+
        KummerTheory.ambientFixedAddSubgroup
          rationalIdeleClassRepresentation K.field :=
    rationalAbstractFixedFieldIdeleClassEquivFixed K.field
  let f :
      KummerTheory.ambientFixedAddSubgroup
          rationalIdeleClassRepresentation K.field →+
        Additive (IdeleClassGroup
          (abstractFixedField ℚ (SeparableClosure ℚ) K.field)) :=
    e.symm.toAddMonoidHom
  have hf : Function.Injective f := e.symm.injective
  calc
    ordinaryIdeleClassNormSubgroup K (L₁.compositum L₂) =
        ((L₁.compositum L₂).normSubgroup
          rationalIdeleClassRepresentation).map
            f :=
      ordinaryIdeleClassNormSubgroup_eq_map K (L₁.compositum L₂)
    _ = ((L₁.normSubgroup rationalIdeleClassRepresentation) ⊓
          (L₂.normSubgroup rationalIdeleClassRepresentation)).map
            f :=
      congrArg
        (fun H : AddSubgroup
            (KummerTheory.ambientFixedAddSubgroup
              rationalIdeleClassRepresentation K.field) =>
          AddSubgroup.map
            (N := Additive (IdeleClassGroup
              (abstractFixedField ℚ (SeparableClosure ℚ) K.field))) f H)
        (FiniteAbelianSubextension.normSubgroup_compositum
          rationalCyclotomicIdeleClassValuationData
          rationalIdeleClassRepresentation_satisfiesClassFieldAxiom
          K L₁ L₂)
    _ = (L₁.normSubgroup rationalIdeleClassRepresentation).map
          f ⊓
        (L₂.normSubgroup rationalIdeleClassRepresentation).map
          f :=
      AddSubgroup.map_inf
        (G := KummerTheory.ambientFixedAddSubgroup
          rationalIdeleClassRepresentation K.field)
        (N := Additive (IdeleClassGroup
          (abstractFixedField ℚ (SeparableClosure ℚ) K.field)))
        (H := L₁.normSubgroup rationalIdeleClassRepresentation)
        (K := L₂.normSubgroup rationalIdeleClassRepresentation)
        (f := f) (hf := hf)
    _ = ordinaryIdeleClassNormSubgroup K L₁ ⊓
        ordinaryIdeleClassNormSubgroup K L₂ :=
      congrArg₂ (fun A B => A ⊓ B)
        (ordinaryIdeleClassNormSubgroup_eq_map K L₁).symm
        (ordinaryIdeleClassNormSubgroup_eq_map K L₂).symm

/-- The ordinary norm subgroup of an intersection field is the product
of the two ordinary norm subgroups. -/
theorem ordinaryIdeleClassNormSubgroup_intersection
    (K : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L₁ L₂ : FiniteAbelianSubextension K.field) :
    ordinaryIdeleClassNormSubgroup K (L₁.intersection L₂) =
      ordinaryIdeleClassNormSubgroup K L₁ ⊔
        ordinaryIdeleClassNormSubgroup K L₂ := by
  let e :
      Additive (IdeleClassGroup
        (abstractFixedField ℚ (SeparableClosure ℚ) K.field)) ≃+
        KummerTheory.ambientFixedAddSubgroup
          rationalIdeleClassRepresentation K.field :=
    rationalAbstractFixedFieldIdeleClassEquivFixed K.field
  let f :
      KummerTheory.ambientFixedAddSubgroup
          rationalIdeleClassRepresentation K.field →+
        Additive (IdeleClassGroup
          (abstractFixedField ℚ (SeparableClosure ℚ) K.field)) :=
    e.symm.toAddMonoidHom
  calc
    ordinaryIdeleClassNormSubgroup K (L₁.intersection L₂) =
        ((L₁.intersection L₂).normSubgroup
          rationalIdeleClassRepresentation).map
            f :=
      ordinaryIdeleClassNormSubgroup_eq_map K (L₁.intersection L₂)
    _ = ((L₁.normSubgroup rationalIdeleClassRepresentation) ⊔
          (L₂.normSubgroup rationalIdeleClassRepresentation)).map
            f :=
      congrArg
        (fun H : AddSubgroup
            (KummerTheory.ambientFixedAddSubgroup
              rationalIdeleClassRepresentation K.field) =>
          AddSubgroup.map
            (N := Additive (IdeleClassGroup
              (abstractFixedField ℚ (SeparableClosure ℚ) K.field))) f H)
        (FiniteAbelianSubextension.normSubgroup_intersection
          rationalCyclotomicIdeleClassValuationData
          rationalIdeleClassRepresentation_satisfiesClassFieldAxiom
          K L₁ L₂)
    _ = (L₁.normSubgroup rationalIdeleClassRepresentation).map
          f ⊔
        (L₂.normSubgroup rationalIdeleClassRepresentation).map
          f :=
      AddSubgroup.map_sup
        (G := KummerTheory.ambientFixedAddSubgroup
          rationalIdeleClassRepresentation K.field)
        (N := Additive (IdeleClassGroup
          (abstractFixedField ℚ (SeparableClosure ℚ) K.field)))
        (H := L₁.normSubgroup rationalIdeleClassRepresentation)
        (K := L₂.normSubgroup rationalIdeleClassRepresentation)
        (f := f)
    _ = ordinaryIdeleClassNormSubgroup K L₁ ⊔
        ordinaryIdeleClassNormSubgroup K L₂ :=
      congrArg₂ (fun A B => A ⊔ B)
        (ordinaryIdeleClassNormSubgroup_eq_map K L₁).symm
        (ordinaryIdeleClassNormSubgroup_eq_map K L₂).symm

end GlobalClassFields
end GlobalClassFieldTheory
