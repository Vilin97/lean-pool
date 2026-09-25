/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.RationalAbstractExtensionToOrdinary
/-!
# Rational fixed-field base-change transport

Compatibility of abstract fixed-field inclusion with ordinary idele-class extension after
base change.
-/

@[expose] public section

noncomputable section

namespace GlobalClassFieldTheory
namespace IdealClassFieldTheory

open ClassFormation
open CyclicCohomology

section RationalIdeleExtension

open Reciprocity
open LocalClassFieldTheory

/-- Under the rational fixed-field realization, abstract fixed-field
inclusion is the actual extension map on ordinary idele classes. -/
theorem rationalFixedFieldInclusion_baseChange_eq_ideleClassExtension
    (K L : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    [hKfinite : Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          K (le_baseField K))]
    [hfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    (c : RelativeIdeleGroup.ClassGroup ℚ
      (abstractFixedField ℚ (SeparableClosure ℚ) K)) :
    let F := abstractFixedField ℚ (SeparableClosure ℚ) K
    let E := abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK
    letI := hnormal
    letI : FiniteDimensional ℚ F :=
      abstractFixedField_finiteDimensional
        ℚ (SeparableClosure ℚ) K hKfinite
    letI : FiniteDimensional F E :=
      abstractRelativeFixedField_finiteDimensional
        ℚ (SeparableClosure ℚ) K L hLK hKfinite hfinite
    letI : IsScalarTower ℚ F E :=
      IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
    letI : FiniteDimensional ℚ E :=
      FiniteDimensional.trans ℚ F E
    letI : NumberField F :=
      NumberField.of_module_finite ℚ F
    letI : NumberField E :=
      NumberField.of_module_finite ℚ E
    (MulEquiv.toAdditive
      (_root_.relativeIdeleClassBaseChangeMulEquiv
        (K := F) (L := E)))
        (rationalAbstractExtensionIdeleClassEquiv
          K L hLK hnormal
          ((extensionFixedRepresentationEquiv
            rationalIdeleClassRepresentation
              K L hLK hnormal).symm
            (fixedFieldInclusion
              rationalIdeleClassRepresentation K L hLK
              (rationalAbstractFixedFieldIdeleClassEquivFixed K
                (Additive.ofMul
                  (_root_.relativeIdeleClassBaseChangeMulEquiv
                    (K := ℚ) (L := F) c)))))) =
      Additive.ofMul
        (ideleClassExtension F E
          (_root_.relativeIdeleClassBaseChangeMulEquiv
            (K := ℚ) (L := F) c)) := by
  dsimp only
  let F := abstractFixedField ℚ (SeparableClosure ℚ) K
  let E := abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK
  let := hnormal
  let : FiniteDimensional ℚ F :=
    abstractFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) K hKfinite
  let : FiniteDimensional F E :=
    abstractRelativeFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) K L hLK hKfinite hfinite
  let : IsScalarTower ℚ F E :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  let : FiniteDimensional ℚ E :=
    FiniteDimensional.trans ℚ F E
  let : NumberField F :=
    NumberField.of_module_finite ℚ F
  let : NumberField E :=
    NumberField.of_module_finite ℚ E
  let q : IdeleClassGroup F :=
    _root_.relativeIdeleClassBaseChangeMulEquiv
      (K := ℚ) (L := F) c
  have hInclusion :=
    rationalAbstractExtensionIdeleClassEquiv_fixedFieldInclusion
      K L hLK hnormal c
  change
    rationalAbstractExtensionIdeleClassEquiv
        K L hLK hnormal
        ((extensionFixedRepresentationEquiv
          rationalIdeleClassRepresentation
            K L hLK hnormal).symm
          (fixedFieldInclusion
            rationalIdeleClassRepresentation K L hLK
            (rationalAbstractFixedFieldIdeleClassEquivFixed K
              (Additive.ofMul q)))) =
      Additive.ofMul
        (RelativeIdeleGroup.classInclusion F E q)
    at hInclusion
  have hBaseChange :=
    congrArg
      (MulEquiv.toAdditive
        (_root_.relativeIdeleClassBaseChangeMulEquiv
          (K := F) (L := E))) hInclusion
  change
    (MulEquiv.toAdditive
      (_root_.relativeIdeleClassBaseChangeMulEquiv
        (K := F) (L := E)))
        (rationalAbstractExtensionIdeleClassEquiv
          K L hLK hnormal
          ((extensionFixedRepresentationEquiv
            rationalIdeleClassRepresentation
              K L hLK hnormal).symm
            (fixedFieldInclusion
              rationalIdeleClassRepresentation K L hLK
              (rationalAbstractFixedFieldIdeleClassEquivFixed K
                (Additive.ofMul q))))) =
      Additive.ofMul
        (_root_.relativeIdeleClassBaseChangeMulEquiv
          (K := F) (L := E)
          (RelativeIdeleGroup.classInclusion F E q))
    at hBaseChange
  have hClassInclusion :
      Additive.ofMul
          (_root_.relativeIdeleClassBaseChangeMulEquiv
            (K := F) (L := E)
            (RelativeIdeleGroup.classInclusion F E q)) =
        Additive.ofMul (ideleClassExtension F E q) :=
    congrArg Additive.ofMul
      (_root_.relativeIdeleClassBaseChangeMulEquiv_classInclusion
        (K := F) (L := E) q)
  change
    (MulEquiv.toAdditive
      (_root_.relativeIdeleClassBaseChangeMulEquiv
        (K := F) (L := E)))
        (rationalAbstractExtensionIdeleClassEquiv
          K L hLK hnormal
          ((extensionFixedRepresentationEquiv
            rationalIdeleClassRepresentation
              K L hLK hnormal).symm
            (fixedFieldInclusion
              rationalIdeleClassRepresentation K L hLK
              (rationalAbstractFixedFieldIdeleClassEquivFixed K
                (Additive.ofMul q))))) =
      Additive.ofMul (ideleClassExtension F E q)
  exact hBaseChange.trans hClassInclusion

end RationalIdeleExtension

end IdealClassFieldTheory
end GlobalClassFieldTheory
