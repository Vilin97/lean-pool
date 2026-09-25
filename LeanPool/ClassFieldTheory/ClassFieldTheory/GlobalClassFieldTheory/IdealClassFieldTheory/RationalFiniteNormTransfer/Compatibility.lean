/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.RationalFiniteNormTransfer.Representatives
/-!
# Compatibility of rational finite-norm representatives

This compiled leaf preserves the original public declarations while reusing
the shared fixed-field instance providers.
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

local instance
    compatibilityIdeleClassGroupIsMulCommutative
    {F : Type} [Field F] [NumberField F] :
    IsMulCommutative (IdeleClassGroup F) :=
  RationalFiniteNormTransferInternal.ideleClassGroupIsMulCommutative

local instance
    compatibilityIdeleClassSubgroupNormal
    {F : Type} [Field F] [NumberField F]
    (N : Subgroup (IdeleClassGroup F)) : N.Normal :=
  RationalFiniteNormTransferInternal.ideleClassSubgroupNormal N

/-- Named base-change comparison for the canonical ordinary input. -/
noncomputable def
    rationalFiniteNormTransferCanonicalBaseChangeCompatibility
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
    (c : rationalFiniteNormTransferBaseIdeleClass
      (hKfinite := hKfinite) K) : Prop :=
  rationalFiniteNormTransferCanonicalAbstractExtensionEndpoint
      K L hLK hnormal c =
    Additive.ofMul
      (rationalFiniteNormTransferOrdinaryExtensionRepresentative
        K L hLK hnormal c)

/-- Named relative-to-ordinary comparison for the same canonical input. -/
noncomputable def
    rationalFiniteNormTransferCanonicalToOrdinaryCompatibility
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
    (c : rationalFiniteNormTransferBaseIdeleClass
      (hKfinite := hKfinite) K) : Prop :=
  rationalFiniteNormTransferCanonicalAbstractExtensionEndpoint
      K L hLK hnormal c =
    Additive.ofMul
      (rationalFiniteNormTransferCanonicalFixedRepresentative
        K L hLK c)

/-- The canonical abstract endpoint is ordinary idele-class extension. -/
theorem rationalFiniteNormTransferCanonicalBaseChangeCompatibility_proof
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
    (c : rationalFiniteNormTransferBaseIdeleClass
      (hKfinite := hKfinite) K) :
    rationalFiniteNormTransferCanonicalBaseChangeCompatibility
      K L hLK hnormal c := by
  let F := abstractFixedField ℚ (SeparableClosure ℚ) K
  obtain ⟨relativeClass, rfl⟩ :=
    (_root_.relativeIdeleClassBaseChangeMulEquiv
      (K := ℚ) (L := F)).surjective c
  change
    rationalFiniteNormTransferCanonicalAbstractExtensionEndpoint
        K L hLK hnormal
          (_root_.relativeIdeleClassBaseChangeMulEquiv
            (K := ℚ) (L := F) relativeClass) =
      Additive.ofMul
        (rationalFiniteNormTransferOrdinaryExtensionRepresentative
          K L hLK hnormal
            (_root_.relativeIdeleClassBaseChangeMulEquiv
              (K := ℚ) (L := F) relativeClass))
  simpa only [rationalFiniteNormTransferCanonicalAbstractExtensionEndpoint,
      rationalFiniteNormTransferOrdinaryExtensionRepresentative] using
    (rationalFixedFieldInclusion_baseChange_eq_ideleClassExtension
      K L hLK hnormal relativeClass)

/-- The same abstract endpoint is represented by the canonical fixed-field
idele class. -/
theorem rationalFiniteNormTransferCanonicalToOrdinaryCompatibility_proof
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
    (c : rationalFiniteNormTransferBaseIdeleClass
      (hKfinite := hKfinite) K) :
    rationalFiniteNormTransferCanonicalToOrdinaryCompatibility
      K L hLK hnormal c := by
  let F := abstractFixedField ℚ (SeparableClosure ℚ) K
  let E := abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK
  let : FiniteDimensional ℚ F :=
    RationalFiniteNormTransferInternal.fixedFiniteDimensional K
  let : FiniteDimensional F E :=
    RationalFiniteNormTransferInternal.relativeFiniteDimensional
      K L hLK
  let : IsScalarTower ℚ F E :=
    RationalFiniteNormTransferInternal.relativeScalarTower
      K L hLK
  let : FiniteDimensional ℚ E :=
    RationalFiniteNormTransferInternal.relativeAbsoluteFiniteDimensional
      K L hLK
  let : FiniteDimensional ℚ (E.restrictScalars ℚ) := by
    change FiniteDimensional ℚ
      (abstractFixedField ℚ (SeparableClosure ℚ) L)
    change FiniteDimensional ℚ E
    infer_instance
  let : NumberField F :=
    RationalFiniteNormTransferInternal.fixedNumberField K
  let : NumberField E :=
    RationalFiniteNormTransferInternal.relativeNumberField
      K L hLK
  let : IsGalois F E :=
    RationalFiniteNormTransferInternal.relativeIsGalois
      K L hLK hnormal
  let eL :=
    rationalAbstractRelativeFixedFieldIdeleClassEquivFixedOfFiniteDimensional
      K L hLK
  let eAmbient :=
    extensionFixedRepresentationEquiv
      rationalIdeleClassRepresentation K L hLK hnormal
  let x :
      (extensionFixedRepresentation
        rationalIdeleClassRepresentation K L hLK hnormal).V :=
    eAmbient.symm
      (fixedFieldInclusion rationalIdeleClassRepresentation K L hLK
        (rationalAbstractFixedFieldIdeleClassEquivFixed K
          (Additive.ofMul c)))
  have hOrdinary :=
    rationalAbstractExtensionIdeleClassEquiv_to_ordinary
      K L hLK hnormal x
  have hx :
      eAmbient x =
        fixedFieldInclusion rationalIdeleClassRepresentation K L hLK
          (rationalAbstractFixedFieldIdeleClassEquivFixed K
            (Additive.ofMul c)) :=
    eAmbient.apply_symm_apply
      (fixedFieldInclusion rationalIdeleClassRepresentation K L hLK
        (rationalAbstractFixedFieldIdeleClassEquivFixed K
          (Additive.ofMul c)))
  change
    rationalFiniteNormTransferCanonicalAbstractExtensionEndpoint
        K L hLK hnormal c =
      Additive.ofMul
        (rationalFiniteNormTransferCanonicalFixedRepresentative
          K L hLK c)
  simpa only [rationalFiniteNormTransferCanonicalAbstractExtensionEndpoint,
      rationalFiniteNormTransferCanonicalFixedRepresentative,
      ofMul_toMul, eL, eAmbient, x] using
    hOrdinary.trans (congrArg (fun z => eL.symm z) hx)

/-- The named compatibility proposition between the canonical fixed-field
representative and ordinary idele-class extension. -/
noncomputable def
    rationalFiniteNormTransferCanonicalFixedRepresentativeExtensionCompatibility
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
    (c : rationalFiniteNormTransferBaseIdeleClass
      (hKfinite := hKfinite) K) : Prop :=
    rationalFiniteNormTransferCanonicalFixedRepresentative K L hLK c =
      rationalFiniteNormTransferOrdinaryExtensionRepresentative
        K L hLK hnormal c

/-- Fixed-field inclusion gives exactly the ordinary idele-class extension of
the canonical base representative. -/
theorem rationalFiniteNormTransferCanonicalFixedRepresentative_eq_extension
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
    (c : rationalFiniteNormTransferBaseIdeleClass
      (hKfinite := hKfinite) K) :
    rationalFiniteNormTransferCanonicalFixedRepresentativeExtensionCompatibility
      K L hLK hnormal c := by
  change
    rationalFiniteNormTransferCanonicalFixedRepresentative K L hLK c =
      rationalFiniteNormTransferOrdinaryExtensionRepresentative
        K L hLK hnormal c
  have hBaseChange :=
    rationalFiniteNormTransferCanonicalBaseChangeCompatibility_proof
      K L hLK hnormal c
  have hToOrdinary :=
    rationalFiniteNormTransferCanonicalToOrdinaryCompatibility_proof
      K L hLK hnormal c
  change
    rationalFiniteNormTransferCanonicalAbstractExtensionEndpoint
        K L hLK hnormal c =
      Additive.ofMul
        (rationalFiniteNormTransferOrdinaryExtensionRepresentative
          K L hLK hnormal c) at hBaseChange
  change
    rationalFiniteNormTransferCanonicalAbstractExtensionEndpoint
        K L hLK hnormal c =
      Additive.ofMul
        (rationalFiniteNormTransferCanonicalFixedRepresentative
          K L hLK c) at hToOrdinary
  simpa only [toMul_ofMul] using
    congrArg Additive.toMul (hToOrdinary.symm.trans hBaseChange)


end RationalIdeleExtension

end IdealClassFieldTheory
end GlobalClassFieldTheory
