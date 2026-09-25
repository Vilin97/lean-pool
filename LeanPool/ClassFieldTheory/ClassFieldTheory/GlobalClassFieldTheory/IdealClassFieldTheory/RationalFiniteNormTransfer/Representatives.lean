/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.RationalFiniteNormTransfer.FieldSpine
/-!
# Representatives and comparison endpoints for rational finite-norm transport

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
    representativesIdeleClassGroupIsMulCommutative
    {F : Type} [Field F] [NumberField F] :
    IsMulCommutative (IdeleClassGroup F) :=
  RationalFiniteNormTransferInternal.ideleClassGroupIsMulCommutative

local instance
    representativesIdeleClassSubgroupNormal
    {F : Type} [Field F] [NumberField F]
    (N : Subgroup (IdeleClassGroup F)) : N.Normal :=
  RationalFiniteNormTransferInternal.ideleClassSubgroupNormal N

/-- The ordinary idele-class representative obtained from abstract fixed-field
inclusion. -/
noncomputable def rationalFiniteNormTransferAbstractRepresentative
    (K L : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hKfinite : Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          K (le_baseField K))]
    [hfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    (a : KummerTheory.ambientFixedAddSubgroup
      rationalIdeleClassRepresentation K) := by
  letI hLfinite := RationalFiniteNormTransferInternal.absoluteFinite
    K L hLK (hKfinite := hKfinite) (hfinite := hfinite)
  let E := abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK
  letI : Algebra ℚ E :=
    RationalFiniteNormTransferInternal.absoluteAlgebra K L hLK
  letI : FiniteDimensional ℚ E :=
    RationalFiniteNormTransferInternal.fixedFiniteDimensional L
  letI : NumberField E :=
    RationalFiniteNormTransferInternal.relativeNumberField
      K L hLK
  exact Additive.toMul
    ((rationalAbstractFixedFieldIdeleClassEquivFixed L).symm
      (fixedFieldInclusion rationalIdeleClassRepresentation
        K L hLK a))


/-- The canonical fixed-field representative attached to an ordinary base
idele class. -/
noncomputable def rationalFiniteNormTransferCanonicalFixedRepresentative
    (K L : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
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
    rationalFiniteNormTransferExtensionIdeleClass K L hLK := by
  let F := abstractFixedField ℚ (SeparableClosure ℚ) K
  let E := abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK
  letI : FiniteDimensional ℚ F :=
    RationalFiniteNormTransferInternal.fixedFiniteDimensional K
  letI : FiniteDimensional F E :=
    RationalFiniteNormTransferInternal.relativeFiniteDimensional
      K L hLK
  letI : IsScalarTower ℚ F E :=
    RationalFiniteNormTransferInternal.relativeScalarTower
      K L hLK
  letI : FiniteDimensional ℚ E :=
    RationalFiniteNormTransferInternal.relativeAbsoluteFiniteDimensional
      K L hLK
  letI : FiniteDimensional ℚ (E.restrictScalars ℚ) := by
    change FiniteDimensional ℚ
      (abstractFixedField ℚ (SeparableClosure ℚ) L)
    change FiniteDimensional ℚ E
    infer_instance
  letI : NumberField F :=
    RationalFiniteNormTransferInternal.fixedNumberField K
  letI : NumberField E :=
    RationalFiniteNormTransferInternal.relativeNumberField
      K L hLK
  exact Additive.toMul
    ((rationalAbstractRelativeFixedFieldIdeleClassEquivFixedOfFiniteDimensional
      K L hLK).symm
      (fixedFieldInclusion rationalIdeleClassRepresentation K L hLK
        (rationalAbstractFixedFieldIdeleClassEquivFixed K
          (Additive.ofMul c))))

/-- The ordinary extension representative attached to the same base idele
class. -/
noncomputable def rationalFiniteNormTransferOrdinaryExtensionRepresentative
    (K L : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (_hnormal : (extensionSubgroup K L hLK).Normal)
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
    rationalFiniteNormTransferExtensionIdeleClass K L hLK := by
  let F := abstractFixedField ℚ (SeparableClosure ℚ) K
  let E := abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK
  letI : FiniteDimensional ℚ F :=
    RationalFiniteNormTransferInternal.fixedFiniteDimensional K
  letI : FiniteDimensional F E :=
    RationalFiniteNormTransferInternal.relativeFiniteDimensional
      K L hLK
  letI : IsScalarTower ℚ F E :=
    RationalFiniteNormTransferInternal.relativeScalarTower
      K L hLK
  letI : FiniteDimensional ℚ E :=
    RationalFiniteNormTransferInternal.relativeAbsoluteFiniteDimensional
      K L hLK
  letI : NumberField F :=
    RationalFiniteNormTransferInternal.fixedNumberField K
  letI : NumberField E :=
    RationalFiniteNormTransferInternal.relativeNumberField
      K L hLK
  letI : IsGalois F E :=
    RationalFiniteNormTransferInternal.relativeIsGalois
      K L hLK _hnormal
  exact ideleClassExtension F E c

/-- The common additive endpoint appearing in the base-change and
relative-to-ordinary comparisons. -/
noncomputable def rationalFiniteNormTransferCanonicalAbstractExtensionEndpoint
    (K L : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (_hnormal : (extensionSubgroup K L hLK).Normal)
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
    Additive (rationalFiniteNormTransferExtensionIdeleClass K L hLK) := by
  let F := abstractFixedField ℚ (SeparableClosure ℚ) K
  let E := abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK
  letI : FiniteDimensional ℚ F :=
    RationalFiniteNormTransferInternal.fixedFiniteDimensional K
  letI : FiniteDimensional F E :=
    RationalFiniteNormTransferInternal.relativeFiniteDimensional
      K L hLK
  letI : IsScalarTower ℚ F E :=
    RationalFiniteNormTransferInternal.relativeScalarTower
      K L hLK
  letI : FiniteDimensional ℚ E :=
    RationalFiniteNormTransferInternal.relativeAbsoluteFiniteDimensional
      K L hLK
  letI : NumberField F :=
    RationalFiniteNormTransferInternal.fixedNumberField K
  letI : NumberField E :=
    RationalFiniteNormTransferInternal.relativeNumberField
      K L hLK
  letI : IsGalois F E :=
    RationalFiniteNormTransferInternal.relativeIsGalois
      K L hLK _hnormal
  let eK := rationalAbstractFixedFieldIdeleClassEquivFixed K
  let eAmbient :=
    extensionFixedRepresentationEquiv
      rationalIdeleClassRepresentation K L hLK _hnormal
  exact
    (MulEquiv.toAdditive
      (_root_.relativeIdeleClassBaseChangeMulEquiv
        (K := F) (L := E)))
      (rationalAbstractExtensionIdeleClassEquiv
        K L hLK _hnormal
        (eAmbient.symm
          (fixedFieldInclusion rationalIdeleClassRepresentation K L hLK
            (eK (Additive.ofMul c)))))


end RationalIdeleExtension

end IdealClassFieldTheory
end GlobalClassFieldTheory
