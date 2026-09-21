/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.RationalFiniteNormTransfer.FieldSpine
/-!
# Norm quotient maps for rational finite-norm transport

This compiled leaf preserves the original public declarations while reusing
the shared fixed-field instance providers.
-/

noncomputable section

namespace GlobalClassFieldTheory
namespace IdealClassFieldTheory

open ClassFormation
open CyclicCohomology

section RationalIdeleExtension

open Reciprocity
open LocalClassFieldTheory

local instance
    quotientIdeleClassGroupIsMulCommutative
    {F : Type} [Field F] [NumberField F] :
    IsMulCommutative (IdeleClassGroup F) :=
  RationalFiniteNormTransferInternal.ideleClassGroupIsMulCommutative

local instance
    quotientIdeleClassSubgroupNormal
    {F : Type} [Field F] [NumberField F]
    (N : Subgroup (IdeleClassGroup F)) : N.Normal :=
  RationalFiniteNormTransferInternal.ideleClassSubgroupNormal N

/-- The canonical map from ordinary idele classes to the additive norm
quotient used by rational finite-norm transport. -/
noncomputable def rationalFiniteNormTransferQuotientMap
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
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)] :
    rationalFiniteNormTransferBaseIdeleClass K →
      rationalFiniteNormTransferQuotientTarget
        K L hLK hnormal := by
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
  exact fun c : IdeleClassGroup F =>
    Additive.ofMul (QuotientGroup.mk c)

/-- Membership in the ordinary norm range represented by the rational
finite-norm quotient. -/
noncomputable def rationalFiniteNormTransferNormMembership
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
      K L hLK hnormal
  c ∈ (_root_.ideleClassNorm F E).range

/-- A rational finite norm class is sent to the canonical quotient class of
its ordinary idele-class representative. -/
theorem rationalFiniteNormTransferFiniteNormClass_spec
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
    (b : KummerTheory.ambientFixedAddSubgroup
      rationalIdeleClassRepresentation K) :
    rationalFiniteNormQuotientEquivIdeleClassNormQuotient
        K L hLK hnormal
        (finiteNormClass rationalIdeleClassRepresentation K L hLK b) =
      rationalFiniteNormTransferQuotientMap
        K L hLK hnormal
        (Additive.toMul
          ((rationalAbstractFixedFieldIdeleClassEquivFixed K).symm b)) := by
  have h :=
    rationalFiniteNormQuotientEquivIdeleClassNormQuotient_finiteNormClass
      (hKfinite := hKfinite) (hfinite := hfinite)
      K L hLK hnormal b
  exact h

/-- The named zero-class input for the canonical finite-norm transfer. -/
noncomputable def rationalFiniteNormTransferCanonicalFiniteNormClassZero
    (K H L : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (hHK : H.toSubgroup ≤ K.toSubgroup)
    (hLH : L.toSubgroup ≤ H.toSubgroup)
    [hKfinite : Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          K (le_baseField K))]
    [hHLfinite : Finite
      (H.toSubgroup ⧸ extensionSubgroup H L hLH)]
    (c : rationalFiniteNormTransferBaseIdeleClass
      (hKfinite := hKfinite) K) : Prop :=
  (0 : FiniteNormQuotient rationalIdeleClassRepresentation H L hLH) =
    finiteNormClass rationalIdeleClassRepresentation H L hLH
      (fixedFieldInclusion rationalIdeleClassRepresentation K H hHK
        (rationalAbstractFixedFieldIdeleClassEquivFixed K
          (Additive.ofMul c)))

end RationalIdeleExtension

end IdealClassFieldTheory
end GlobalClassFieldTheory
