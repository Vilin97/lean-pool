/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.RationalFiniteNormTransfer.Representatives
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.RationalFiniteNormTransfer.Quotient
/-!
# Named membership endpoints for rational finite-norm transport

This compiled leaf preserves the original public declarations while reusing
the shared fixed-field instance providers.
-/

@[expose] public section

noncomputable
section

namespace GlobalClassFieldTheory
namespace IdealClassFieldTheory

open ClassFormation
open CyclicCohomology

section RationalIdeleExtension

open Reciprocity
open LocalClassFieldTheory

local instance
    membershipTypesIdeleClassGroupIsMulCommutative
    {F : Type} [Field F] [NumberField F] :
    IsMulCommutative (IdeleClassGroup F) :=
  RationalFiniteNormTransferInternal.ideleClassGroupIsMulCommutative

local instance
    membershipTypesIdeleClassSubgroupNormal
    {F : Type} [Field F] [NumberField F]
    (N : Subgroup (IdeleClassGroup F)) : N.Normal :=
  RationalFiniteNormTransferInternal.ideleClassSubgroupNormal N

/-- Membership in the ordinary norm range on the relative `K/H/L` field
spine.  The absolute `H` presentation used by the finite-norm quotient does
not occur in this public endpoint. -/
noncomputable def rationalFiniteNormTransferRelativeNormMembership
    (K H L : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (hHK : H.toSubgroup ≤ K.toSubgroup)
    (hLH : L.toSubgroup ≤ H.toSubgroup)
    (_hLHnormal : (extensionSubgroup H L hLH).Normal)
    [hKfinite : Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          K (le_baseField K))]
    [hKHfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K H hHK)]
    [hHLfinite : Finite
      (H.toSubgroup ⧸ extensionSubgroup H L hLH)]
    (c : rationalFiniteNormTransferExtensionIdeleClass K H hHK) : Prop :=
  letI := RationalFiniteNormTransferInternal.absoluteFinite
    K H hHK (hKfinite := hKfinite) (hfinite := hKHfinite)
  let B := abstractFixedField ℚ (SeparableClosure ℚ) K
  let E := abstractRelativeFixedField ℚ (SeparableClosure ℚ) hHK
  let F := abstractFixedField ℚ (SeparableClosure ℚ) H
  let U := abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLH
  letI : FiniteDimensional ℚ B :=
    RationalFiniteNormTransferInternal.fixedFiniteDimensional K
  letI : FiniteDimensional B E :=
    RationalFiniteNormTransferInternal.relativeFiniteDimensional
      K H hHK
  letI : IsScalarTower ℚ B E :=
    RationalFiniteNormTransferInternal.relativeScalarTower
      K H hHK
  letI : FiniteDimensional ℚ E :=
    RationalFiniteNormTransferInternal.relativeAbsoluteFiniteDimensional
      K H hHK
  letI : NumberField E :=
    RationalFiniteNormTransferInternal.relativeNumberField
      K H hHK
  letI : FiniteDimensional ℚ F :=
    RationalFiniteNormTransferInternal.fixedFiniteDimensional H
  letI : FiniteDimensional ℚ U :=
    RationalFiniteNormTransferInternal.relativeAbsoluteFiniteDimensional
      H L hLH
  letI : NumberField F :=
    RationalFiniteNormTransferInternal.fixedNumberField H
  letI : NumberField U :=
    RationalFiniteNormTransferInternal.relativeNumberField
      H L hLH
  letI : Algebra E U := by
    change Algebra F U
    exact U.algebra
  letI : Module E U := by
    change Module F U
    exact (U.algebra : Algebra F U).toModule
  letI : FiniteDimensional E U := by
    change FiniteDimensional F U
    exact RationalFiniteNormTransferInternal.relativeFiniteDimensional
      H L hLH
  letI : IsScalarTower ℚ E U := by
    change IsScalarTower ℚ F U
    exact RationalFiniteNormTransferInternal.relativeScalarTower
      H L hLH
  letI : IsGalois E U := by
    change IsGalois F U
    exact RationalFiniteNormTransferInternal.relativeIsGalois
      H L hLH _hLHnormal
  c ∈ (_root_.ideleClassNorm E U).range

/-- The named relative norm-membership endpoint for the canonical ordinary
extension representative. -/
@[irreducible]
noncomputable def
    rationalFiniteNormTransferCanonicalOrdinaryExtensionNormMembership
    (K H L : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (hHK : H.toSubgroup ≤ K.toSubgroup)
    (hLH : L.toSubgroup ≤ H.toSubgroup)
    (hHKnormal : (extensionSubgroup K H hHK).Normal)
    (hLHnormal : (extensionSubgroup H L hLH).Normal)
    [hKfinite : Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          K (le_baseField K))]
    [hKHfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K H hHK)]
    [hHLfinite : Finite
      (H.toSubgroup ⧸ extensionSubgroup H L hLH)]
    (c : rationalFiniteNormTransferBaseIdeleClass
      (hKfinite := hKfinite) K) : Prop :=
  rationalFiniteNormTransferRelativeNormMembership
    K H L hHK hLH hLHnormal
      (rationalFiniteNormTransferOrdinaryExtensionRepresentative
        K H hHK hHKnormal c)

/-- The absolute-`H` norm-membership endpoint used internally by the finite
norm quotient before transport to the relative `K/H` presentation. -/
noncomputable def
    rationalFiniteNormTransferCanonicalOrdinaryExtensionAbsoluteNormMembership
    (K H L : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (hHK : H.toSubgroup ≤ K.toSubgroup)
    (hLH : L.toSubgroup ≤ H.toSubgroup)
    (hHKnormal : (extensionSubgroup K H hHK).Normal)
    (hLHnormal : (extensionSubgroup H L hLH).Normal)
    [hKfinite : Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          K (le_baseField K))]
    [hKHfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K H hHK)]
    [hHLfinite : Finite
      (H.toSubgroup ⧸ extensionSubgroup H L hLH)]
    (c : rationalFiniteNormTransferBaseIdeleClass
      (hKfinite := hKfinite) K) : Prop :=
  letI := RationalFiniteNormTransferInternal.absoluteFinite
    K H hHK (hKfinite := hKfinite) (hfinite := hKHfinite)
  let F := abstractFixedField ℚ (SeparableClosure ℚ) H
  let U := abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLH
  letI : FiniteDimensional ℚ F :=
    RationalFiniteNormTransferInternal.fixedFiniteDimensional H
  letI : FiniteDimensional F U :=
    RationalFiniteNormTransferInternal.relativeFiniteDimensional
      H L hLH
  letI : IsScalarTower ℚ F U :=
    RationalFiniteNormTransferInternal.relativeScalarTower
      H L hLH
  letI : FiniteDimensional ℚ U :=
    RationalFiniteNormTransferInternal.relativeAbsoluteFiniteDimensional
      H L hLH
  letI : NumberField F :=
    RationalFiniteNormTransferInternal.fixedNumberField H
  letI : NumberField U :=
    RationalFiniteNormTransferInternal.relativeNumberField
      H L hLH
  letI : IsGalois F U :=
    RationalFiniteNormTransferInternal.relativeIsGalois
      H L hLH hLHnormal
  rationalFiniteNormTransferOrdinaryExtensionRepresentative
      K H hHK hHKnormal c ∈
    (_root_.ideleClassNorm F U).range

/-- Absolute norm membership of the canonical representative produced by the
finite-norm-class comparison. -/
noncomputable def
    rationalFiniteNormTransferCanonicalFiniteNormRepresentativeAbsoluteNormMembership
    (K H L : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (hHK : H.toSubgroup ≤ K.toSubgroup)
    (hLH : L.toSubgroup ≤ H.toSubgroup)
    (hLHnormal : (extensionSubgroup H L hLH).Normal)
    [hKfinite : Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          K (le_baseField K))]
    [hKHfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K H hHK)]
    [hHLfinite : Finite
      (H.toSubgroup ⧸ extensionSubgroup H L hLH)]
    (c : rationalFiniteNormTransferBaseIdeleClass
      (hKfinite := hKfinite) K) : Prop :=
  letI := RationalFiniteNormTransferInternal.absoluteFinite
    K H hHK (hKfinite := hKfinite) (hfinite := hKHfinite)
  let F := abstractFixedField ℚ (SeparableClosure ℚ) H
  let U := abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLH
  letI : FiniteDimensional ℚ F :=
    RationalFiniteNormTransferInternal.fixedFiniteDimensional H
  letI : FiniteDimensional F U :=
    RationalFiniteNormTransferInternal.relativeFiniteDimensional
      H L hLH
  letI : IsScalarTower ℚ F U :=
    RationalFiniteNormTransferInternal.relativeScalarTower
      H L hLH
  letI : FiniteDimensional ℚ U :=
    RationalFiniteNormTransferInternal.relativeAbsoluteFiniteDimensional
      H L hLH
  letI : NumberField F :=
    RationalFiniteNormTransferInternal.fixedNumberField H
  letI : NumberField U :=
    RationalFiniteNormTransferInternal.relativeNumberField
      H L hLH
  letI : IsGalois F U :=
    RationalFiniteNormTransferInternal.relativeIsGalois
      H L hLH hLHnormal
  let b :=
    fixedFieldInclusion rationalIdeleClassRepresentation K H hHK
      (rationalAbstractFixedFieldIdeleClassEquivFixed K
        (Additive.ofMul c))
  Additive.toMul
      ((rationalAbstractFixedFieldIdeleClassEquivFixed H).symm b) ∈
    (_root_.ideleClassNorm F U).range

/-- Packaged absolute membership of the finite-norm representative. -/
structure RationalFiniteNormTransferCanonicalFiniteNormRepresentativeMembershipData
    (K H L : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (hHK : H.toSubgroup ≤ K.toSubgroup)
    (hLH : L.toSubgroup ≤ H.toSubgroup)
    (hLHnormal : (extensionSubgroup H L hLH).Normal)
    [hKfinite : Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          K (le_baseField K))]
    [hKHfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K H hHK)]
    [hHLfinite : Finite
      (H.toSubgroup ⧸ extensionSubgroup H L hLH)]
    (c : rationalFiniteNormTransferBaseIdeleClass
      (hKfinite := hKfinite) K) : Prop where
  /-- The packaged finite-norm-representative membership proof. -/
  membership :
    rationalFiniteNormTransferCanonicalFiniteNormRepresentativeAbsoluteNormMembership
      K H L hHK hLH hLHnormal c

/-- The finite-norm representative and zero have the same named ordinary
quotient value. -/
noncomputable def
    rationalFiniteNormTransferCanonicalFiniteNormRepresentativeQuotientZero
    (K H L : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (hHK : H.toSubgroup ≤ K.toSubgroup)
    (hLH : L.toSubgroup ≤ H.toSubgroup)
    (hLHnormal : (extensionSubgroup H L hLH).Normal)
    [hKfinite : Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          K (le_baseField K))]
    [hKHfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K H hHK)]
    [hHLfinite : Finite
      (H.toSubgroup ⧸ extensionSubgroup H L hLH)]
    (c : rationalFiniteNormTransferBaseIdeleClass
      (hKfinite := hKfinite) K) : Prop :=
  letI hHfinite := RationalFiniteNormTransferInternal.absoluteFinite
    K H hHK (hKfinite := hKfinite) (hfinite := hKHfinite)
  let b :=
    fixedFieldInclusion rationalIdeleClassRepresentation K H hHK
      (rationalAbstractFixedFieldIdeleClassEquivFixed K
        (Additive.ofMul c))
  let finiteNormRepresentative :
      rationalFiniteNormTransferBaseIdeleClass
        (hKfinite := hHfinite) H :=
    Additive.toMul
      ((rationalAbstractFixedFieldIdeleClassEquivFixed H).symm b)
  rationalFiniteNormTransferQuotientMap
      (hKfinite := hHfinite) (hfinite := hHLfinite)
      H L hLH hLHnormal finiteNormRepresentative =
    rationalFiniteNormQuotientEquivIdeleClassNormQuotient
      (hKfinite := hHfinite) (hfinite := hHLfinite)
      H L hLH hLHnormal 0

/-- Packaged quotient-zero comparison for the finite-norm representative. -/
structure RationalFiniteNormTransferCanonicalFiniteNormRepresentativeQuotientZeroData
    (K H L : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (hHK : H.toSubgroup ≤ K.toSubgroup)
    (hLH : L.toSubgroup ≤ H.toSubgroup)
    (hLHnormal : (extensionSubgroup H L hLH).Normal)
    [hKfinite : Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          K (le_baseField K))]
    [hKHfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K H hHK)]
    [hHLfinite : Finite
      (H.toSubgroup ⧸ extensionSubgroup H L hLH)]
    (c : rationalFiniteNormTransferBaseIdeleClass
      (hKfinite := hKfinite) K) : Prop where
  /-- The packaged quotient-zero equality. -/
  equality :
    rationalFiniteNormTransferCanonicalFiniteNormRepresentativeQuotientZero
      K H L hHK hLH hLHnormal c

/-- The named quotient-target zero equality obtained after evaluating the
finite-norm quotient equivalence at zero. -/
noncomputable def
    rationalFiniteNormTransferCanonicalFiniteNormRepresentativeTargetZero
    (K H L : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (hHK : H.toSubgroup ≤ K.toSubgroup)
    (hLH : L.toSubgroup ≤ H.toSubgroup)
    (hLHnormal : (extensionSubgroup H L hLH).Normal)
    [hKfinite : Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          K (le_baseField K))]
    [hKHfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K H hHK)]
    [hHLfinite : Finite
      (H.toSubgroup ⧸ extensionSubgroup H L hLH)]
    (c : rationalFiniteNormTransferBaseIdeleClass
      (hKfinite := hKfinite) K) : Prop :=
  letI hHfinite := RationalFiniteNormTransferInternal.absoluteFinite
    K H hHK (hKfinite := hKfinite) (hfinite := hKHfinite)
  letI : Zero
      (rationalFiniteNormTransferQuotientTarget
        (hKfinite := hHfinite) (hfinite := hHLfinite)
        H L hLH hLHnormal) :=
    RationalFiniteNormTransferInternal.quotientTargetZero
      (hKfinite := hHfinite) (hfinite := hHLfinite)
      H L hLH hLHnormal
  let b :=
    fixedFieldInclusion rationalIdeleClassRepresentation K H hHK
      (rationalAbstractFixedFieldIdeleClassEquivFixed K
        (Additive.ofMul c))
  let finiteNormRepresentative :
      rationalFiniteNormTransferBaseIdeleClass
        (hKfinite := hHfinite) H :=
    Additive.toMul
      ((rationalAbstractFixedFieldIdeleClassEquivFixed H).symm b)
  rationalFiniteNormTransferQuotientMap
      (hKfinite := hHfinite) (hfinite := hHLfinite)
      H L hLH hLHnormal finiteNormRepresentative = 0

/-- Packaged quotient-target zero equality for the finite-norm
representative. -/
structure RationalFiniteNormTransferCanonicalFiniteNormRepresentativeTargetZeroData
    (K H L : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (hHK : H.toSubgroup ≤ K.toSubgroup)
    (hLH : L.toSubgroup ≤ H.toSubgroup)
    (hLHnormal : (extensionSubgroup H L hLH).Normal)
    [hKfinite : Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          K (le_baseField K))]
    [hKHfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K H hHK)]
    [hHLfinite : Finite
      (H.toSubgroup ⧸ extensionSubgroup H L hLH)]
    (c : rationalFiniteNormTransferBaseIdeleClass
      (hKfinite := hKfinite) K) : Prop where
  /-- The packaged target-zero equality. -/
  equality :
    rationalFiniteNormTransferCanonicalFiniteNormRepresentativeTargetZero
      K H L hHK hLH hLHnormal c

/-- Packaged absolute norm membership used to keep the provider proof's
dependent field spine out of declaration finalization. -/
structure RationalFiniteNormTransferCanonicalAbsoluteNormMembershipData
    (K H L : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (hHK : H.toSubgroup ≤ K.toSubgroup)
    (hLH : L.toSubgroup ≤ H.toSubgroup)
    (hHKnormal : (extensionSubgroup K H hHK).Normal)
    (hLHnormal : (extensionSubgroup H L hLH).Normal)
    [hKfinite : Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          K (le_baseField K))]
    [hKHfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K H hHK)]
    [hHLfinite : Finite
      (H.toSubgroup ⧸ extensionSubgroup H L hLH)]
    (c : rationalFiniteNormTransferBaseIdeleClass
      (hKfinite := hKfinite) K) : Prop where
  /-- The packaged absolute norm-membership proof. -/
  membership :
    rationalFiniteNormTransferCanonicalOrdinaryExtensionAbsoluteNormMembership
      K H L hHK hLH hHKnormal hLHnormal c

/-- Packaged relative norm membership used as the final internal provider
boundary before exposing the canonical theorem. -/
structure RationalFiniteNormTransferCanonicalNormMembershipData
    (K H L : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (hHK : H.toSubgroup ≤ K.toSubgroup)
    (hLH : L.toSubgroup ≤ H.toSubgroup)
    (hHKnormal : (extensionSubgroup K H hHK).Normal)
    (hLHnormal : (extensionSubgroup H L hLH).Normal)
    [hKfinite : Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          K (le_baseField K))]
    [hKHfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K H hHK)]
    [hHLfinite : Finite
      (H.toSubgroup ⧸ extensionSubgroup H L hLH)]
    (c : rationalFiniteNormTransferBaseIdeleClass
      (hKfinite := hKfinite) K) : Prop where
  /-- The packaged relative norm-membership proof. -/
  membership :
    rationalFiniteNormTransferCanonicalOrdinaryExtensionNormMembership
      K H L hHK hLH hHKnormal hLHnormal c


end RationalIdeleExtension

end IdealClassFieldTheory
end GlobalClassFieldTheory
