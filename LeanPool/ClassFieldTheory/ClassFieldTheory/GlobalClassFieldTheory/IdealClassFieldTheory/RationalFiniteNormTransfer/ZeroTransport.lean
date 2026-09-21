/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.RationalFiniteNormTransfer.Compatibility
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.RationalFiniteNormTransfer.MembershipTypes
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.RationalFiniteNormTransfer.Quotient
/-!
# Zero-class transport to norm membership

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
    zeroTransportIdeleClassGroupIsMulCommutative
    {F : Type} [Field F] [NumberField F] :
    IsMulCommutative (IdeleClassGroup F) :=
  RationalFiniteNormTransferInternal.ideleClassGroupIsMulCommutative

local instance
    zeroTransportIdeleClassSubgroupNormal
    {F : Type} [Field F] [NumberField F]
    (N : Subgroup (IdeleClassGroup F)) : N.Normal :=
  RationalFiniteNormTransferInternal.ideleClassSubgroupNormal N

/-- Internal finite-norm-class-zero to quotient-zero step. -/
private noncomputable def
    rationalFiniteNormTransferCanonicalFiniteNormClassZero_implies_finiteNormRepresentativeQuotientZero
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
      (hKfinite := hKfinite) K)
    (hincludeCanonical :
      rationalFiniteNormTransferCanonicalFiniteNormClassZero
        K H L hHK hLH c) :
    RationalFiniteNormTransferCanonicalFiniteNormRepresentativeQuotientZeroData
      K H L hHK hLH hLHnormal c := by
  refine ⟨?_⟩
  let hHfinite := RationalFiniteNormTransferInternal.absoluteFinite
    K H hHK (hKfinite := hKfinite) (hfinite := hKHfinite)
  change
    (0 : FiniteNormQuotient rationalIdeleClassRepresentation H L hLH) =
      finiteNormClass rationalIdeleClassRepresentation H L hLH
        (fixedFieldInclusion rationalIdeleClassRepresentation K H hHK
          (rationalAbstractFixedFieldIdeleClassEquivFixed K
            (Additive.ofMul c))) at hincludeCanonical
  let e :=
    rationalFiniteNormQuotientEquivIdeleClassNormQuotient
      (hKfinite := hHfinite) (hfinite := hHLfinite)
      H L hLH hLHnormal
  let q :=
    rationalFiniteNormTransferQuotientMap
      (hKfinite := hHfinite) (hfinite := hHLfinite)
      H L hLH hLHnormal
  let b : KummerTheory.ambientFixedAddSubgroup
      rationalIdeleClassRepresentation H :=
    fixedFieldInclusion rationalIdeleClassRepresentation K H hHK
      (rationalAbstractFixedFieldIdeleClassEquivFixed K
        (Additive.ofMul c))
  let finiteNormRepresentative :
      rationalFiniteNormTransferBaseIdeleClass
        (hKfinite := hHfinite) H :=
    Additive.toMul
      ((rationalAbstractFixedFieldIdeleClassEquivFixed H).symm b)
  change
    rationalFiniteNormTransferQuotientMap
        (hKfinite := hHfinite) (hfinite := hHLfinite)
        H L hLH hLHnormal finiteNormRepresentative =
      rationalFiniteNormQuotientEquivIdeleClassNormQuotient
        (hKfinite := hHfinite) (hfinite := hHLfinite)
        H L hLH hLHnormal 0
  have htransport :
      e
          (finiteNormClass rationalIdeleClassRepresentation H L hLH b) =
        q finiteNormRepresentative := by
    simpa only [e, q, b, finiteNormRepresentative] using
      (rationalFiniteNormTransferFiniteNormClass_spec
        (hKfinite := hHfinite) (hfinite := hHLfinite)
        H L hLH hLHnormal b)
  calc
    q finiteNormRepresentative =
        e (finiteNormClass rationalIdeleClassRepresentation H L hLH b) :=
      htransport.symm
    _ = e 0 := by
      apply congrArg e
      simpa only [b] using hincludeCanonical.symm

/-- Internal evaluation of the quotient equivalence at zero. -/
private noncomputable def
    rationalFiniteNormTransferFiniteNormRepresentativeQuotientZero_implies_targetZero
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
      (hKfinite := hKfinite) K)
    (hincludeCanonical :
      rationalFiniteNormTransferCanonicalFiniteNormClassZero
        K H L hHK hLH c) :
    RationalFiniteNormTransferCanonicalFiniteNormRepresentativeTargetZeroData
      (hKfinite := hKfinite) (hKHfinite := hKHfinite)
      (hHLfinite := hHLfinite)
      K H L hHK hLH hLHnormal c := by
  refine ⟨?_⟩
  let hHfinite := RationalFiniteNormTransferInternal.absoluteFinite
    K H hHK (hKfinite := hKfinite) (hfinite := hKHfinite)
  let : Zero
      (rationalFiniteNormTransferQuotientTarget
        (hKfinite := hHfinite) (hfinite := hHLfinite)
        H L hLH hLHnormal) :=
    RationalFiniteNormTransferInternal.quotientTargetZero
      (hKfinite := hHfinite) (hfinite := hHLfinite)
      H L hLH hLHnormal
  have hquotientZero :=
    rationalFiniteNormTransferCanonicalFiniteNormClassZero_implies_finiteNormRepresentativeQuotientZero
      (hKfinite := hKfinite) (hKHfinite := hKHfinite)
      (hHLfinite := hHLfinite)
      K H L hHK hLH hLHnormal c hincludeCanonical
  let e :=
    rationalFiniteNormQuotientEquivIdeleClassNormQuotient
      (hKfinite := hHfinite) (hfinite := hHLfinite)
      H L hLH hLHnormal
  let q :=
    rationalFiniteNormTransferQuotientMap
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
  have htransportZero := hquotientZero.equality
  change q finiteNormRepresentative = e 0 at htransportZero
  change q finiteNormRepresentative = 0
  exact htransportZero.trans e.map_zero

/-- Internal quotient-target zero to absolute norm-membership step. -/
private noncomputable def
    rationalFiniteNormTransferFiniteNormRepresentativeTargetZero_implies_membership
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
      (hKfinite := hKfinite) K)
    (hincludeCanonical :
      rationalFiniteNormTransferCanonicalFiniteNormClassZero
        K H L hHK hLH c) :
    RationalFiniteNormTransferCanonicalFiniteNormRepresentativeMembershipData
      (hKfinite := hKfinite) (hKHfinite := hKHfinite)
      (hHLfinite := hHLfinite)
      K H L hHK hLH hLHnormal c := by
  refine ⟨?_⟩
  let hHfinite := RationalFiniteNormTransferInternal.absoluteFinite
    K H hHK (hKfinite := hKfinite) (hfinite := hKHfinite)
  let F := abstractFixedField ℚ (SeparableClosure ℚ) H
  let U := abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLH
  let : FiniteDimensional ℚ F :=
    RationalFiniteNormTransferInternal.fixedFiniteDimensional H
  let : FiniteDimensional F U :=
    RationalFiniteNormTransferInternal.relativeFiniteDimensional
      H L hLH
  let : IsScalarTower ℚ F U :=
    RationalFiniteNormTransferInternal.relativeScalarTower
      H L hLH
  let : FiniteDimensional ℚ U :=
    RationalFiniteNormTransferInternal.relativeAbsoluteFiniteDimensional
      H L hLH
  let : NumberField F :=
    RationalFiniteNormTransferInternal.fixedNumberField H
  let : NumberField U :=
    RationalFiniteNormTransferInternal.relativeNumberField
      H L hLH
  let : IsGalois F U :=
    RationalFiniteNormTransferInternal.relativeIsGalois
      H L hLH hLHnormal
  let b :=
    fixedFieldInclusion rationalIdeleClassRepresentation K H hHK
      (rationalAbstractFixedFieldIdeleClassEquivFixed K
        (Additive.ofMul c))
  let finiteNormRepresentative : IdeleClassGroup F :=
    Additive.toMul
      ((rationalAbstractFixedFieldIdeleClassEquivFixed H).symm b)
  let q :=
    rationalFiniteNormTransferQuotientMap
      (hKfinite := hHfinite) (hfinite := hHLfinite)
      H L hLH hLHnormal
  let : Zero
      (rationalFiniteNormTransferQuotientTarget
        (hKfinite := hHfinite) (hfinite := hHLfinite)
        H L hLH hLHnormal) :=
    RationalFiniteNormTransferInternal.quotientTargetZero
      (hKfinite := hHfinite) (hfinite := hHLfinite)
      H L hLH hLHnormal
  have htargetZero :=
    rationalFiniteNormTransferFiniteNormRepresentativeQuotientZero_implies_targetZero
      (hKfinite := hKfinite) (hKHfinite := hKHfinite)
      (hHLfinite := hHLfinite)
      K H L hHK hLH hLHnormal c hincludeCanonical
  have htarget := htargetZero.equality
  change q finiteNormRepresentative = 0 at htarget
  change finiteNormRepresentative ∈
    (_root_.ideleClassNorm F U).range
  apply (QuotientGroup.eq_one_iff finiteNormRepresentative).1
  apply Additive.ofMul.injective
  change q finiteNormRepresentative = 0
  exact htarget

/-- Internal replacement of the absolute finite-norm representative by the
canonical ordinary extension representative. -/
private noncomputable def
    rationalFiniteNormTransferFiniteNormRepresentativeMembership_implies_canonicalAbsoluteMembership
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
      (hKfinite := hKfinite) K)
    (hincludeCanonical :
      rationalFiniteNormTransferCanonicalFiniteNormClassZero
        K H L hHK hLH c) :
    RationalFiniteNormTransferCanonicalAbsoluteNormMembershipData
      (hKfinite := hKfinite) (hKHfinite := hKHfinite)
      (hHLfinite := hHLfinite)
      K H L hHK hLH hHKnormal hLHnormal c := by
  refine ⟨?_⟩
  let hHfinite := RationalFiniteNormTransferInternal.absoluteFinite
    K H hHK (hKfinite := hKfinite) (hfinite := hKHfinite)
  let F := abstractFixedField ℚ (SeparableClosure ℚ) H
  let U := abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLH
  let : FiniteDimensional ℚ F :=
    RationalFiniteNormTransferInternal.fixedFiniteDimensional H
  let : FiniteDimensional F U :=
    RationalFiniteNormTransferInternal.relativeFiniteDimensional
      H L hLH
  let : IsScalarTower ℚ F U :=
    RationalFiniteNormTransferInternal.relativeScalarTower
      H L hLH
  let : FiniteDimensional ℚ U :=
    RationalFiniteNormTransferInternal.relativeAbsoluteFiniteDimensional
      H L hLH
  let : NumberField F :=
    RationalFiniteNormTransferInternal.fixedNumberField H
  let : NumberField U :=
    RationalFiniteNormTransferInternal.relativeNumberField
      H L hLH
  let : IsGalois F U :=
    RationalFiniteNormTransferInternal.relativeIsGalois
      H L hLH hLHnormal
  have hmembership :=
    rationalFiniteNormTransferFiniteNormRepresentativeTargetZero_implies_membership
      (hKfinite := hKfinite) (hKHfinite := hKHfinite)
      (hHLfinite := hHLfinite)
      K H L hHK hLH hLHnormal c hincludeCanonical
  have hfixedToExtension :=
    rationalFiniteNormTransferCanonicalFixedRepresentative_eq_extension
      K H hHK hHKnormal c
  change
    rationalFiniteNormTransferCanonicalFixedRepresentative K H hHK c =
      rationalFiniteNormTransferOrdinaryExtensionRepresentative
        K H hHK hHKnormal c at hfixedToExtension
  change
    rationalFiniteNormTransferOrdinaryExtensionRepresentative
        K H hHK hHKnormal c ∈
      (_root_.ideleClassNorm F U).range
  rw [← hfixedToExtension]
  exact hmembership.membership

/-- Internal transport of the canonical absolute norm membership to the
relative ordinary-extension field spine. -/
private theorem
    rationalFiniteNormTransferCanonicalAbsoluteMembership_implies_relativeMembership
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
      (hKfinite := hKfinite) K)
    (hincludeCanonical :
      rationalFiniteNormTransferCanonicalFiniteNormClassZero
        K H L hHK hLH c) :
    rationalFiniteNormTransferCanonicalOrdinaryExtensionNormMembership
      K H L hHK hLH hHKnormal hLHnormal c := by
  let hHfinite := RationalFiniteNormTransferInternal.absoluteFinite
    K H hHK (hKfinite := hKfinite) (hfinite := hKHfinite)
  let E := abstractRelativeFixedField ℚ (SeparableClosure ℚ) hHK
  let U := abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLH
  let : FiniteDimensional ℚ E :=
    RationalFiniteNormTransferInternal.relativeAbsoluteFiniteDimensional
      K H hHK
  let : NumberField E :=
    RationalFiniteNormTransferInternal.relativeNumberField
      K H hHK
  let : FiniteDimensional ℚ U :=
    RationalFiniteNormTransferInternal.relativeAbsoluteFiniteDimensional
      H L hLH
  let : NumberField U :=
    RationalFiniteNormTransferInternal.relativeNumberField
      H L hLH
  let : Algebra E U := by
    change Algebra
      (abstractFixedField ℚ (SeparableClosure ℚ) H) U
    exact U.algebra
  let : Module E U := by
    change Module
      (abstractFixedField ℚ (SeparableClosure ℚ) H) U
    exact
      (U.algebra : Algebra
        (abstractFixedField ℚ (SeparableClosure ℚ) H) U).toModule
  let : FiniteDimensional E U := by
    change FiniteDimensional
      (abstractFixedField ℚ (SeparableClosure ℚ) H) U
    exact RationalFiniteNormTransferInternal.relativeFiniteDimensional
      H L hLH
  let : IsScalarTower ℚ E U := by
    change IsScalarTower ℚ
      (abstractFixedField ℚ (SeparableClosure ℚ) H) U
    exact RationalFiniteNormTransferInternal.relativeScalarTower
      H L hLH
  let : IsGalois E U := by
    change IsGalois
      (abstractFixedField ℚ (SeparableClosure ℚ) H) U
    exact RationalFiniteNormTransferInternal.relativeIsGalois
      H L hLH hLHnormal
  have habsoluteData :=
    rationalFiniteNormTransferFiniteNormRepresentativeMembership_implies_canonicalAbsoluteMembership
      (hKfinite := hKfinite) (hKHfinite := hKHfinite)
      (hHLfinite := hHLfinite)
      K H L hHK hLH hHKnormal hLHnormal c hincludeCanonical
  have habsolute := habsoluteData.membership
  change
    rationalFiniteNormTransferOrdinaryExtensionRepresentative
        K H hHK hHKnormal c ∈
    (_root_.ideleClassNorm E U).range at habsolute
  unfold
    rationalFiniteNormTransferCanonicalOrdinaryExtensionNormMembership
  change
    rationalFiniteNormTransferOrdinaryExtensionRepresentative
        K H hHK hHKnormal c ∈
      (_root_.ideleClassNorm E U).range
  exact habsolute

/-- A zero canonical finite-norm class forces the ordinary idele class
extended to the intermediate fixed field to lie in the relative norm range. -/
theorem
    rationalFiniteNormTransferCanonicalFiniteNormClassZero_implies_normMembership
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
      (hKfinite := hKfinite) K)
    (hincludeCanonical :
      rationalFiniteNormTransferCanonicalFiniteNormClassZero
        K H L hHK hLH c) :
    rationalFiniteNormTransferCanonicalOrdinaryExtensionNormMembership
      K H L hHK hLH hHKnormal hLHnormal c := by
  exact
    rationalFiniteNormTransferCanonicalAbsoluteMembership_implies_relativeMembership
      (hKfinite := hKfinite) (hKHfinite := hKHfinite)
      (hHLfinite := hHLfinite)
      K H L hHK hLH hHKnormal hLHnormal c hincludeCanonical

end RationalIdeleExtension

end IdealClassFieldTheory
end GlobalClassFieldTheory
