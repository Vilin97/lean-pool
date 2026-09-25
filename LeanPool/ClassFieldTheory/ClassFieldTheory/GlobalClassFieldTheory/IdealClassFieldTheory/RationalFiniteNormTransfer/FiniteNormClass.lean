/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.RationalFiniteNormTransfer.Representatives
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.RationalFiniteNormTransfer.Quotient
/-!
# Finite norm-class evaluation after fixed-field inclusion

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
    finiteNormClassIdeleClassGroupIsMulCommutative
    {F : Type} [Field F] [NumberField F] :
    IsMulCommutative (IdeleClassGroup F) :=
  RationalFiniteNormTransferInternal.ideleClassGroupIsMulCommutative

local instance
    finiteNormClassIdeleClassSubgroupNormal
    {F : Type} [Field F] [NumberField F]
    (N : Subgroup (IdeleClassGroup F)) : N.Normal :=
  RationalFiniteNormTransferInternal.ideleClassSubgroupNormal N

/-- Transporting a finite norm class after fixed-field inclusion is the
canonical norm-quotient class of its named abstract representative. The three
fields are supplied directly so clients that already have their finite-extension
context do not rebuild an intermediate-subgroup instance tower. -/
theorem rationalFiniteNormTransferFiniteNormClass_eq_abstractRepresentative
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
    [hHfinite : Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          H (le_baseField H))]
    [hHLfinite : Finite
      (H.toSubgroup ⧸ extensionSubgroup H L hLH)]
    (a : KummerTheory.ambientFixedAddSubgroup
      rationalIdeleClassRepresentation K) :
    rationalFiniteNormQuotientEquivIdeleClassNormQuotient
        H L hLH hLHnormal
        (finiteNormClass rationalIdeleClassRepresentation H L hLH
          (fixedFieldInclusion rationalIdeleClassRepresentation
            K H hHK a)) =
      rationalFiniteNormTransferQuotientMap
        H L hLH hLHnormal
        (rationalFiniteNormTransferAbstractRepresentative
          K H hHK a) := by
  let q :
      rationalFiniteNormTransferBaseIdeleClass
          (hKfinite := hHfinite) H →
        rationalFiniteNormTransferQuotientTarget
          (hKfinite := hHfinite) (hfinite := hHLfinite)
          H L hLH hLHnormal :=
    fun c => Additive.ofMul (QuotientGroup.mk c)
  let abstractRepresentative :
      rationalFiniteNormTransferBaseIdeleClass
        (hKfinite := hHfinite) H :=
    rationalFiniteNormTransferAbstractRepresentative
      (hKfinite := hKfinite) (hfinite := hKHfinite)
      K H hHK a
  have hclass :
      rationalFiniteNormQuotientEquivIdeleClassNormQuotient
          H L hLH hLHnormal
          (finiteNormClass rationalIdeleClassRepresentation H L hLH
            (fixedFieldInclusion rationalIdeleClassRepresentation
              K H hHK a)) =
        q abstractRepresentative :=
    rationalFiniteNormTransferFiniteNormClass_spec
      (hKfinite := hHfinite) (hfinite := hHLfinite)
      H L hLH hLHnormal
      (fixedFieldInclusion rationalIdeleClassRepresentation
        K H hHK a)
  exact hclass


end RationalIdeleExtension

end IdealClassFieldTheory
end GlobalClassFieldTheory
