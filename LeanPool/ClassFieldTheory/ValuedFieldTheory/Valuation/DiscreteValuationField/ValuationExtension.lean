/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.DiscreteValuationField.Extensions

/-! # Valuation Extension -/
namespace ValuationTheory

/-!
# Valuation extensions

Mathlib's uniqueness criterion for valuations is expressed through
`Valuation.IsEquiv`: two valuations on the same field are equivalent exactly
when they have the same valuation subring.  The results here use the ambient
valued-extension property directly; no marker object is introduced.
-/

noncomputable section

universe u v w x y

namespace DiscreteValuationField
namespace ValuedExtension

variable {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]

section EquivalentBase

variable {Gamma₁ Gamma₂ GammaL : Type*}
variable [LinearOrderedCommGroupWithZero Gamma₁]
variable [LinearOrderedCommGroupWithZero Gamma₂]
variable [LinearOrderedCommGroupWithZero GammaL]

/-- Replacing the base valuation by an equivalent valuation preserves the
extension relation. -/
theorem hasExtension_of_isEquiv_base
    {v₁ : _root_.Valuation K Gamma₁}
    {v₂ : _root_.Valuation K Gamma₂}
    {wL : _root_.Valuation L GammaL}
    (h : v₁.IsEquiv v₂) [v₂.HasExtension wL] :
    v₁.HasExtension wL where
  val_isEquiv_comap :=
    h.trans
      (_root_.Valuation.HasExtension.val_isEquiv_comap
        (vR := v₂) (vA := wL))

end EquivalentBase

section ComapAlongCompatibleEmbedding

variable {M : Type y} [Field M] [Algebra K M]
variable {GammaK GammaM : Type*}
variable [LinearOrderedCommGroupWithZero GammaK]
variable [LinearOrderedCommGroupWithZero GammaM]

/-- If an ambient valuation extends the base valuation, then its pullback
along any field embedding compatible with the two base embeddings also
extends the base valuation. -/
theorem hasExtension_comap_of_algebraMap_compatible
    {vK : _root_.Valuation K GammaK}
    {vM : _root_.Valuation M GammaM}
    (ι : L →+* M)
    (hι :
      ι.comp (algebraMap K L) =
        algebraMap K M)
    [vK.HasExtension vM] :
    vK.HasExtension (vM.comap ι) where
  val_isEquiv_comap := by
    rw [_root_.Valuation.isEquiv_iff_val_le_one]
    intro a
    change
      vK a ≤ 1 ↔
        vM (ι (algebraMap K L a)) ≤ 1
    rw [show ι (algebraMap K L a) = algebraMap K M a by
      exact DFunLike.congr_fun hι a]
    exact
      (_root_.Valuation.HasExtension.val_map_le_one_iff
        (vR := vK) (vA := vM) a).symm

end ComapAlongCompatibleEmbedding

section LocalValuationSubringMap

variable (base : CompleteDVF.{u, v} K) (target : CompleteDVF.{w, x} L)

/-- A local map between the valuation rings, whose map on fraction fields is
the given algebra map, determines an extension of valuations.

The locality hypothesis is the essential point: if an element of the base
field is not integral, its inverse lies in the maximal ideal.  Locality sends
that inverse into the target maximal ideal, so the image of the original
element cannot be integral. -/
theorem valuation_hasExtension_of_local_valuationSubring_map
    (f : base.valuationSubring →+* target.valuationSubring)
    [IsLocalHom f]
    (hcoe : ∀ z : base.valuationSubring,
      ((f z : target.valuationSubring) : L) =
        algebraMap K L (z : K)) :
    base.valuation.HasExtension target.valuation := by
  apply _root_.Valuation.HasExtension.ofComapInteger
  ext z
  change
    algebraMap K L z ∈ target.valuation.valuationSubring ↔
      z ∈ base.valuation.valuationSubring
  constructor
  · intro hzTarget
    by_contra hzBase
    have hz_ne : z ≠ 0 := by
      intro hz
      subst z
      exact hzBase base.valuation.valuationSubring.zero_mem
    have hinvNonunit :
        z⁻¹ ∈ base.valuation.valuationSubring.nonunits :=
      (base.valuation.valuationSubring.inv_mem_nonunits_iff).2
        (Or.inr hzBase)
    let zinverse : base.valuationSubring :=
      ⟨z⁻¹,
        base.valuation.valuationSubring.nonunits_subset hinvNonunit⟩
    have hzinverseMaximal :
        zinverse ∈ IsLocalRing.maximalIdeal base.valuationSubring := by
      apply
        base.valuation.valuationSubring.coe_mem_nonunits_iff.mp
      exact hinvNonunit
    have hmapMaximal :
        f zinverse ∈ IsLocalRing.maximalIdeal target.valuationSubring :=
      map_nonunit f zinverse hzinverseMaximal
    let ztarget : target.valuationSubring :=
      ⟨algebraMap K L z, hzTarget⟩
    have hproduct : f zinverse * ztarget = 1 := by
      apply Subtype.ext
      change
        ((f zinverse : target.valuationSubring) : L) *
            algebraMap K L z =
          1
      rw [hcoe]
      change algebraMap K L (z⁻¹) * algebraMap K L z = 1
      rw [← map_mul, inv_mul_cancel₀ hz_ne, map_one]
    have hone :
        (1 : target.valuationSubring) ∈
          IsLocalRing.maximalIdeal target.valuationSubring := by
      rw [← hproduct]
      exact
        (IsLocalRing.maximalIdeal target.valuationSubring).mul_mem_right
          ztarget hmapMaximal
    exact
      (IsLocalRing.maximalIdeal.isMaximal target.valuationSubring).isPrime.one_notMem
        hone
  · intro hzBase
    let zbase : base.valuationSubring := ⟨z, hzBase⟩
    have hzMap :
        ((f zbase : target.valuationSubring) : L) ∈
          target.valuation.valuationSubring :=
      (f zbase).property
    rwa [hcoe] at hzMap

/-- An equivalence of valuation subrings whose underlying field map is the
given algebra map determines an extension of valuations.  Surjectivity makes
the induced ring homomorphism local, so this is the source-producing
equivalence form of
`valuation_hasExtension_of_local_valuationSubring_map`. -/
theorem valuation_hasExtension_of_valuationSubring_equiv
    (e : base.valuationSubring ≃+* target.valuationSubring)
    (hcoe : ∀ z : base.valuationSubring,
      ((e z : target.valuationSubring) : L) =
        algebraMap K L (z : K)) :
    base.valuation.HasExtension target.valuation := by
  let : IsLocalHom e.toRingHom :=
    IsLocalHom.of_surjective e.toRingHom e.surjective
  exact
    valuation_hasExtension_of_local_valuationSubring_map
      base target e.toRingHom hcoe

end LocalValuationSubringMap

section Pullback

variable (base : CompleteDVF.{u, v} K) (target : CompleteDVF.{w, x} L)
variable [base.valuation.HasExtension target.valuation]

/-- The target valuation subring pulls back to the base valuation subring. -/
theorem comap_valuationSubring_eq_base :
    target.valuation.valuationSubring.comap (algebraMap K L) =
      base.valuation.valuationSubring := by
  ext a
  simp [Valuation.mem_valuationSubring_iff,
    _root_.Valuation.HasExtension.val_map_le_one_iff
      (vR := base.valuation) (vA := target.valuation)]

/-- Any valuation extending the base valuation has valuation subring pulling
back to the base valuation subring. -/
theorem comap_valuationSubring_eq_base_of_hasExtension
    {Gamma' : Type y} [LinearOrderedCommGroupWithZero Gamma']
    (v' : _root_.Valuation L Gamma') [base.valuation.HasExtension v'] :
    v'.valuationSubring.comap (algebraMap K L) =
      base.valuation.valuationSubring := by
  ext a
  simp [Valuation.mem_valuationSubring_iff,
    _root_.Valuation.HasExtension.val_map_le_one_iff
      (vR := base.valuation) (vA := v')]

end Pullback

section Comparison

variable (target : CompleteDVF.{w, x} L)

/-- Equality of valuation subrings implies valuation equivalence. -/
theorem valuation_isEquiv_of_valuationSubring_eq
    {Gamma' : Type y} [LinearOrderedCommGroupWithZero Gamma']
    (v' : _root_.Valuation L Gamma')
    (hsub : target.valuation.valuationSubring = v'.valuationSubring) :
    target.valuation.IsEquiv v' :=
  (_root_.Valuation.isEquiv_iff_valuationSubring target.valuation v').2 hsub

/-- Equivalent valuations have the same valuation subring. -/
theorem valuationSubring_eq_of_valuation_isEquiv
    {Gamma' : Type y} [LinearOrderedCommGroupWithZero Gamma']
    {v' : _root_.Valuation L Gamma'}
    (h : target.valuation.IsEquiv v') :
    target.valuation.valuationSubring = v'.valuationSubring :=
  (_root_.Valuation.isEquiv_iff_valuationSubring target.valuation v').1 h

/-- Valuation equivalence is exactly equality of valuation subrings. -/
theorem valuation_isEquiv_iff_valuationSubring_eq
    {Gamma' : Type y} [LinearOrderedCommGroupWithZero Gamma']
    (v' : _root_.Valuation L Gamma') :
    target.valuation.IsEquiv v' ↔
      target.valuation.valuationSubring = v'.valuationSubring :=
  _root_.Valuation.isEquiv_iff_valuationSubring target.valuation v'

/-- Equality of valuation subrings is pointwise equality of membership. -/
theorem valuationSubring_eq_iff_mem_valuationSubring
    {Gamma' : Type y} [LinearOrderedCommGroupWithZero Gamma']
    (v' : _root_.Valuation L Gamma') :
    target.valuation.valuationSubring = v'.valuationSubring ↔
      ∀ z : L, z ∈ target.valuation.valuationSubring ↔
        z ∈ v'.valuationSubring := by
  constructor
  · intro h z
    rw [h]
  · exact fun h => SetLike.ext h

/-- Valuation equivalence can be checked pointwise on valuation-ring
membership. -/
theorem valuation_isEquiv_iff_mem_valuationSubring
    {Gamma' : Type y} [LinearOrderedCommGroupWithZero Gamma']
    (v' : _root_.Valuation L Gamma') :
    target.valuation.IsEquiv v' ↔
      ∀ z : L, z ∈ target.valuation.valuationSubring ↔
        z ∈ v'.valuationSubring := by
  rw [valuation_isEquiv_iff_valuationSubring_eq target v',
    valuationSubring_eq_iff_mem_valuationSubring target v']

/-- A pointwise valuation-ring membership criterion gives valuation
equivalence. -/
theorem valuation_isEquiv_of_mem_valuationSubring_iff
    {Gamma' : Type y} [LinearOrderedCommGroupWithZero Gamma']
    (v' : _root_.Valuation L Gamma')
    (hmem : ∀ z : L,
      z ∈ target.valuation.valuationSubring ↔ z ∈ v'.valuationSubring) :
    target.valuation.IsEquiv v' :=
  valuation_isEquiv_of_valuationSubring_eq target v' (SetLike.ext hmem)

end Comparison
end ValuedExtension
end DiscreteValuationField
end
end ValuationTheory
