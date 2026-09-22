/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import Mathlib.GroupTheory.Abelianization.Defs
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.AmbientPrimeComparison
/-!
# Norm--restriction for local Artin maps

This module proves norm--restriction naturality for actual finite abelian local Artin maps.
-/

noncomputable section

namespace LocalClassFieldTheory

open LocalFieldTheory RamificationTheory CyclicCohomology KummerTheory
open ClassFormation
open scoped IsMulCommutative ValuativeRel

/-- A compatible restriction of concrete embedded Galois actions induces the
corresponding restriction map on ambient finite quotient representatives. -/
theorem AmbientEmbeddedFixedFieldPresentation.quotientRestriction
    (K K' L L' : Type)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field K'] [ValuativeRel K'] [TopologicalSpace K']
    [IsNonarchimedeanLocalField K']
    [Field L] [Field L']
    [Algebra K K'] [Algebra K L] [Algebra K L']
    [Algebra K' L'] [Algebra L L']
    [IsScalarTower K K' L']
    [FiniteDimensional K K'] [Algebra.IsSeparable K K']
    [Valuation.HasExtension
      (ValuativeRel.valuation K) (ValuativeRel.valuation K')]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [FiniteDimensional K' L'] [IsAbelianGalois K' L']
    {jLower : L →ₐ[K] SeparableClosure K}
    {jUpper : L' →ₐ[K] SeparableClosure K}
    (lower : AmbientEmbeddedFixedFieldPresentation K K L jLower)
    (upper : AmbientEmbeddedFixedFieldPresentation K K' L' jUpper)
    (hH'H : upper.base.field.toSubgroup ≤ lower.base.field.toSubgroup)
    (hJ'J : upper.extension.field.toSubgroup ≤
      lower.extension.field.toSubgroup)
    [hJnormal :
      (extensionSubgroup lower.base.field lower.extension.field
        lower.extension.below).Normal]
    [_hJfinite : Finite
      (lower.base.field.toSubgroup ⧸
        extensionSubgroup lower.base.field lower.extension.field
          lower.extension.below)]
    [hJ'normal :
      (extensionSubgroup upper.base.field upper.extension.field
        upper.extension.below).Normal]
    [_hJ'finite : Finite
      (upper.base.field.toSubgroup ⧸
        extensionSubgroup upper.base.field upper.extension.field
          upper.extension.below)]
    [_hHabsolute : Finite
      ((baseField Gal(SeparableClosure K/K)).toSubgroup ⧸
        extensionSubgroup
          (baseField Gal(SeparableClosure K / K))
          lower.base.field (le_baseField lower.base.field))]
    [_hH'absolute : Finite
      ((baseField Gal(SeparableClosure K/K)).toSubgroup ⧸
        extensionSubgroup
          (baseField Gal(SeparableClosure K / K))
          upper.base.field (le_baseField upper.base.field))]
    [_hH'finite : Finite
      (lower.base.field.toSubgroup ⧸
        extensionSubgroup lower.base.field upper.base.field hH'H)]
    (restrictActual : Gal(L' / K') →* Gal(L/K))
    (hbase : ∀ x : L,
      jUpper (algebraMap L L' x) = jLower x)
    (hcompat : ∀ (τ : Gal(L' / K')) (x : L),
      jLower (restrictActual τ x) =
        jUpper (τ (algebraMap L L' x)))
    (z : Abelianization
      (upper.base.field.toSubgroup ⧸
        extensionSubgroup upper.base.field upper.extension.field
          upper.extension.below)) :
    restrictActual
        ((Abelianization.equivOfComm (H := Gal(L' / K'))).symm
          ((upper.extension.extensionQuotientMulEquiv.symm.trans
            upper.quotientEquiv).abelianizationCongr z)) =
      (Abelianization.equivOfComm (H := Gal(L / K))).symm
        ((lower.extension.extensionQuotientMulEquiv.symm.trans
          lower.quotientEquiv).abelianizationCongr
          (normResidueNaturalityAbelianizedRestriction
            lower.base.field upper.base.field
            lower.extension.field upper.extension.field
            lower.extension.below upper.extension.below
            hH'H hJ'J z)) := by
  let qLower :=
    lower.extension.extensionQuotientMulEquiv.symm.trans
      lower.quotientEquiv
  let qUpper :=
    upper.extension.extensionQuotientMulEquiv.symm.trans
      upper.quotientEquiv
  obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective z
  obtain ⟨sigma, rfl⟩ := QuotientGroup.mk_surjective q
  change
    restrictActual
        ((Abelianization.equivOfComm (H := Gal(L' / K'))).symm
          (qUpper.abelianizationCongr
            (Abelianization.of (QuotientGroup.mk sigma)))) =
      (Abelianization.equivOfComm (H := Gal(L / K))).symm
        (qLower.abelianizationCongr
          (normResidueNaturalityAbelianizedRestriction
            lower.base.field upper.base.field
            lower.extension.field upper.extension.field
            lower.extension.below upper.extension.below
            hH'H hJ'J (Abelianization.of (QuotientGroup.mk sigma))))
  rw [normResidueNaturalityAbelianizedRestriction_of_mk,
    abelianizationCongr_of, abelianizationCongr_of]
  change
    restrictActual (qUpper (QuotientGroup.mk sigma)) =
      qLower (QuotientGroup.mk (Subgroup.inclusion hH'H sigma))
  have hqUpper_mk :
      qUpper (QuotientGroup.mk sigma) =
        upper.quotientEquiv
          (upper.extension.extensionQuotientMk sigma) := by
    dsimp [qUpper]
    have hmk :
        upper.extension.extensionQuotientMulEquiv.symm
            (QuotientGroup.mk sigma) =
          upper.extension.extensionQuotientMk sigma := by
      exact
        upper.extension.extensionQuotientMulEquiv.symm_apply_eq.mpr
          (upper.extension.extensionQuotientMk_apply sigma).symm
    rw [hmk]
  have hqLower_mk :
      qLower (QuotientGroup.mk (Subgroup.inclusion hH'H sigma)) =
        lower.quotientEquiv
          (lower.extension.extensionQuotientMk
            (Subgroup.inclusion hH'H sigma)) := by
    dsimp [qLower]
    have hmk :
        lower.extension.extensionQuotientMulEquiv.symm
            (QuotientGroup.mk (Subgroup.inclusion hH'H sigma)) =
          lower.extension.extensionQuotientMk
            (Subgroup.inclusion hH'H sigma) := by
      exact
        lower.extension.extensionQuotientMulEquiv.symm_apply_eq.mpr
          (lower.extension.extensionQuotientMk_apply
            (Subgroup.inclusion hH'H sigma)).symm
    rw [hmk]
  apply AlgEquiv.ext
  intro x
  apply jLower.injective
  calc
    jLower
        (restrictActual
          (qUpper (QuotientGroup.mk sigma)) x) =
        jUpper
          ((qUpper (QuotientGroup.mk sigma))
            (algebraMap L L' x)) :=
      hcompat (qUpper (QuotientGroup.mk sigma)) x
    _ = jUpper
          (upper.quotientEquiv
            (upper.extension.extensionQuotientMk sigma)
            (algebraMap L L' x)) := by
      rw [hqUpper_mk]
    _ = sigma.1.1
        (jUpper (algebraMap L L' x)) :=
      upper.quotientEquiv_mk_apply sigma (algebraMap L L' x)
    _ = (Subgroup.inclusion hH'H sigma).1.1
        (jLower x) := by
      rw [hbase x]
      change sigma.1.1 (jLower x) = sigma.1.1 (jLower x)
      rfl
    _ = jLower
        (lower.quotientEquiv
          (lower.extension.extensionQuotientMk
            (Subgroup.inclusion hH'H sigma)) x) :=
      (lower.quotientEquiv_mk_apply
        (Subgroup.inclusion hH'H sigma) x).symm
    _ = jLower
        (qLower (QuotientGroup.mk
          (Subgroup.inclusion hH'H sigma)) x) := by
      rw [hqLower_mk]

/-- The actual abstract fixed-field norm-residue symbols commute with norm and
restriction through the canonical quotient equivalences of the presentations. -/
theorem AmbientEmbeddedFixedFieldPresentation.fixedFieldNormResidueTransport
    (K K' L L' : Type)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field K'] [ValuativeRel K'] [TopologicalSpace K']
    [IsNonarchimedeanLocalField K']
    [Field L] [Field L']
    [Algebra K K'] [Algebra K L] [Algebra K L']
    [Algebra K' L'] [Algebra L L']
    [IsScalarTower K K' L'] [IsScalarTower K L L']
    [FiniteDimensional K K'] [Algebra.IsSeparable K K']
    [Valuation.HasExtension
      (ValuativeRel.valuation K) (ValuativeRel.valuation K')]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [FiniteDimensional K' L'] [IsAbelianGalois K' L']
    {jLower : L →ₐ[K] SeparableClosure K}
    {jUpper : L' →ₐ[K] SeparableClosure K}
    (lower : AmbientEmbeddedFixedFieldPresentation K K L jLower)
    (upper : AmbientEmbeddedFixedFieldPresentation K K' L' jUpper)
    (hH'H : upper.base.field.toSubgroup ≤ lower.base.field.toSubgroup)
    (hJ'J : upper.extension.field.toSubgroup ≤
      lower.extension.field.toSubgroup)
    [hJnormal :
      (extensionSubgroup lower.base.field lower.extension.field
        lower.extension.below).Normal]
    [_hJfinite : Finite
      (lower.base.field.toSubgroup ⧸
        extensionSubgroup lower.base.field lower.extension.field
          lower.extension.below)]
    [hJ'normal :
      (extensionSubgroup upper.base.field upper.extension.field
        upper.extension.below).Normal]
    [_hJ'finite : Finite
      (upper.base.field.toSubgroup ⧸
        extensionSubgroup upper.base.field upper.extension.field
          upper.extension.below)]
    [_hHabsolute : Finite
      ((baseField Gal(SeparableClosure K/K)).toSubgroup ⧸
        extensionSubgroup
          (baseField Gal(SeparableClosure K / K))
          lower.base.field (le_baseField lower.base.field))]
    [_hH'absolute : Finite
      ((baseField Gal(SeparableClosure K/K)).toSubgroup ⧸
        extensionSubgroup
          (baseField Gal(SeparableClosure K / K))
          upper.base.field (le_baseField upper.base.field))]
    [_hH'finite : Finite
      (lower.base.field.toSubgroup ⧸
        extensionSubgroup lower.base.field upper.base.field hH'H)]
    (hbase : ∀ x : L,
      jUpper (algebraMap L L' x) = jLower x)
    (a : K'ˣ) :
    normResidueNaturalityAbelianizedRestriction
        lower.base.field upper.base.field
        lower.extension.field upper.extension.field
        lower.extension.below upper.extension.below
        hH'H hJ'J
        ((upper.extension.extensionQuotientMulEquiv.symm.trans
          upper.fixedFieldQuotientEquiv).abelianizationCongr.symm
          (Additive.toMul
            (abstractFixedFieldNormResidueSymbol
              K (SeparableClosure K)
              (localResidueDatum K)
              (localHenselianValuation K)
              (separableClosureUnits_isClassFormation K)
              upper.base.field upper.extension.field
              upper.extension.below
              (Additive.ofMul
                (Units.mapEquiv upper.baseEquiv.toMulEquiv a))))) =
      (lower.extension.extensionQuotientMulEquiv.symm.trans
        lower.fixedFieldQuotientEquiv).abelianizationCongr.symm
        (Additive.toMul
          (abstractFixedFieldNormResidueSymbol
            K (SeparableClosure K)
            (localResidueDatum K)
            (localHenselianValuation K)
            (separableClosureUnits_isClassFormation K)
            lower.base.field lower.extension.field
            lower.extension.below
            (Additive.ofMul
              (Units.mapEquiv lower.baseEquiv.toMulEquiv
                (normUnits K K' a))))) := by
  let H := lower.base.field
  let H' := upper.base.field
  let J := lower.extension.field
  let J' := upper.extension.field
  let hJH : J.toSubgroup ≤ H.toSubgroup := lower.extension.below
  let hJ'H' : J'.toSubgroup ≤ H'.toSubgroup := upper.extension.below
  let qActualLower :=
    lower.extension.extensionQuotientMulEquiv.symm.trans
      lower.fixedFieldQuotientEquiv
  let qActualUpper :=
    upper.extension.extensionQuotientMulEquiv.symm.trans
      upper.fixedFieldQuotientEquiv
  let FLower :=
    abstractFixedField K (SeparableClosure K) H
  let phiLower : K ≃ₐ[K] FLower :=
    lower.baseEquiv
  let FUpper :=
    abstractFixedField K (SeparableClosure K) H'
  let : Algebra FLower FUpper :=
    RingHom.toAlgebra
      (IntermediateField.inclusion
        (abstractFixedField_le K (SeparableClosure K) hH'H))
  let phiUpper : K' ≃ₐ[K] FUpper :=
    upper.baseEquiv
  have hphiComm :
      RingHom.comp (algebraMap FLower FUpper)
          phiLower.toRingEquiv.toRingHom =
        RingHom.comp phiUpper.toRingEquiv.toRingHom
          (algebraMap K K') := by
    apply RingHom.ext
    intro x
    apply FUpper.val.injective
    change
      ((phiLower x : FLower) : SeparableClosure K) =
        ((phiUpper (algebraMap K K' x) : FUpper) : SeparableClosure K)
    rw [lower.baseEquiv_apply, upper.baseEquiv_apply,
      lower.baseEmbedding_eq, upper.baseEmbedding_eq]
    change
      jLower (algebraMap K L x) =
        jUpper (algebraMap K' L' (algebraMap K K' x))
    calc
      jLower (algebraMap K L x) =
          jUpper (algebraMap L L' (algebraMap K L x)) :=
        (hbase (algebraMap K L x)).symm
      _ = jUpper (algebraMap K' L' (algebraMap K K' x)) := by
        rw [← IsScalarTower.algebraMap_apply K L L',
          ← IsScalarTower.algebraMap_apply K K' L']
  let aUpper : FUpperˣ :=
    Units.mapEquiv phiUpper.toMulEquiv a
  let aLower : FLowerˣ :=
    Units.mapEquiv phiLower.toMulEquiv (normUnits K K' a)
  have hbaseNorm :
      abstractFixedFieldNormUnits
          K (SeparableClosure K) H H' hH'H
          (Additive.ofMul aUpper) =
        Additive.ofMul aLower := by
    exact
      congrArg Additive.toMul
        (normUnits_mapEquiv
          K K' FLower FUpper
          phiLower.toRingEquiv phiUpper.toRingEquiv
          hphiComm a)
  let symbolUpper :=
    abstractFixedFieldNormResidueSymbol
      K (SeparableClosure K)
      (localResidueDatum K)
      (localHenselianValuation K)
      (separableClosureUnits_isClassFormation K)
      H' J' hJ'H'
  let symbolLower :=
    abstractFixedFieldNormResidueSymbol
      K (SeparableClosure K)
      (localResidueDatum K)
      (localHenselianValuation K)
      (separableClosureUnits_isClassFormation K)
      H J hJH
  have hnaturality :=
    DFunLike.congr_fun
      (abstractFixedFieldNormResidueSymbol_norm_restriction
        K (SeparableClosure K)
        (localResidueDatum K)
        (localHenselianValuation K)
        (separableClosureUnits_isClassFormation K)
        H H' J J' hJH hJ'H' hH'H hJ'J)
      (Additive.ofMul aUpper)
  have hrawActual :
      normResidueNaturalityAbelianizedRestriction
          H H' J J' hJH hJ'H' hH'H hJ'J
          (qActualUpper.abelianizationCongr.symm
            (Additive.toMul
              (symbolUpper (Additive.ofMul aUpper)))) =
        qActualLower.abelianizationCongr.symm
          (Additive.toMul
            (symbolLower (Additive.ofMul aLower))) := by
    change
      (abstractFixedFieldAbelianizedRestriction
          K (SeparableClosure K) H H' J J'
          hJH hJ'H' hH'H hJ'J)
          (symbolUpper (Additive.ofMul aUpper)) =
        symbolLower
          (abstractFixedFieldNormUnits
            K (SeparableClosure K) H H' hH'H
            (Additive.ofMul aUpper)) at hnaturality
    rw [hbaseNorm] at hnaturality
    have hmul := congrArg Additive.toMul hnaturality
    change
      qActualLower.abelianizationCongr
          (normResidueNaturalityAbelianizedRestriction
            H H' J J' hJH hJ'H' hH'H hJ'J
            (qActualUpper.abelianizationCongr.symm
              (Additive.toMul
                (symbolUpper (Additive.ofMul aUpper))))) =
        Additive.toMul
          (symbolLower (Additive.ofMul aLower)) at hmul
    exact qActualLower.abelianizationCongr.eq_symm_apply.mpr hmul
  simpa only [H, H', J, J', hJH, hJ'H', qActualLower, qActualUpper,
    aUpper, aLower, symbolUpper, symbolLower] using
    hrawActual

/-- Canonical ambient fixed-field norm-residue values commute with restriction
and norm in an arbitrary finite square of nonarchimedean local fields. -/
theorem ambientEmbeddedNormResidueElement_norm_restriction
    (K K' L L' : Type)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field K'] [ValuativeRel K'] [TopologicalSpace K']
    [IsNonarchimedeanLocalField K']
    [Field L] [Field L']
    [Algebra K K'] [Algebra K L] [Algebra K L']
    [Algebra K' L'] [Algebra L L']
    [IsScalarTower K K' L'] [IsScalarTower K L L']
    [FiniteDimensional K K'] [Algebra.IsSeparable K K']
    [Valuation.HasExtension
      (ValuativeRel.valuation K) (ValuativeRel.valuation K')]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [FiniteDimensional K' L'] [IsAbelianGalois K' L']
    (j : L' →ₐ[K] SeparableClosure K)
    (eLower :
      @AlgEquiv K (SeparableClosure K) (SeparableClosure K)
        _ _ _
        (separableClosure K (AlgebraicClosure K)).algebra
        (((j.comp (IsScalarTower.toAlgHom K L L')).comp
          (IsScalarTower.toAlgHom K K L)).toRingHom.toAlgebra))
    (eUpper :
      letI : Algebra K' (SeparableClosure K) :=
        (j.comp (IsScalarTower.toAlgHom K K' L')).toRingHom.toAlgebra
      SeparableClosure K' ≃ₐ[K'] SeparableClosure K)
    (a : K'ˣ) :
    ((AlgEquiv.restrictNormalHom L).comp
        (AlgEquiv.restrictScalarsHom K))
        (ambientEmbeddedNormResidueElement K K' L' j eUpper a) =
      ambientEmbeddedNormResidueElement K K L
        (j.comp (IsScalarTower.toAlgHom K L L')) eLower
        (normUnits K K' a) := by
  let : FiniteDimensional K L' :=
    FiniteDimensional.trans K K' L'
  let : Algebra.IsSeparable K L' :=
    Algebra.IsSeparable.trans K K' L'
  let iUpper : K' →ₐ[K] SeparableClosure K :=
    j.comp (IsScalarTower.toAlgHom K K' L')
  let jLower : L →ₐ[K] SeparableClosure K :=
    j.comp (IsScalarTower.toAlgHom K L L')
  let iLower : K →ₐ[K] SeparableClosure K :=
    jLower.comp (IsScalarTower.toAlgHom K K L)
  let lower :=
    ambientEmbeddedFixedFieldPresentation K K L jLower eLower
  let upper :=
    ambientEmbeddedFixedFieldPresentation K K' L' j eUpper
  let H := lower.base.field
  let H' := upper.base.field
  let J := lower.extension.field
  let J' := upper.extension.field
  have hRangeHH :
      AlgHom.fieldRange iLower ≤
        AlgHom.fieldRange iUpper := by
    intro x hx
    rcases hx with ⟨y, rfl⟩
    refine ⟨algebraMap K K' y, ?_⟩
    change
      j (algebraMap K' L' (algebraMap K K' y)) =
        j (algebraMap L L' (algebraMap K L y))
    rw [← IsScalarTower.algebraMap_apply K K' L',
      ← IsScalarTower.algebraMap_apply K L L']
  let hH'H : H'.toSubgroup ≤ H.toSubgroup := by
    change upper.base.field.toSubgroup ≤ lower.base.field.toSubgroup
    rw [lower.base_field_eq, upper.base_field_eq,
      lower.baseEmbedding_eq, upper.baseEmbedding_eq]
    change
      (AlgHom.fieldRange iUpper).fixingSubgroup ≤
        (AlgHom.fieldRange iLower).fixingSubgroup
    exact
      (AlgHom.fieldRange iLower).fixingSubgroup_le
        hRangeHH
  have hRangeJJ :
      AlgHom.fieldRange jLower ≤
        AlgHom.fieldRange j := by
    intro x hx
    rcases hx with ⟨y, rfl⟩
    exact ⟨algebraMap L L' y, rfl⟩
  let hJ'J : J'.toSubgroup ≤ J.toSubgroup := by
    change upper.extension.field.toSubgroup ≤ lower.extension.field.toSubgroup
    rw [lower.extension_field_eq, upper.extension_field_eq]
    change
      (AlgHom.fieldRange j).fixingSubgroup ≤
        (AlgHom.fieldRange jLower).fixingSubgroup
    exact
      (AlgHom.fieldRange jLower).fixingSubgroup_le
        hRangeJJ
  let hJH : J.toSubgroup ≤ H.toSubgroup := lower.extension.below
  let hJ'H' : J'.toSubgroup ≤ H'.toSubgroup := upper.extension.below
  let hJnormal :
      (extensionSubgroup H J hJH).Normal :=
    lower.extension.normal
  let hJfinite : Finite
      (H.toSubgroup ⧸ extensionSubgroup H J hJH) :=
    lower.extension.finite
  let hJ'normal :
      (extensionSubgroup H' J' hJ'H').Normal :=
    upper.extension.normal
  let hJ'finite : Finite
      (H'.toSubgroup ⧸ extensionSubgroup H' J' hJ'H') :=
    upper.extension.finite
  let hHabsolute : Finite
      ((baseField
        Gal(SeparableClosure K / K)).toSubgroup ⧸
        extensionSubgroup
          (baseField Gal(SeparableClosure K / K))
          H (le_baseField H)) :=
    lower.base.finite
  let hH'absolute : Finite
      ((baseField
        Gal(SeparableClosure K / K)).toSubgroup ⧸
        extensionSubgroup
          (baseField Gal(SeparableClosure K / K))
          H' (le_baseField H')) :=
    upper.base.finite
  let hH'finite : Finite
      (H.toSubgroup ⧸ extensionSubgroup H H' hH'H) := by
    let inclusion :=
      Subgroup.quotientSubgroupOfEmbeddingOfLE
        H'.toSubgroup (le_baseField H)
    exact Finite.of_injective inclusion inclusion.injective
  let FLower :=
    abstractFixedField K (SeparableClosure K) H
  let phiLower : K ≃ₐ[K] FLower :=
    lower.baseEquiv
  let FUpper :=
    abstractFixedField K (SeparableClosure K) H'
  let phiUpper : K' ≃ₐ[K] FUpper :=
    upper.baseEquiv
  let restrictActual :
      Gal(L' / K') →* Gal(L / K) :=
    (AlgEquiv.restrictNormalHom L).comp
      (AlgEquiv.restrictScalarsHom K)
  have hcompat : ∀ (τ : Gal(L' / K')) (x : L),
      jLower (restrictActual τ x) =
        j (τ (algebraMap L L' x)) := by
    intro τ x
    exact congrArg j
      (AlgEquiv.restrictNormal_commutes
        ((AlgEquiv.restrictScalarsHom K) τ) L x)
  have hbase : ∀ x : L,
      j (algebraMap L L' x) = jLower x := by
    intro x
    rfl
  let aUpper : FUpperˣ :=
    Units.mapEquiv phiUpper.toMulEquiv a
  let aNorm : Kˣ :=
    normUnits K K' a
  let aLower : FLowerˣ :=
    Units.mapEquiv phiLower.toMulEquiv aNorm
  let symbolUpper :=
    abstractFixedFieldNormResidueSymbol
      K (SeparableClosure K)
      (localResidueDatum K)
      (localHenselianValuation K)
      (separableClosureUnits_isClassFormation K)
      H' J' hJ'H'
  let symbolLower :=
    abstractFixedFieldNormResidueSymbol
      K (SeparableClosure K)
      (localResidueDatum K)
      (localHenselianValuation K)
      (separableClosureUnits_isClassFormation K)
      H J hJH
  let upperSymbolValue :=
    Additive.toMul
      (symbolUpper (Additive.ofMul aUpper))
  let lowerSymbolValue :=
    Additive.toMul
      (symbolLower (Additive.ofMul aLower))
  let upperQuotientValue :=
    upper.fixedFieldQuotientEquiv.abelianizationCongr.symm
      upperSymbolValue
  let lowerQuotientValue :=
    lower.fixedFieldQuotientEquiv.abelianizationCongr.symm
      lowerSymbolValue
  have hraw :
      normResidueNaturalityAbelianizedRestriction
          H H' J J' hJH hJ'H' hH'H hJ'J
          ((upper.extension.extensionQuotientMulEquiv.symm.trans
            upper.fixedFieldQuotientEquiv).abelianizationCongr.symm
            upperSymbolValue) =
        (lower.extension.extensionQuotientMulEquiv.symm.trans
          lower.fixedFieldQuotientEquiv).abelianizationCongr.symm
          lowerSymbolValue := by
    simpa only [H, H', J, J', hJH, hJ'H',
      aUpper, aLower, aNorm, symbolUpper, symbolLower,
      upperSymbolValue, lowerSymbolValue] using
      AmbientEmbeddedFixedFieldPresentation.fixedFieldNormResidueTransport
        K K' L L' lower upper hH'H hJ'J
        hbase a
  have htarget
      (z : Abelianization upper.extension.extensionQuotient) :
      restrictActual
          ((Abelianization.equivOfComm (H := Gal(L' / K'))).symm
            (upper.quotientEquiv.abelianizationCongr z)) =
        (Abelianization.equivOfComm (H := Gal(L / K))).symm
          (lower.quotientEquiv.abelianizationCongr
            (lower.extension.extensionQuotientMulEquiv.abelianizationCongr.symm
              (normResidueNaturalityAbelianizedRestriction
                H H' J J' hJH hJ'H' hH'H hJ'J
                (upper.extension.extensionQuotientMulEquiv.abelianizationCongr
                  z)))) := by
    simpa only [← abelianizationCongr_trans,
      ← abelianizationCongr_symm,
      MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply] using
      AmbientEmbeddedFixedFieldPresentation.quotientRestriction
        K K' L L' lower upper hH'H hJ'J restrictActual hbase hcompat
        (upper.extension.extensionQuotientMulEquiv.abelianizationCongr z)
  have hambient :
      lower.extension.extensionQuotientMulEquiv.abelianizationCongr.symm
          (normResidueNaturalityAbelianizedRestriction
            H H' J J' hJH hJ'H' hH'H hJ'J
            (upper.extension.extensionQuotientMulEquiv.abelianizationCongr
              upperQuotientValue)) =
        lowerQuotientValue := by
    refine
      lower.extension.extensionQuotientMulEquiv.abelianizationCongr.symm_apply_eq.mpr ?_
    calc
      normResidueNaturalityAbelianizedRestriction
          H H' J J' hJH hJ'H' hH'H hJ'J
          (upper.extension.extensionQuotientMulEquiv.abelianizationCongr
            upperQuotientValue) =
          normResidueNaturalityAbelianizedRestriction
            H H' J J' hJH hJ'H' hH'H hJ'J
            ((upper.extension.extensionQuotientMulEquiv.symm.trans
              upper.fixedFieldQuotientEquiv).abelianizationCongr.symm
              upperSymbolValue) := by
        simp only [← abelianizationCongr_trans,
          ← abelianizationCongr_symm, MulEquiv.symm_trans_apply,
          MulEquiv.symm_symm, upperQuotientValue]
      _ = (lower.extension.extensionQuotientMulEquiv.symm.trans
            lower.fixedFieldQuotientEquiv).abelianizationCongr.symm
            lowerSymbolValue := hraw
      _ = lower.extension.extensionQuotientMulEquiv.abelianizationCongr
            lowerQuotientValue := by
        simp only [← abelianizationCongr_trans,
          ← abelianizationCongr_symm, MulEquiv.symm_trans_apply,
          MulEquiv.symm_symm, lowerQuotientValue]
  have hupperEval :
      upper.normResidueAbelianElement a =
        upper.quotientEquiv.abelianizationCongr
          upperQuotientValue := by
    exact upper.normResidueAbelianElement_apply a
  have hlowerEval :
      lower.normResidueAbelianElement aNorm =
        lower.quotientEquiv.abelianizationCongr
          lowerQuotientValue := by
    exact lower.normResidueAbelianElement_apply aNorm
  let ambientUpper : Gal(L' / K') :=
    ambientEmbeddedNormResidueElement K K' L' j eUpper a
  let ambientLower : Gal(L / K) :=
    ambientEmbeddedNormResidueElement K K L jLower eLower aNorm
  have htransport :
      restrictActual ambientUpper = ambientLower := by
    dsimp only [ambientUpper, ambientLower,
      ambientEmbeddedNormResidueElement,
      ambientEmbeddedNormResidueAbelianElement]
    change
      restrictActual
          ((Abelianization.equivOfComm (H := Gal(L' / K'))).symm
            (upper.normResidueAbelianElement a)) =
        (Abelianization.equivOfComm (H := Gal(L / K))).symm
          (lower.normResidueAbelianElement aNorm)
    rw [hupperEval, hlowerEval]
    calc
      restrictActual
          ((Abelianization.equivOfComm (H := Gal(L' / K'))).symm
            (upper.quotientEquiv.abelianizationCongr
              upperQuotientValue)) =
        (Abelianization.equivOfComm (H := Gal(L / K))).symm
            (lower.quotientEquiv.abelianizationCongr
              (lower.extension.extensionQuotientMulEquiv.abelianizationCongr.symm
                (normResidueNaturalityAbelianizedRestriction
                  H H' J J' hJH hJ'H' hH'H hJ'J
                  (upper.extension.extensionQuotientMulEquiv.abelianizationCongr
                    upperQuotientValue)))) :=
        htarget upperQuotientValue
      _ = (Abelianization.equivOfComm (H := Gal(L / K))).symm
            (lower.quotientEquiv.abelianizationCongr
              lowerQuotientValue) :=
        congrArg
          (fun z =>
            (Abelianization.equivOfComm (H := Gal(L / K))).symm
              (lower.quotientEquiv.abelianizationCongr z))
          hambient
  change
    restrictActual ambientUpper = ambientLower
  exact htransport

/-- The actual finite abelian local Artin maps satisfy norm--restriction
naturality in an arbitrary finite square of nonarchimedean local fields. -/
theorem abelianLocalArtinMonoidHom_norm_restriction
    (K K' L L' : Type)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field K'] [ValuativeRel K'] [TopologicalSpace K']
    [IsNonarchimedeanLocalField K']
    [Field L] [Field L']
    [Algebra K K'] [Algebra K L] [Algebra K L']
    [Algebra K' L'] [Algebra L L']
    [IsScalarTower K K' L'] [IsScalarTower K L L']
    [FiniteDimensional K K'] [Algebra.IsSeparable K K']
    [Valuation.HasExtension
      (ValuativeRel.valuation K) (ValuativeRel.valuation K')]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [FiniteDimensional K' L'] [IsAbelianGalois K' L'] :
    ((AlgEquiv.restrictNormalHom L).comp
        (AlgEquiv.restrictScalarsHom K)).comp
        (abelianLocalArtinMonoidHom K' L') =
      (abelianLocalArtinMonoidHom K L).comp
        (normUnits K K') := by
  apply MonoidHom.ext
  intro a
  let : FiniteDimensional K L' :=
    FiniteDimensional.trans K K' L'
  let : Algebra.IsSeparable K L' :=
    Algebra.IsSeparable.trans K K' L'
  let j : L' →ₐ[K] SeparableClosure K :=
    IsSepClosed.lift
  let jLower : L →ₐ[K] SeparableClosure K :=
    j.comp (IsScalarTower.toAlgHom K L L')
  let iLower : K →ₐ[K] SeparableClosure K :=
    jLower.comp (IsScalarTower.toAlgHom K K L)
  let eLower :
      @AlgEquiv K (SeparableClosure K) (SeparableClosure K)
        _ _ _
        (separableClosure K (AlgebraicClosure K)).algebra
        iLower.toRingHom.toAlgebra := by
    refine @AlgEquiv.ofRingEquiv
      K (SeparableClosure K) (SeparableClosure K)
      _ _ _
      (separableClosure K (AlgebraicClosure K)).algebra
      iLower.toRingHom.toAlgebra
      (RingEquiv.refl (SeparableClosure K)) ?_
    intro x
    change algebraMap K (SeparableClosure K) x = iLower x
    exact (iLower.commutes x).symm
  let iUpper : K' →ₐ[K] SeparableClosure K :=
    j.comp (IsScalarTower.toAlgHom K K' L')
  let eUpper :
      letI : Algebra K' (SeparableClosure K) :=
        iUpper.toRingHom.toAlgebra
      SeparableClosure K' ≃ₐ[K'] SeparableClosure K := by
    letI : Algebra K' (SeparableClosure K) :=
      iUpper.toRingHom.toAlgebra
    letI : Algebra.IsSeparable K' (SeparableClosure K) :=
      Algebra.isSeparable_tower_top_of_isSeparable
        K K' (SeparableClosure K)
    letI : IsSepClosure K' (SeparableClosure K) :=
      ⟨inferInstance, inferInstance⟩
    exact
      IsSepClosure.equiv K'
        (SeparableClosure K') (SeparableClosure K)
  let restrictActual :
      Gal(L' / K') →* Gal(L / K) :=
    (AlgEquiv.restrictNormalHom L).comp
      (AlgEquiv.restrictScalarsHom K)
  let aNorm : Kˣ :=
    normUnits K K' a
  let ambientUpper : Gal(L' / K') :=
    ambientEmbeddedNormResidueElement K K' L' j eUpper a
  let ambientLower : Gal(L / K) :=
    ambientEmbeddedNormResidueElement K K L jLower eLower aNorm
  have hUpper :
      abelianLocalArtinMonoidHom K' L' a = ambientUpper :=
    abelianLocalArtin_eq_ambientEmbeddedNormResidueSymbol_of_equiv
      K K' L' j eUpper a
  have hLower :
      abelianLocalArtinMonoidHom K L aNorm = ambientLower :=
    abelianLocalArtin_eq_ambientEmbeddedNormResidueSymbol_of_equiv
      K K L jLower eLower aNorm
  have htransport :
      restrictActual ambientUpper = ambientLower := by
    simpa only [restrictActual, ambientUpper, ambientLower, aNorm, jLower] using
      ambientEmbeddedNormResidueElement_norm_restriction
        K K' L L' j eLower eUpper a
  change
    restrictActual (abelianLocalArtinMonoidHom K' L' a) =
      abelianLocalArtinMonoidHom K L aNorm
  calc
    restrictActual (abelianLocalArtinMonoidHom K' L' a) =
        restrictActual ambientUpper := by
      exact congrArg restrictActual hUpper
    _ = ambientLower := htransport
    _ = abelianLocalArtinMonoidHom K L aNorm := hLower.symm

end LocalClassFieldTheory
