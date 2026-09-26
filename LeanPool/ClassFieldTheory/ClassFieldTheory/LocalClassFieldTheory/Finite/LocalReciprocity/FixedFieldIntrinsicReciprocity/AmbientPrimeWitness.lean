/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.FieldTheory.Galois.Basic
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.AmbientNormResidue
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.AmbientPrimeNormTransport
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.AmbientPrimeTarget
/-!
# Ambient prime witnesses

This module constructs a valuation-one prime witness for each abelianized Galois element
using the corresponding intrinsic Frobenius lift.
-/

@[expose] public section

noncomputable
section

namespace LocalClassFieldTheory

open LocalFieldTheory RamificationTheory CyclicCohomology KummerTheory
open ClassFormation
open scoped ValuativeRel

/-- A prime-norm unit in the intrinsic base field chosen from a Frobenius
lift of an abelianized Galois element. -/
noncomputable def ambientEmbeddedPrimeWitness
    (K F E : Type)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field E] [Algebra K F] [Algebra F E] [Algebra K E]
    [IsScalarTower K F E]
    [FiniteDimensional K F] [Algebra.IsSeparable K F]
    [Valuation.HasExtension
      (ValuativeRel.valuation K) (ValuativeRel.valuation F)]
    [FiniteDimensional F E] [IsAbelianGalois F E]
    (j : E →ₐ[K] SeparableClosure K)
    (e : ambientEmbeddedSeparableClosureEquiv K F E j)
    (z : Abelianization Gal(E/F)) : Fˣ := by
  let i :=
    j.comp (IsScalarTower.toAlgHom K F E)
  letI : Algebra F (SeparableClosure K) :=
    i.toRingHom.toAlgebra
  let jF : E →ₐ[F] SeparableClosure K :=
    { j with commutes' := fun x => rfl }
  let jI : E →ₐ[F] SeparableClosure F :=
    e.symm.toAlgHom.comp jF
  let EI :=
    finiteGaloisAbstractExtensionOfEmbedding F E jI
  let H₀ :=
    closedFixingSubgroup K (SeparableClosure K)
      (AlgHom.fieldRange i)
  let J₀ :=
    closedFixingSubgroup K (SeparableClosure K)
      (AlgHom.fieldRange j)
  let hJH : J₀.toSubgroup ≤ H₀.toSubgroup := by
    change
      (AlgHom.fieldRange j).fixingSubgroup ≤
        (AlgHom.fieldRange i).fixingSubgroup
    apply (AlgHom.fieldRange i).fixingSubgroup_le
    intro x hx
    rcases hx with ⟨y, rfl⟩
    exact ⟨algebraMap F E y, rfl⟩
  letI hSourceNormal :
      (extensionSubgroup
        (intrinsicAbstractBase F) EI.field EI.below).Normal :=
    EI.normal
  letI hSourceFinite : Finite
      ((intrinsicAbstractBase F).toSubgroup ⧸
        extensionSubgroup
          (intrinsicAbstractBase F) EI.field EI.below) :=
    EI.finite
  letI hTargetNormal :
      (extensionSubgroup H₀ J₀ hJH).Normal :=
    ambientEmbeddedExtensionSubgroup_normal K F E j e
  letI hTargetFinite : Finite
      (H₀.toSubgroup ⧸ extensionSubgroup H₀ J₀ hJH) :=
    ambientEmbeddedExtensionQuotient_finite K F E j e
  letI hHabsolute : Finite
      ((baseField
        Gal(SeparableClosure K/K)).toSubgroup ⧸
        extensionSubgroup
          (baseField Gal(SeparableClosure K/K))
          H₀ (le_baseField H₀)) := by
    exact ambientEmbeddedAbsoluteQuotientFinite K F i
  let H : FiniteAbstractField
      Gal(SeparableClosure K/K) :=
    ⟨H₀, ambientEmbeddedAbsoluteQuotientFinite K F i⟩
  let qF :=
    finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding
      F E jI
  let RF :=
    (intrinsicFiniteAbstractBase F).toFiniteResidueAbstractField
      (localResidueDatum F)
  letI _hRFFinite : Finite
      (RF.field.toSubgroup ⧸
        extensionSubgroup RF.field EI.field EI.below) := by
    change Finite
      ((intrinsicAbstractBase F).toSubgroup ⧸
        extensionSubgroup
          (intrinsicAbstractBase F) EI.field EI.below)
    exact hSourceFinite
  let RH :=
    H.toFiniteResidueAbstractField (localResidueDatum K)
  let zF : Abelianization EI.extensionQuotient :=
    qF.abelianizationCongr.symm z
  let q :=
    Classical.choose (QuotientGroup.mk_surjective zF)
  have hq :=
    Classical.choose_spec (QuotientGroup.mk_surjective zF)
  let sigma :=
    Classical.choose
      ((localResidueDatum F).frobeniusRestriction_surjective
        RF EI.field EI.below q)
  have hsigma :=
    Classical.choose_spec
      ((localResidueDatum F).frobeniusRestriction_surjective
        RF EI.field EI.below q)
  let sigmaH :=
    intrinsicFrobeniusElementToAmbientEmbeddedField
      K F E j e sigma
  let SF :=
    (localResidueDatum F).frobeniusFixedField
      RF EI.field EI.below sigma
  let hSFabsolute :=
    (localResidueDatum F).frobeniusFixedField_absoluteFinite
      (intrinsicFiniteAbstractBase F) EI.field EI.below sigma
  let LF :=
    abstractFixedField F (SeparableClosure F) SF
  let SH :=
    (localResidueDatum K).frobeniusFixedField
      RH J₀ hJH sigmaH
  let hSHH :=
    (localResidueDatum K).frobeniusFixedField_le
      RH J₀ hJH sigmaH
  let hSHabsolute :=
    (localResidueDatum K).frobeniusFixedField_absoluteFinite
      H J₀ hJH sigmaH
  let LH :=
    abstractRelativeFixedField K (SeparableClosure K) hSHH
  let iLH : F →ₐ[K] LH :=
    i.codRestrict (LH.restrictScalars K).toSubalgebra (fun x => by
      change i x ∈ IntermediateField.fixedField SH.toSubgroup
      rw [IntermediateField.mem_fixedField_iff]
      intro rho hrho
      have hrhoH : rho ∈ H₀.toSubgroup :=
        hSHH hrho
      change rho (i x) = i x
      change
        rho ∈ (AlgHom.fieldRange i).fixingSubgroup at hrhoH
      rw [IntermediateField.mem_fixingSubgroup_iff] at hrhoH
      exact hrhoH (i x) ⟨x, rfl⟩)
  let phi : LF ≃+* LH := by
    letI : Algebra F LH := iLH.toRingHom.toAlgebra
    exact
      (intrinsicFrobeniusFixedFieldEquivAmbientEmbeddedField
        K F E j e sigma).toRingEquiv
  have hphi (x : LF) :
      ((phi x : LH) : SeparableClosure K) =
        e (x : SeparableClosure F) := by
    exact
      intrinsicFrobeniusFixedFieldEquivAmbientEmbeddedField_apply_val
        K F E j e sigma x
  letI : FiniteDimensional F LF :=
    abstractFixedField_finiteDimensional
      F (SeparableClosure F) SF hSFabsolute
  letI : NontriviallyNormedField LF :=
    finiteExtensionSpectralNormedField F LF
  letI : ValuativeRel LF :=
    finiteExtensionSpectralValuativeRel F LF
  letI : IsNonarchimedeanLocalField LF :=
    finiteExtensionSpectralIsNonarchimedeanLocalField F LF
  letI : Valuation.HasExtension
      (ValuativeRel.valuation F) (ValuativeRel.valuation LF) :=
    finiteExtensionSpectralValuation_hasExtension F LF
  letI : FiniteDimensional K LH :=
    abstractFixedField_finiteDimensional
      K (SeparableClosure K) SH hSHabsolute
  let iH : LH →ₐ[K] SeparableClosure K :=
    LH.val.restrictScalars K
  letI : Algebra.IsSeparable K LH := by
    let : IsScalarTower K LH (SeparableClosure K) :=
      IsScalarTower.of_algebraMap_eq' (by
        apply RingHom.ext
        intro x
        exact (iH.commutes x).symm)
    exact
      Algebra.isSeparable_tower_bot_of_isSeparable
        K LH (SeparableClosure K)
  letI : NontriviallyNormedField LH :=
    finiteExtensionSpectralNormedField K LH
  letI : ValuativeRel LH :=
    finiteExtensionSpectralValuativeRel K LH
  letI : IsNonarchimedeanLocalField LH :=
    finiteExtensionSpectralIsNonarchimedeanLocalField K LH
  letI : Valuation.HasExtension
      (ValuativeRel.valuation K) (ValuativeRel.valuation LH) :=
    finiteExtensionSpectralValuation_hasExtension K LH
  have hmem (x : LF) :
      x ∈ (ValuativeRel.valuation LF).valuationSubring ↔
        phi x ∈ (ValuativeRel.valuation LH).valuationSubring := by
    exact
      valuationSubring_mem_iff_of_separableClosureRingEquiv
        F K LF LH LF.val iH e.toRingEquiv
        (localSeparableValuationSubring_eq_comap_finiteExtensionEquiv
          K F i e)
        phi hphi
        x
  let pF :=
    chosenValuationOneUnitOfRingEquiv LF LH phi hmem
  exact normUnits F LF pF


end LocalClassFieldTheory
