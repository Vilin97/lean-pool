/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import Mathlib.FieldTheory.Galois.Basic
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.AmbientPrimeWitness
/-!
# Ambient prime symbol setup

This module identifies the ambient norm-residue symbol of the chosen
prime witness with the Frobenius target transported back to the
original embedded Galois group.
-/

noncomputable section

namespace LocalClassFieldTheory

open LocalFieldTheory RamificationTheory CyclicCohomology KummerTheory
open ClassFormation
open scoped ValuativeRel

/-- The ambient fixed-field norm-residue value of the chosen prime
witness, transported to the original embedded Galois group. -/
noncomputable def ambientEmbeddedPrimeTransportValue
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
    (z : Abelianization Gal(E/F)) :
    Abelianization Gal(E / F) := by
  let i :=
    j.comp (IsScalarTower.toAlgHom K F E)
  letI : Algebra F (SeparableClosure K) :=
    i.toRingHom.toAlgebra
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
  letI hTargetNormal :
      (extensionSubgroup H₀ J₀ hJH).Normal :=
    ambientEmbeddedExtensionSubgroup_normal K F E j e
  letI hTargetFinite : Finite
      (H₀.toSubgroup ⧸ extensionSubgroup H₀ J₀ hJH) :=
    ambientEmbeddedExtensionQuotient_finite K F E j e
  letI hHabsolute : Finite
      ((baseField
        Gal(SeparableClosure K / K)).toSubgroup ⧸
        extensionSubgroup
          (baseField Gal(SeparableClosure K / K))
          H₀ (le_baseField H₀)) := by
    exact ambientEmbeddedAbsoluteQuotientFinite K F i
  let F₀ :=
    abstractFixedField K (SeparableClosure K) H₀
  let hfixed :
      F₀ = AlgHom.fieldRange i :=
    InfiniteGalois.fixedField_fixingSubgroup
      (AlgHom.fieldRange i)
  let phiF : F ≃ₐ[K] F₀ :=
    (i.equivFieldRange).trans
      (IntermediateField.equivOfEq hfixed.symm)
  let q₀ :=
    abstractExtensionQuotientEquivGaloisGroup
      K (SeparableClosure K) H₀ J₀ hJH hTargetNormal
  let qE :=
    ambientEmbeddedExtensionQuotientEquivGaloisGroup
      K F E j e
  exact
    qE.abelianizationCongr
      (q₀.abelianizationCongr.symm
        (Additive.toMul
          (abstractFixedFieldNormResidueSymbol
            K (SeparableClosure K)
            (localResidueDatum K)
            (localHenselianValuation K)
            (separableClosureUnits_isClassFormation K)
            H₀ J₀ hJH
            (Additive.ofMul
              (Units.mapEquiv phiF.toMulEquiv
                (ambientEmbeddedPrimeWitness K F E j e z))))))

/-- The fixed-field norm-residue symbol of the chosen prime witness is
the abelianized restriction of its ambient Frobenius lift. -/
noncomputable def ambientEmbeddedPrimeSymbolProperty
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
    (z : Abelianization Gal(E/F)) : Prop := by
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
  letI _hSourceNormal :
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
        Gal(SeparableClosure K / K)).toSubgroup ⧸
        extensionSubgroup
          (baseField Gal(SeparableClosure K / K))
          H₀ (le_baseField H₀)) := by
    exact ambientEmbeddedAbsoluteQuotientFinite K F i
  let H : FiniteAbstractField
      Gal(SeparableClosure K / K) :=
    ⟨H₀, ambientEmbeddedAbsoluteQuotientFinite K F i⟩
  let F₀ :=
    abstractFixedField K (SeparableClosure K) H₀
  let hfixed :
      F₀ = AlgHom.fieldRange i :=
    InfiniteGalois.fixedField_fixingSubgroup
      (AlgHom.fieldRange i)
  let phiF : F ≃ₐ[K] F₀ :=
    (i.equivFieldRange).trans
      (IntermediateField.equivOfEq hfixed.symm)
  let qF :=
    finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding
      F E jI
  let q₀ :=
    abstractExtensionQuotientEquivGaloisGroup
      K (SeparableClosure K) H₀ J₀ hJH hTargetNormal
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
  let sigma :=
    Classical.choose
      ((localResidueDatum F).frobeniusRestriction_surjective
        RF EI.field EI.below q)
  let sigmaH :=
    intrinsicFrobeniusElementToAmbientEmbeddedField
      K F E j e sigma
  let qAmbient :=
    (localResidueDatum K).frobeniusRestriction
      RH J₀ hJH sigmaH
  exact
    abstractFixedFieldNormResidueSymbol
        K (SeparableClosure K)
        (localResidueDatum K)
        (localHenselianValuation K)
        (separableClosureUnits_isClassFormation K)
        H₀ J₀ hJH
        (Additive.ofMul
          (Units.mapEquiv phiF.toMulEquiv
            (ambientEmbeddedPrimeWitness K F E j e z))) =
      Additive.ofMul
        (q₀.abelianizationCongr
          (Abelianization.of qAmbient))

/-- The explicit fixed-field symbol formula identifies the transported
prime value with its ambient Frobenius target. -/
theorem
    ambientEmbeddedPrimeTransportValue_eq_target_of_symbol
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
    (z : Abelianization Gal(E/F)) :
    let i :=
      j.comp (IsScalarTower.toAlgHom K F E)
    letI : Algebra F (SeparableClosure F) :=
      (separableClosure F (AlgebraicClosure F)).algebra
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
    letI _hSourceNormal :
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
          Gal(SeparableClosure K / K)).toSubgroup ⧸
          extensionSubgroup
            (baseField Gal(SeparableClosure K / K))
            H₀ (le_baseField H₀)) := by
      exact ambientEmbeddedAbsoluteQuotientFinite K F i
    let H : FiniteAbstractField
        Gal(SeparableClosure K / K) :=
      ⟨H₀, ambientEmbeddedAbsoluteQuotientFinite K F i⟩
    let F₀ :=
      abstractFixedField K (SeparableClosure K) H₀
    let hfixed :
        F₀ = AlgHom.fieldRange i :=
      InfiniteGalois.fixedField_fixingSubgroup
        (AlgHom.fieldRange i)
    let phiF : F ≃ₐ[K] F₀ :=
      (i.equivFieldRange).trans
        (IntermediateField.equivOfEq hfixed.symm)
    let qF :=
      finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding
        F E jI
    let q₀ :=
      abstractExtensionQuotientEquivGaloisGroup
        K (SeparableClosure K) H₀ J₀ hJH hTargetNormal
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
    let sigma :=
      Classical.choose
        ((localResidueDatum F).frobeniusRestriction_surjective
          RF EI.field EI.below q)
    let sigmaH :=
      intrinsicFrobeniusElementToAmbientEmbeddedField
        K F E j e sigma
    let qAmbient :=
      (localResidueDatum K).frobeniusRestriction
        RH J₀ hJH sigmaH
    ∀ (_hsymbol :
        abstractFixedFieldNormResidueSymbol
            K (SeparableClosure K)
            (localResidueDatum K)
            (localHenselianValuation K)
            (separableClosureUnits_isClassFormation K)
            H₀ J₀ hJH
            (Additive.ofMul
              (Units.mapEquiv phiF.toMulEquiv
                (ambientEmbeddedPrimeWitness K F E j e z))) =
          Additive.ofMul
            (q₀.abelianizationCongr
              (Abelianization.of qAmbient))),
      ambientEmbeddedPrimeTransportValue K F E j e z =
        ambientEmbeddedPrimeTarget K F E j e z := by
  dsimp only
  intro hsymbol
  let i :=
    j.comp (IsScalarTower.toAlgHom K F E)
  let : Algebra F (SeparableClosure F) :=
    (separableClosure F (AlgebraicClosure F)).algebra
  let : Algebra F (SeparableClosure K) :=
    i.toRingHom.toAlgebra
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
  let hTargetNormal :
      (extensionSubgroup H₀ J₀ hJH).Normal :=
    ambientEmbeddedExtensionSubgroup_normal K F E j e
  exact
    abelianizationCongr_symm_eq_primeTarget
      _ _ _ _ hsymbol

end LocalClassFieldTheory
