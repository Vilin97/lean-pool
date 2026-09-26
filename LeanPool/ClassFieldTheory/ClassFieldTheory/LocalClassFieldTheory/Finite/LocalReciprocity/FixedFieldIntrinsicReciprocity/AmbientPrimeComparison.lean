/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.GroupTheory.Abelianization.Defs
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.AmbientPrimeWitnessComparison
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.NormResidue
/-!
# Ambient prime comparison

The local Artin map and the ambient embedded norm-residue construction
agree on norm classes and therefore agree pointwise.
-/

@[expose] public section

noncomputable
section

namespace LocalClassFieldTheory

open LocalFieldTheory RamificationTheory CyclicCohomology KummerTheory
open ClassFormation
open scoped ValuativeRel
open scoped IsMulCommutative

/-- Every abelianized Galois element is simultaneously represented by the local
Artin map and by the ambient embedded norm-residue construction. -/
theorem
    exists_localArtin_ambientEmbedded_prime
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
    ∃ x : Fˣ,
      localArtinMonoidHom F E x = z ∧
        ambientEmbeddedNormResidueAbelianElement K F E j e x = z := by
  exact
    ⟨ambientEmbeddedPrimeWitness K F E j e z,
      ambientEmbeddedPrimeWitness_local K F E j e z,
      ambientEmbeddedPrimeWitness_ambient K F E j e z⟩

/-- The ambient embedded norm-residue element depends only on the unit's norm
class modulo norms from `E`. -/
theorem
    ambientEmbeddedNormResidueAbelianElement_eq_of_normClass_eq
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
    (a x : Fˣ)
    (h : normClass F E a = normClass F E x) :
    ambientEmbeddedNormResidueAbelianElement K F E j e a =
      ambientEmbeddedNormResidueAbelianElement K F E j e x := by
  let i :=
    j.comp (IsScalarTower.toAlgHom K F E)
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
    intro y hy
    rcases hy with ⟨z, rfl⟩
    exact ⟨algebraMap F E z, rfl⟩
  let hTargetNormal :
      (extensionSubgroup H₀ J₀ hJH).Normal :=
    ambientEmbeddedExtensionSubgroup_normal K F E j e
  let hTargetFinite : Finite
      (H₀.toSubgroup ⧸ extensionSubgroup H₀ J₀ hJH) :=
    ambientEmbeddedExtensionQuotient_finite K F E j e
  let hHabsolute : Finite
      ((baseField
        Gal(SeparableClosure K/K)).toSubgroup ⧸
        extensionSubgroup
          (baseField Gal(SeparableClosure K/K))
          H₀ (le_baseField H₀)) := by
    exact ambientEmbeddedAbsoluteQuotientFinite K F i
  let F₀ :=
    abstractFixedField K (SeparableClosure K) H₀
  have hfixed :
      F₀ = AlgHom.fieldRange i :=
    InfiniteGalois.fixedField_fixingSubgroup
      (AlgHom.fieldRange i)
  let phiF : F ≃ₐ[K] F₀ :=
    (i.equivFieldRange).trans
      (IntermediateField.equivOfEq hfixed.symm)
  let E₀ :=
    abstractRelativeFixedField K (SeparableClosure K) hJH
  have hfixedE :
      abstractFixedField K (SeparableClosure K) J₀ =
        AlgHom.fieldRange j :=
    InfiniteGalois.fixedField_fixingSubgroup
      (AlgHom.fieldRange j)
  let phiE : E ≃+* E₀ := by
    change
      E ≃+*
        abstractFixedField K (SeparableClosure K) J₀
    exact
      ((j.equivFieldRange).trans
        (IntermediateField.equivOfEq hfixedE.symm)).toRingEquiv
  let q₀ :=
    abstractExtensionQuotientEquivGaloisGroup
      K (SeparableClosure K) H₀ J₀ hJH hTargetNormal
  let qE :=
    ambientEmbeddedExtensionQuotientEquivGaloisGroup
      K F E j e
  let aF0 : F₀ˣ :=
    Units.mapEquiv phiF.toMulEquiv a
  let xF0 : F₀ˣ :=
    Units.mapEquiv phiF.toMulEquiv x
  have hnormClass0 :
      normClass F₀ E₀ aF0 =
        normClass F₀ E₀ xF0 := by
    exact
      normClass_mapEquiv F E F₀ E₀
        phiF.toRingEquiv phiE
        (by
          apply RingHom.ext
          intro y
          rfl)
        a x h
  have hambientSame :
      abstractFixedFieldNormResidueSymbol
          K (SeparableClosure K)
          (localResidueDatum K)
          (localHenselianValuation K)
          (separableClosureUnits_isClassFormation K)
          H₀ J₀ hJH (Additive.ofMul aF0) =
        abstractFixedFieldNormResidueSymbol
          K (SeparableClosure K)
          (localResidueDatum K)
          (localHenselianValuation K)
          (separableClosureUnits_isClassFormation K)
          H₀ J₀ hJH (Additive.ofMul xF0) :=
    abstractFixedFieldNormResidueSymbol_eq_of_normClass_eq
      K (SeparableClosure K)
      (localResidueDatum K)
      (localHenselianValuation K)
      (separableClosureUnits_isClassFormation K)
      H₀ J₀ hJH aF0 xF0 hnormClass0
  change
    qE.abelianizationCongr
        (q₀.abelianizationCongr.symm
          (Additive.toMul
            (abstractFixedFieldNormResidueSymbol
              K (SeparableClosure K)
              (localResidueDatum K)
              (localHenselianValuation K)
              (separableClosureUnits_isClassFormation K)
              H₀ J₀ hJH (Additive.ofMul aF0)))) =
      qE.abelianizationCongr
        (q₀.abelianizationCongr.symm
          (Additive.toMul
            (abstractFixedFieldNormResidueSymbol
              K (SeparableClosure K)
              (localResidueDatum K)
              (localHenselianValuation K)
              (separableClosureUnits_isClassFormation K)
              H₀ J₀ hJH (Additive.ofMul xF0))))
  rw [hambientSame]

/-- For an embedded finite abelian local extension, the abelian local Artin
map agrees pointwise with the ambient norm-residue element transported through
a separable-closure equivalence. -/
theorem
    abelianLocalArtin_eq_ambientEmbeddedNormResidueSymbol_of_equiv
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
    (a : Fˣ) :
    abelianLocalArtinMonoidHom F E a =
      ambientEmbeddedNormResidueElement K F E j e a := by
  obtain ⟨x, hxLocal, hxAmbient⟩ :=
    exists_localArtin_ambientEmbedded_prime K F E j e
      (localArtinMonoidHom F E a)
  let i :=
    j.comp (IsScalarTower.toAlgHom K F E)
  let : Algebra F (SeparableClosure K) :=
    i.toRingHom.toAlgebra
  let jF : E →ₐ[F] SeparableClosure K :=
    { j with commutes' := fun y => rfl }
  let jI : E →ₐ[F] SeparableClosure F :=
    e.symm.toAlgHom.comp jF
  have hnormClass :
      normClass F E a = normClass F E x := by
    apply
      (concreteReciprocityEquivOfEmbedding
        F E jI
        (localResidueDatum F)
        (localHenselianValuation F)
        (separableClosureUnits_isClassFormation F)).symm.injective
    change
      concreteNormResidueSymbolOfEmbedding
          F E jI
          (localResidueDatum F)
          (localHenselianValuation F)
          (separableClosureUnits_isClassFormation F) a =
        concreteNormResidueSymbolOfEmbedding
          F E jI
          (localResidueDatum F)
          (localHenselianValuation F)
          (separableClosureUnits_isClassFormation F) x
    have ha :=
      DFunLike.congr_fun
        (localArtinMonoidHom_eq_of_embedding F E jI) a
    have hx :=
      DFunLike.congr_fun
        (localArtinMonoidHom_eq_of_embedding F E jI) x
    rw [← ha, ← hx]
    exact hxLocal.symm
  have hxNormResidue :=
    ambientEmbeddedNormResidueAbelianElement_eq_of_normClass_eq
      K F E j e a x hnormClass
  change
    (Abelianization.equivOfComm (H := Gal(E/F))).symm
        (localArtinMonoidHom F E a) =
      (Abelianization.equivOfComm (H := Gal(E/F))).symm
        (ambientEmbeddedNormResidueAbelianElement K F E j e a)
  apply congrArg (Abelianization.equivOfComm (H := Gal(E/F))).symm
  calc
    localArtinMonoidHom F E a =
        ambientEmbeddedNormResidueAbelianElement K F E j e x :=
      hxAmbient.symm
    _ = ambientEmbeddedNormResidueAbelianElement K F E j e a :=
      hxNormResidue.symm

end LocalClassFieldTheory
