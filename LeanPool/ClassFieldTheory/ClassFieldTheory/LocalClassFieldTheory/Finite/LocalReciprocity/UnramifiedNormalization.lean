/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import Mathlib.GroupTheory.Abelianization.Defs
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.SeparableClosureEmbedding
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ConcreteReciprocityPrimeNorm
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.IntrinsicAbsoluteData
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.NormResidue
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.UnramifiedComparison
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.TopologicalReciprocity
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.UnramifiedReciprocity
import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.UnramifiedFrobenius
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteIntegralClosure
/-!
# Canonical unramified normalization

The canonical local norm-residue symbol is identified with the field-facing
unramified Artin map. An element of normalized valuation one maps to arithmetic
Frobenius, both algebraically and in the topological abelianization.
-/

noncomputable section

namespace LocalClassFieldTheory

open scoped IsMulCommutative ValuativeRel
open LocalFieldTheory RamificationTheory CyclicCohomology KummerTheory
open ClassFormation

private abbrev G (K : Type) [Field K] :=
  intrinsicAbsoluteGalois K

private abbrev A (K : Type) [Field K] : Rep ℤ (G K) :=
  intrinsicAbsoluteUnits K

private abbrev B (K : Type) [Field K] : ClosedSubgroup (G K) :=
  intrinsicAbstractBase K

private def extensionQuotientEquivOfEq
    {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    {K L K' L' : ClosedSubgroup Γ}
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hL'K' : L'.toSubgroup ≤ K'.toSubgroup)
    (hK : K = K') (hL : L = L') :
    (K.toSubgroup ⧸ extensionSubgroup K L hLK) ≃
      (K'.toSubgroup ⧸ extensionSubgroup K' L' hL'K') := by
  subst K'
  subst L'
  have hp : hLK = hL'K' := Subsingleton.elim _ _
  subst hL'K'
  exact Equiv.refl _

section BasePrime

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

private theorem localHenselianValuation_valuationAt_baseUnit
    (x : Kˣ) :
    (((localHenselianValuation K).valuationAt (intrinsicFiniteAbstractBase K)
      (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)
        (Additive.ofMul x)) :
        (localHenselianValuation K).valueGroup) : ZHat) =
      Int.castRingHom ZHat
        (LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K
          (Additive.ofMul x)) := by
  let : Finite ((baseField (G K)).toSubgroup ⧸
      extensionSubgroup (baseField (G K)) (B K) (le_baseField (B K))) :=
    (intrinsicFiniteAbstractBase K).finite
  have h :=
    (localHenselianValuation K).residueDegree_nsmul_dividedAt
      (intrinsicFiniteAbstractBase K)
      (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)
        (Additive.ofMul x))
  rw [intrinsicFiniteAbstractBase_residueDegree_eq_one K, one_nsmul] at h
  rw [(localHenselianValuation K).valuationAt_coe, h]
  change localBaseValuation K
      (normToBase (A K) (B K)
        (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)
          (Additive.ofMul x))) =
    Int.castRingHom ZHat
      (LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K
        (Additive.ofMul x))
  let a : ambientFixedAddSubgroup (A K) (baseField (G K)) :=
    baseFieldUnitsEquiv K (Additive.ofMul x)
  have ha :
      baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)
          (Additive.ofMul x) =
        fixedFieldInclusion (A K) (baseField (G K)) (B K)
          (le_baseField (B K)) a := by
    apply Subtype.ext
    rfl
  rw [ha]
  let E : DegreeData.FiniteAbstractExtension (G K) := {
    field := B K
    base := baseField (G K)
    below := le_baseField (B K)
    finiteQuotient := inferInstance }
  change localBaseValuation K
      (relativeNorm (A K) (baseField (G K)) (B K)
        (le_baseField (B K))
        (fixedFieldInclusion (A K) (baseField (G K)) (B K)
          (le_baseField (B K)) a)) = _
  rw [relativeNorm_fixedFieldInclusion (A K) E]
  have hdegree :
      (E.degree : ℕ) = 1 := by
    rw [← E.relIndex_eq_degree]
    change (B K).toSubgroup.relIndex (baseField (G K)).toSubgroup = 1
    rw [show B K = baseField (G K) from
      closedFixingSubgroup_bot_eq_baseField K (SeparableClosure K)]
    exact Subgroup.relIndex_self (H := (baseField (G K)).toSubgroup)
  rw [hdegree, one_nsmul]
  exact localBaseValuation_baseFieldUnitsEquiv K (Additive.ofMul x)

/-- The concrete base-field unit represented by the canonical prime element
of the local henselian valuation. -/
noncomputable def localAbstractPrimeFieldUnit : Kˣ :=
  Additive.toMul
    ((baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).symm
      ((localHenselianValuation K).chosenPrimeElement
        (intrinsicFiniteAbstractBase K)))

/-- The canonical abstract prime has normalized valuation one modulo every
positive integer after transport to the actual local field. -/
theorem valuationMap_localAbstractPrimeFieldUnit_mod
    (n : ℕ) (hn : 0 < n) :
    (LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K
        (Additive.ofMul (localAbstractPrimeFieldUnit K)) : ZMod n) = 1 := by
  let v := localHenselianValuation K
  let pi : ambientFixedAddSubgroup (A K) (B K) :=
    v.chosenPrimeElement (intrinsicFiniteAbstractBase K)
  have htransport :
      baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)
          (Additive.ofMul (localAbstractPrimeFieldUnit K)) =
        pi := by
    change
      baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)
          ((baseUnitsEquivGaloisAmbientFixed K
            (SeparableClosure K)).symm pi) = pi
    exact
      (baseUnitsEquivGaloisAmbientFixed K
        (SeparableClosure K)).apply_symm_apply pi
  have hvalue :=
    localHenselianValuation_valuationAt_baseUnit K
      (localAbstractPrimeFieldUnit K)
  rw [htransport, v.valuationAt_chosenPrimeElement] at hvalue
  have hvalue := hvalue.symm
  change Int.castRingHom ZHat
      (LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K
        (Additive.ofMul (localAbstractPrimeFieldUnit K))) = 1 at hvalue
  have hred := congrArg (zHatReduction n hn) hvalue
  simpa only [zHatReduction_int, zHatReduction_one] using hred

end BasePrime

section UnramifiedPrimeClass

variable (K L : Type)
  [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [UniformSpace L] [IsUniformAddGroup L]
  [IsNonarchimedeanLocalField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  [Valuation.HasExtension (ValuativeRel.valuation K)
    (ValuativeRel.valuation L)]

private noncomputable instance normalizationIntegerRingIsIntegralClosure :
    IsIntegralClosure 𝒪[L] 𝒪[K] L :=
  localCompleteDVF_integerRing_isIntegralClosure K L

variable
  [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]

omit [IsUniformAddGroup L] in
/-- In the actual unramified norm quotient, the canonical abstract prime and
the chosen inverse DVR uniformizer define the same normalized generator. -/
theorem normClass_localAbstractPrimeFieldUnit_eq_uniformizer :
    normClass K L (localAbstractPrimeFieldUnit K) =
      normClass K L
        (inverseIntegerRingUniformizerFieldUnit K) := by
  apply
    (normQuotientUnramifiedValuationEquivZModOfIsIntegralClosure K L).injective
  rw [normQuotientUnramifiedValuationEquivZModOfIsIntegralClosure_mk,
    normQuotientUnramifiedValuationEquivZModOfIsIntegralClosure_mk,
    valuationModDegreeMulHom_apply,
    valuationModDegreeMulHom_apply,
    valuationMap_localAbstractPrimeFieldUnit_mod K
      (Module.finrank K L) (Module.finrank_pos),
    LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap_apply,
    v_inverseIntegerRingUniformizerFieldUnit]
  simp

/-! ## Canonical norm-residue normalization -/

omit [IsUniformAddGroup L] in
/-- The canonical norm-residue symbol sends the transported abstract prime to
the arithmetic Frobenius class. -/
theorem localArtinMonoidHom_localAbstractPrimeFieldUnit :
    localArtinMonoidHom K L (localAbstractPrimeFieldUnit K) =
      Abelianization.of
        (arithmeticFrobeniusOfUnramifiedValuation K L) := by
  let i := AlgebraicNumberTheory.separableEmbeddingIntoSeparableClosure K L
  let D := localResidueDatum K
  let v := localHenselianValuation K
  let hcf := separableClosureUnits_isClassFormation K
  let E := finiteGaloisAbstractExtensionOfEmbedding K L i
  let Kbase := intrinsicFiniteAbstractBase K
  let KR := Kbase.toFiniteResidueAbstractField D
  let hEfinite : Finite ((B K).toSubgroup ⧸
      extensionSubgroup (B K) E.field E.below) :=
    E.finite
  let hKbaseEfinite : Finite (Kbase.field.toSubgroup ⧸
      extensionSubgroup Kbase.field E.field E.below) := by
    exact Finite.of_equiv
      ((B K).toSubgroup ⧸
        extensionSubgroup (B K) E.field E.below)
      (extensionQuotientEquivOfEq
        (K := B K) (L := E.field)
        (K' := Kbase.field) (L' := E.field)
        E.below E.below rfl rfl)
  let hKREfinite : Finite (KR.field.toSubgroup ⧸
      extensionSubgroup KR.field E.field E.below) := by
    exact Finite.of_equiv
      ((B K).toSubgroup ⧸
        extensionSubgroup (B K) E.field E.below)
      (extensionQuotientEquivOfEq
        (K := B K) (L := E.field)
        (K' := KR.field) (L' := E.field)
        E.below E.below rfl rfl)
  let sigma := D.chosenUnramifiedFrobeniusLift KR E.field E.below
  let q := D.unramifiedFrobenius KR E.field E.below
  have hUnramified : E.IsUnramified D := by
    simpa only [D, E, B] using
      finiteGaloisAbstractExtensionOfEmbedding_isUnramified K L i
  let S := D.frobeniusFixedField KR E.field E.below sigma
  let hSB := D.frobeniusFixedField_le
    KR E.field E.below sigma
  let hSBfinite :
      Finite ((B K).toSubgroup ⧸
        extensionSubgroup (B K) S hSB) :=
    D.frobeniusFixedField_finite
      KR E.field E.below sigma
  let hSabsoluteFinite :
      Finite ((baseField (G K)).toSubgroup ⧸
        extensionSubgroup (baseField (G K)) S (le_baseField S)) :=
    D.frobeniusFixedField_absoluteFinite
      Kbase E.field E.below sigma
  let Sfinite : FiniteAbstractField (G K) := ⟨S, hSabsoluteFinite⟩
  let pi : ambientFixedAddSubgroup (A K) S :=
    fixedFieldInclusion (A K) (B K) S hSB
      (v.chosenPrimeElement Kbase)
  have hpi : v.IsPrimeElement Sfinite pi := by
    simpa only [Kbase, KR, sigma, S, hSB, Sfinite, pi] using
      v.unramifiedFrobenius_includedPrime_isPrime
        Kbase E.field E.below hUnramified
  have hnorm :
      relativeNorm (A K) (B K) S hSB pi =
        v.chosenPrimeElement Kbase := by
    simpa only [Kbase, KR, sigma, S, hSB, pi] using
      v.unramifiedFrobenius_primeNorm
        Kbase E.field E.below hUnramified
  let e := baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)
  let xNorm : Kˣ :=
    Additive.toMul
      (e.symm (relativeNorm (A K) (B K) S hSB pi))
  have hxNorm :
      e (Additive.ofMul xNorm) =
        relativeNorm (A K) (B K) S hSB pi := by
    exact e.apply_symm_apply _
  have hsymbol :=
    concreteNormResidueSymbolOfEmbedding_apply_primeNorm
      K L i D v hcf q sigma (by rfl) pi hpi xNorm hxNorm
  dsimp only [xNorm] at hsymbol
  have hx :
      Additive.toMul
          (e.symm (relativeNorm (A K) (B K) S hSB pi)) =
        localAbstractPrimeFieldUnit K := by
    rw [hnorm]
    rfl
  change
    concreteNormResidueSymbolOfEmbedding K L i D v hcf
        (Additive.toMul
          (e.symm (relativeNorm (A K) (B K) S hSB pi))) =
      Abelianization.of
        (finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L i q)
    at hsymbol
  rw [hx, ← localArtinMonoidHom_eq_of_embedding K L i] at hsymbol
  have hq :
      finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L i q =
        arithmeticFrobeniusOfUnramifiedValuation K L := by
    rw [←
      finiteGaloisAbstractUnramifiedFrobenius_eq_arithmeticFrobenius
        K L i]
    rfl
  rw [hq] at hsymbol
  exact hsymbol

/-! ## Equality with the field-facing unramified reciprocity map -/

/-- On an unramified extension, the inverse of the canonical reciprocity
isomorphism is exactly the field-facing Frobenius-normalized isomorphism. -/
theorem abelianizationEquivNormQuotient_symm_eq_unramifiedLocalReciprocityIso :
    (abelianizationEquivNormQuotient K L).symm =
      unramifiedLocalReciprocityIso K L := by
  let p : NormQuotient K L :=
    normClass K L (localAbstractPrimeFieldUnit K)
  let e :=
    normQuotientUnramifiedValuationEquivZModOfIsIntegralClosure K L
  have hep :
      e p =
        Multiplicative.ofAdd
          (1 : ZMod (Module.finrank K L)) := by
    change e
      (normClass K L (localAbstractPrimeFieldUnit K)) = _
    rw [normClass_localAbstractPrimeFieldUnit_eq_uniformizer
      K L]
    rw [normQuotientUnramifiedValuationEquivZModOfIsIntegralClosure_mk,
      valuationModDegreeMulHom_apply,
      LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap_apply,
      v_inverseIntegerRingUniformizerFieldUnit]
    simp
  have hpowers (z : NormQuotient K L) :
      ∃ m : ℤ, p ^ m = z := by
    obtain ⟨m, hm⟩ := ZMod.intCast_surjective (e z).toAdd
    refine ⟨m, ?_⟩
    apply e.injective
    rw [map_zpow, hep]
    rw [← ofAdd_zsmul]
    apply Multiplicative.ext
    simpa [zsmul_eq_mul] using hm
  have hcanonical :
      (abelianizationEquivNormQuotient K L).symm p =
        Abelianization.of
          (arithmeticFrobeniusOfUnramifiedValuation K L) := by
    change localArtinMonoidHom K L (localAbstractPrimeFieldUnit K) = _
    exact localArtinMonoidHom_localAbstractPrimeFieldUnit K L
  have hactual :
      unramifiedLocalReciprocityIso K L p =
        Abelianization.of
          (arithmeticFrobeniusOfUnramifiedValuation K L) := by
    change unramifiedLocalReciprocityIso K L
      (normClass K L (localAbstractPrimeFieldUnit K)) =
        _
    rw [normClass_localAbstractPrimeFieldUnit_eq_uniformizer
      K L]
    exact
      unramifiedLocalReciprocityIso_inverseIntegerRingUniformizerFieldUnit
        K L
  apply MulEquiv.ext
  intro z
  obtain ⟨m, rfl⟩ := hpowers z
  rw [map_zpow, map_zpow, hcanonical, hactual]

/-- The canonical local norm-residue symbol is the field-facing unramified
Artin map. -/
theorem localArtinMonoidHom_eq_unramifiedLocalArtinMap :
    localArtinMonoidHom K L =
      unramifiedLocalArtinMap K L := by
  apply MonoidHom.ext
  intro x
  change
    (abelianizationEquivNormQuotient K L).symm (normClass K L x) =
      unramifiedLocalReciprocityIso K L
        (normClass K L x)
  rw [abelianizationEquivNormQuotient_symm_eq_unramifiedLocalReciprocityIso K L]

/-- Frobenius normalization on the chosen inverse prime element. -/
@[simp]
theorem localArtinMonoidHom_inverseIntegerRingUniformizerFieldUnit :
    localArtinMonoidHom K L
        (inverseIntegerRingUniformizerFieldUnit K) =
      Abelianization.of
        (arithmeticFrobeniusOfUnramifiedValuation K L) := by
  rw [localArtinMonoidHom_eq_unramifiedLocalArtinMap K L]
  change
    unramifiedLocalReciprocityIso K L
        (normClass K L
          (inverseIntegerRingUniformizerFieldUnit K)) =
      Abelianization.of
        (arithmeticFrobeniusOfUnramifiedValuation K L)
  exact
    unramifiedLocalReciprocityIso_inverseIntegerRingUniformizerFieldUnit
      K L

/-- Full unramified Artin formula for the canonical local norm-residue symbol. -/
theorem localArtinMonoidHom_eq_frobenius_zpow (x : Kˣ) :
    localArtinMonoidHom K L x =
      (Abelianization.of
        (arithmeticFrobeniusOfUnramifiedValuation K L)) ^
          LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K
            (Additive.ofMul x) := by
  rw [localArtinMonoidHom_eq_unramifiedLocalArtinMap K L]
  exact unramifiedLocalArtinMap_eq_frobenius_zpow K L x

/-! ## Continuous Frobenius normalization -/

/-- The continuous local Artin map sends every field unit to the topological
class of arithmetic Frobenius raised to its normalized valuation. -/
theorem localArtinMap_eq_frobenius_zpow (x : Kˣ) :
    localArtinMap K L x =
      (topologicalAbelianizationFiniteEquiv K L
        (Abelianization.of
          (arithmeticFrobeniusOfUnramifiedValuation K L))) ^
            LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K
              (Additive.ofMul x) := by
  apply (topologicalAbelianizationFiniteEquiv K L).symm.injective
  rw [map_zpow,
    (topologicalAbelianizationFiniteEquiv K L).symm_apply_apply]
  change
    (((topologicalAbelianizationFiniteEquiv K L).symm.toMonoidHom.comp
      (localArtinMap K L).toMonoidHom) x) =
        (Abelianization.of
          (arithmeticFrobeniusOfUnramifiedValuation K L)) ^
            LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K
              (Additive.ofMul x)
  rw [localArtinMap_toMonoidHom,
    localArtinMonoidHom_eq_frobenius_zpow]

omit [IsUniformAddGroup L] in
/-- The transported canonical abstract prime maps to arithmetic Frobenius in
the topological abelianization. -/
@[simp]
theorem localArtinMap_localAbstractPrimeFieldUnit :
    localArtinMap K L (localAbstractPrimeFieldUnit K) =
      topologicalAbelianizationFiniteEquiv K L
        (Abelianization.of
          (arithmeticFrobeniusOfUnramifiedValuation K L)) := by
  apply (topologicalAbelianizationFiniteEquiv K L).symm.injective
  rw [(topologicalAbelianizationFiniteEquiv K L).symm_apply_apply]
  change
    (((topologicalAbelianizationFiniteEquiv K L).symm.toMonoidHom.comp
      (localArtinMap K L).toMonoidHom) (localAbstractPrimeFieldUnit K)) =
        Abelianization.of
          (arithmeticFrobeniusOfUnramifiedValuation K L)
  rw [localArtinMap_toMonoidHom]
  exact localArtinMonoidHom_localAbstractPrimeFieldUnit K L

/-- A chosen inverse DVR uniformizer maps to arithmetic Frobenius. -/
@[simp]
theorem localArtinMap_uniformizer :
    localArtinMap K L (inverseIntegerRingUniformizerFieldUnit K) =
      topologicalAbelianizationFiniteEquiv K L
        (Abelianization.of
          (arithmeticFrobeniusOfUnramifiedValuation K L)) := by
  rw [localArtinMap_eq_frobenius_zpow,
    LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap_apply,
    v_inverseIntegerRingUniformizerFieldUnit, zpow_one]

/-- Elements of normalized valuation zero lie in the kernel of the
unramified local Artin map. -/
theorem localArtinMap_eq_one_of_valuationMap_eq_zero
    (x : Kˣ)
    (hx : LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K
      (Additive.ofMul x) = 0) :
    localArtinMap K L x = 1 := by
  rw [localArtinMap_eq_frobenius_zpow, hx, zpow_zero]

/-- Every valuation-ring unit has trivial unramified Artin symbol. -/
@[simp]
theorem localArtinMap_units_unramified (u : 𝒪[K]ˣ) :
    localArtinMap K L (LocalFieldTheory.IsNonarchimedeanLocalField.integerUnitsToFieldUnits K u)
      = 1 := by
  apply localArtinMap_eq_one_of_valuationMap_eq_zero K L
  rw [LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap_apply,
    LocalFieldTheory.IsNonarchimedeanLocalField.v_integerUnitsToFieldUnits]

end UnramifiedPrimeClass

section AbelianUnramifiedPrimeClass

variable (K L : Type)
  [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [UniformSpace L] [IsUniformAddGroup L]
  [IsNonarchimedeanLocalField L]
  [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L]
  [Valuation.HasExtension (ValuativeRel.valuation K)
    (ValuativeRel.valuation L)]
  [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]

/-- The canonical local Artin map for an abelian unramified extension sends
each field unit to actual arithmetic Frobenius raised to its normalized valuation. -/
theorem abelianLocalArtinMonoidHom_eq_frobenius_zpow (x : Kˣ) :
    abelianLocalArtinMonoidHom K L x =
      (arithmeticFrobeniusOfUnramifiedValuation K L) ^
        LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K
          (Additive.ofMul x) := by
  simp only [abelianLocalArtinMonoidHom, MonoidHom.coe_comp,
    Function.comp_apply]
  rw [localArtinMonoidHom_eq_frobenius_zpow K L x, map_zpow]
  exact
    congrArg
      (fun σ : Gal(L / K) =>
        σ ^ LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K
          (Additive.ofMul x))
      ((Abelianization.equivOfComm (H := Gal(L / K))).symm_apply_apply
        (arithmeticFrobeniusOfUnramifiedValuation K L))

end AbelianUnramifiedPrimeClass

end LocalClassFieldTheory

namespace ClassFieldTheory

open scoped ValuativeRel

/-- The canonical Artin map of an abelian unramified local extension is
arithmetic Frobenius raised to the normalized valuation. -/
theorem finiteAbelianLocalArtinMap_eq_frobenius_zpow
    (K L : Type)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [UniformSpace L] [IsUniformAddGroup L]
    [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K)
      (ValuativeRel.valuation L)]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (x : Kˣ) :
    LocalClassFieldTheory.abelianLocalArtinMap K L x =
      (LocalFieldTheory.arithmeticFrobeniusOfUnramifiedValuation K L) ^
        LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K
          (Additive.ofMul x) := by
  calc
    LocalClassFieldTheory.abelianLocalArtinMap K L x =
        LocalClassFieldTheory.abelianLocalArtinMonoidHom K L x :=
      DFunLike.congr_fun
        (LocalClassFieldTheory.abelianLocalArtinMap_toMonoidHom K L) x
    _ = _ :=
      LocalClassFieldTheory.abelianLocalArtinMonoidHom_eq_frobenius_zpow K L x

/-- Every element of normalized valuation one maps to arithmetic Frobenius;
there is no further choice of an Artin map at this finite level. -/
theorem finiteAbelianLocalArtinMap_uniformizer
    (K L : Type)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [UniformSpace L] [IsUniformAddGroup L]
    [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K)
      (ValuativeRel.valuation L)]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (π : Kˣ)
    (hπ : LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K
      (Additive.ofMul π) = 1) :
    LocalClassFieldTheory.abelianLocalArtinMap K L π =
      LocalFieldTheory.arithmeticFrobeniusOfUnramifiedValuation K L := by
  rw [finiteAbelianLocalArtinMap_eq_frobenius_zpow K L π, hπ, zpow_one]

/-- At an inverse uniformizer, the normalized local Artin automorphism acts
on the residue field by the arithmetic `q`-power Frobenius. This states the
normalization through the reduction of integral elements, without exposing
the implementation's chosen residue-field automorphism in the conclusion. -/
theorem finiteAbelianLocalArtinMap_inverseUniformizer_residue_pow
    (K L : Type)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [UniformSpace L] [IsUniformAddGroup L]
    [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K)
      (ValuativeRel.valuation L)]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (π : Kˣ)
    (hπ : LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K
      (Additive.ofMul π) = 1)
    (x : 𝒪[L]) :
    ∃ z : 𝒪[L],
      (z : L) = (LocalClassFieldTheory.abelianLocalArtinMap K L π) (x : L) ∧
        IsLocalRing.residue 𝒪[L] z =
          (IsLocalRing.residue 𝒪[L] x) ^ Nat.card 𝓀[K] := by
  let σ : Gal(L / K) := LocalClassFieldTheory.abelianLocalArtinMap K L π
  let z : 𝒪[L] :=
    LocalFieldTheory.galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ x
  refine ⟨z, ?_, ?_⟩
  · exact
      LocalFieldTheory.galoisGroupIntegerRingEquivOfIsIntegralClosure_apply
        K L σ x
  · have hres :=
      (LocalFieldTheory.galoisGroupResidueFieldEquivOfIsIntegralClosure_residue
        K L σ x).symm
    change
      IsLocalRing.residue 𝒪[L] z =
        LocalFieldTheory.galoisGroupResidueAlgEquivOfIsIntegralClosure K L σ
          (IsLocalRing.residue 𝒪[L] x) at hres
    rw [show σ =
      LocalFieldTheory.arithmeticFrobeniusOfUnramifiedValuation K L from
        finiteAbelianLocalArtinMap_uniformizer K L π hπ] at hres
    exact hres.trans
      (LocalFieldTheory.galoisGroupResidueAlgEquivOfIsIntegralClosure_arithmeticFrobenius_apply
        K L (IsLocalRing.residue 𝒪[L] x))

end ClassFieldTheory
