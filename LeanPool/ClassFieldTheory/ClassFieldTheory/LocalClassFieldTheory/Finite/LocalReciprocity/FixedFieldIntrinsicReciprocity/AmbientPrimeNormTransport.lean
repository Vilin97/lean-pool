/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import Mathlib.FieldTheory.Galois.Basic
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.EmbeddedFrobeniusTransport
/-!
# Valuation-one units and abstract prime norm-residue transport

This module transports valuation-one units and norm classes through
compatible field equivalences, and evaluates abstract fixed-field
norm-residue symbols on transported prime norms.
-/

noncomputable section

namespace LocalClassFieldTheory

open LocalFieldTheory RamificationTheory CyclicCohomology KummerTheory
open ClassFormation
open scoped ValuativeRel

/-- A valuation-subring-preserving ring equivalence carries some unit of
valuation one to a unit of valuation one. -/
theorem exists_valuationOne_unit_of_ringEquiv
    (L M : Type)
    [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Field M] [ValuativeRel M] [TopologicalSpace M]
    [IsNonarchimedeanLocalField M]
    (phi : L ≃+* M)
    (hmem : ∀ x : L,
      x ∈ (ValuativeRel.valuation L).valuationSubring ↔
        phi x ∈ (ValuativeRel.valuation M).valuationSubring) :
    ∃ p : Lˣ,
      IsNonarchimedeanLocalField.valuationMap L
          (Additive.ofMul p) = 1 ∧
        IsNonarchimedeanLocalField.valuationMap M
          (Additive.ofMul
            (Units.mapEquiv phi.toMulEquiv p)) = 1 := by
  let r : 𝒪[L] ≃+* 𝒪[M] := {
    toFun := fun x =>
      ⟨phi (x : L), (hmem (x : L)).1 x.property⟩
    invFun := fun y =>
      ⟨phi.symm (y : M), (hmem (phi.symm (y : M))).2 (by
        rw [phi.apply_symm_apply]
        exact y.property)⟩
    left_inv := fun x => by
      ext
      simp
    right_inv := fun y => by
      ext
      simp
    map_mul' := fun x y => by
      ext
      simp
    map_add' := fun x y => by
      ext
      simp }
  let piOL : 𝒪[L] :=
    chosenIntegerRingUniformizer L
  have hpiOL : Irreducible piOL :=
    chosenIntegerRingUniformizer_irreducible L
  let piOM : 𝒪[M] := r piOL
  have hpiOM : Irreducible piOM :=
    (MulEquiv.irreducible_iff r.toMulEquiv).2 hpiOL
  let uL : Lˣ :=
    integerRingUniformizerFieldUnit L
  let uM : Mˣ :=
    Units.mapEquiv phi.toMulEquiv uL
  let pL : Lˣ := uL⁻¹
  let pM : Mˣ :=
    Units.mapEquiv phi.toMulEquiv pL
  have huL :
      (uL : L) = ((piOL : 𝒪[L]) : L) := rfl
  have huM :
      (uM : M) = ((piOM : 𝒪[M]) : M) := rfl
  have hpM : pM = uM⁻¹ := by
    simp [pM, pL, uM]
  have hpLvalue :
      IsNonarchimedeanLocalField.valuationMap L
        (Additive.ofMul pL) = 1 := by
    exact
      v_integerRingIrreducibleFieldUnit_inv
        L piOL hpiOL uL huL
  have hpMvalue :
      IsNonarchimedeanLocalField.valuationMap M
        (Additive.ofMul pM) = 1 := by
    rw [hpM]
    exact
      v_integerRingIrreducibleFieldUnit_inv
        M piOM hpiOM uM huM
  exact ⟨pL, hpLvalue, hpMvalue⟩

/-- A chosen valuation-one unit whose image under a valuation-compatible
ring equivalence also has valuation one. -/
noncomputable def chosenValuationOneUnitOfRingEquiv
    (L M : Type)
    [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Field M] [ValuativeRel M] [TopologicalSpace M]
    [IsNonarchimedeanLocalField M]
    (phi : L ≃+* M)
    (hmem : ∀ x : L,
      x ∈ (ValuativeRel.valuation L).valuationSubring ↔
        phi x ∈ (ValuativeRel.valuation M).valuationSubring) :
    Lˣ :=
  Classical.choose
    (exists_valuationOne_unit_of_ringEquiv L M phi hmem)

/-- The chosen transported unit has valuation one in its source field. -/
theorem chosenValuationOneUnitOfRingEquiv_source
    (L M : Type)
    [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Field M] [ValuativeRel M] [TopologicalSpace M]
    [IsNonarchimedeanLocalField M]
    (phi : L ≃+* M)
    (hmem : ∀ x : L,
      x ∈ (ValuativeRel.valuation L).valuationSubring ↔
        phi x ∈ (ValuativeRel.valuation M).valuationSubring) :
    IsNonarchimedeanLocalField.valuationMap L
        (Additive.ofMul
          (chosenValuationOneUnitOfRingEquiv L M phi hmem)) = 1 :=
  (Classical.choose_spec
    (exists_valuationOne_unit_of_ringEquiv L M phi hmem)).1

/-- The image of the chosen transported unit has valuation one in the
target field. -/
theorem chosenValuationOneUnitOfRingEquiv_target
    (L M : Type)
    [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Field M] [ValuativeRel M] [TopologicalSpace M]
    [IsNonarchimedeanLocalField M]
    (phi : L ≃+* M)
    (hmem : ∀ x : L,
      x ∈ (ValuativeRel.valuation L).valuationSubring ↔
        phi x ∈ (ValuativeRel.valuation M).valuationSubring) :
    IsNonarchimedeanLocalField.valuationMap M
        (Additive.ofMul
          (Units.mapEquiv phi.toMulEquiv
            (chosenValuationOneUnitOfRingEquiv L M phi hmem))) = 1 :=
  (Classical.choose_spec
    (exists_valuationOne_unit_of_ringEquiv L M phi hmem)).2

/-- Compatible ring equivalences between finite extensions preserve
valuation-subring membership when their separable-closure transport preserves
the local valuation subrings. -/
theorem valuationSubring_mem_iff_of_separableClosureRingEquiv
    (F K L M : Type)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [Algebra F L]
    [FiniteDimensional F L] [Algebra.IsSeparable F L]
    [Valuation.HasExtension
      (ValuativeRel.valuation F) (ValuativeRel.valuation L)]
    [Field M] [ValuativeRel M] [Algebra K M]
    [FiniteDimensional K M] [Algebra.IsSeparable K M]
    [Valuation.HasExtension
      (ValuativeRel.valuation K) (ValuativeRel.valuation M)]
    (jL : L →ₐ[F] SeparableClosure F)
    (jM : M →ₐ[K] SeparableClosure K)
    (psi : SeparableClosure F ≃+* SeparableClosure K)
    (hpsi :
      localSeparableValuationSubring F =
        (localSeparableValuationSubring K).comap psi.toRingHom)
    (phi : L ≃+* M)
    (hphi : ∀ x : L, jM (phi x) = psi (jL x))
    (x : L) :
    x ∈ (ValuativeRel.valuation L).valuationSubring ↔
      phi x ∈ (ValuativeRel.valuation M).valuationSubring := by
  have hsourceRing :
      (localSeparableValuationSubring F).comap jL.toRingHom =
        (ValuativeRel.valuation L).valuationSubring :=
    localSeparableValuationSubring_comap_embedding F L jL
  have htargetRing :
      (localSeparableValuationSubring K).comap jM.toRingHom =
        (ValuativeRel.valuation M).valuationSubring :=
    localSeparableValuationSubring_comap_embedding K M jM
  rw [← hsourceRing, ← htargetRing]
  change
    jL x ∈ localSeparableValuationSubring F ↔
      jM (phi x) ∈ localSeparableValuationSubring K
  rw [hphi x, hpsi]
  rfl

/-- Field norms on units commute with compatible ring equivalences of the
base and extension fields. -/
theorem normUnits_mapEquiv
    (F E F₀ E₀ : Type)
    [Field F] [Field E] [Field F₀] [Field E₀]
    [Algebra F E] [Algebra F₀ E₀]
    (phiF : F ≃+* F₀) (phiE : E ≃+* E₀)
    (hcomm :
      RingHom.comp (algebraMap F₀ E₀) phiF.toRingHom =
        RingHom.comp phiE.toRingHom (algebraMap F E))
    (y : Eˣ) :
    normUnits F₀ E₀ (Units.mapEquiv phiE.toMulEquiv y) =
      Units.mapEquiv phiF.toMulEquiv (normUnits F E y) := by
  apply Units.ext
  change
    Algebra.norm F₀ (phiE (y : E)) =
      phiF (Algebra.norm F (y : E))
  have hnorm :=
    Algebra.norm_eq_of_equiv_equiv
      phiF phiE hcomm (y : E)
  apply phiF.symm.injective
  rw [phiF.symm_apply_apply]
  exact hnorm.symm

/-- Compatible ring equivalences preserve equality of unit norm classes. -/
theorem normClass_mapEquiv
    (F E F₀ E₀ : Type)
    [Field F] [Field E] [Field F₀] [Field E₀]
    [Algebra F E] [Algebra F₀ E₀]
    (phiF : F ≃+* F₀) (phiE : E ≃+* E₀)
    (hcomm :
      RingHom.comp (algebraMap F₀ E₀) phiF.toRingHom =
        RingHom.comp phiE.toRingHom (algebraMap F E))
    (a x : Fˣ)
    (h : normClass F E a = normClass F E x) :
    normClass F₀ E₀ (Units.mapEquiv phiF.toMulEquiv a) =
      normClass F₀ E₀
        (Units.mapEquiv phiF.toMulEquiv x) := by
  rw [normClass_eq_iff_exists_norm_div] at h ⊢
  rcases h with ⟨y, hy⟩
  refine ⟨Units.mapEquiv phiE.toMulEquiv y, ?_⟩
  have hnorm :=
    normUnits_mapEquiv F E F₀ E₀ phiF phiE hcomm y
  rw [← map_div, hy]
  exact hnorm.symm

/-- A unit of valuation one in an abstract fixed field determines a prime
element for the ambient local henselian valuation datum. -/
theorem
    localHenselianValuation_isPrimeElement_abstractFixedField
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (H : FiniteAbstractField
      Gal(SeparableClosure K/K)) :
    let L :=
      abstractFixedField K (SeparableClosure K) H.field
    letI : FiniteDimensional K L :=
      abstractFixedField_finiteDimensional
        K (SeparableClosure K) H.field H.finite
    letI : NontriviallyNormedField L :=
      finiteExtensionSpectralNormedField K L
    letI : ValuativeRel L :=
      finiteExtensionSpectralValuativeRel K L
    letI : IsNonarchimedeanLocalField L :=
      finiteExtensionSpectralIsNonarchimedeanLocalField K L
    ∀ p : Lˣ,
      IsNonarchimedeanLocalField.valuationMap L
          (Additive.ofMul p) = 1 →
        (localHenselianValuation K).IsPrimeElement H
          (abstractFixedFieldUnitsEquivGaloisFixed
            K (SeparableClosure K) H.field
              (Additive.ofMul p)) := by
  dsimp only
  intro p hp
  change (localHenselianValuation K).valuationAt H
      (abstractFixedFieldUnitsEquivGaloisFixed K (SeparableClosure K) H.field
        (Additive.ofMul p)) =
    (localHenselianValuation K).oneValue
  apply Subtype.ext
  change
    ((((localHenselianValuation K).valuationAt H
      (abstractFixedFieldUnitsEquivGaloisFixed
        K (SeparableClosure K) H.field (Additive.ofMul p)) :
      (localHenselianValuation K).valueGroup) : ZHat)) = 1
  rw [localHenselianValuation_valuationAt_abstractFixedField K H p]
  rw [hp]
  simp

/-- Under the canonical fixed-field unit identifications, the abstract
relative norm from an intrinsic fixed field is the ordinary field norm on
units. -/
theorem
    relativeNorm_intrinsicAbstractBase_abstractFixedFieldUnit
    (F : Type) [Field F]
    (S : ClosedSubgroup Gal(SeparableClosure F/F))
    (hSB : S.toSubgroup ≤ (intrinsicAbstractBase F).toSubgroup)
    [Finite
      ((intrinsicAbstractBase F).toSubgroup ⧸
        extensionSubgroup (intrinsicAbstractBase F) S hSB)]
    [FiniteDimensional F
      (abstractFixedField F (SeparableClosure F) S)]
    (p : (abstractFixedField F (SeparableClosure F) S)ˣ) :
    relativeNorm (intrinsicAbsoluteUnits F)
        (intrinsicAbstractBase F) S hSB
        (abstractFixedFieldUnitsEquivGaloisFixed
          F (SeparableClosure F) S (Additive.ofMul p)) =
      baseUnitsEquivGaloisAmbientFixed F (SeparableClosure F)
        (Additive.ofMul
          (normUnits F
            (abstractFixedField F (SeparableClosure F) S) p)) := by
  let L :=
    abstractFixedField F (SeparableClosure F) S
  let S' :=
    closedFixingSubgroup F (SeparableClosure F) L
  let hS'B : S'.toSubgroup ≤
      (intrinsicAbstractBase F).toSubgroup :=
    fixingSubgroupLeBase F (SeparableClosure F) L
  have hS'S : S' = S := by
    exact closedFixingSubgroup_abstractFixedField_eq
      F (SeparableClosure F) S
  let pi' : ambientFixedAddSubgroup
      (intrinsicAbsoluteUnits F) S' :=
    intermediateFieldUnitsEquivGaloisFixed
      F (SeparableClosure F) L (Additive.ofMul p)
  let pi : ambientFixedAddSubgroup
      (intrinsicAbsoluteUnits F) S :=
    abstractFixedFieldUnitsEquivGaloisFixed
      F (SeparableClosure F) S (Additive.ofMul p)
  let _hS'Finite : Finite
      ((intrinsicAbstractBase F).toSubgroup ⧸
        extensionSubgroup
          (intrinsicAbstractBase F) S' hS'B) :=
    inferInstance
  have hpiCoe : pi'.1 = pi.1 := by
    rfl
  have htransportCoe :=
    relativeNorm_coe_eq_of_closedSubgroup_eq
      (intrinsicAbsoluteUnits F)
      (intrinsicAbstractBase F) (intrinsicAbstractBase F)
      S' S hS'B hSB rfl hS'S pi' pi hpiCoe
  have htransport :
      relativeNorm (intrinsicAbsoluteUnits F)
          (intrinsicAbstractBase F) S' hS'B pi' =
        relativeNorm (intrinsicAbsoluteUnits F)
          (intrinsicAbstractBase F) S hSB pi := by
    apply Subtype.ext
    exact htransportCoe
  have hnorm :=
    relativeNorm_intermediateFieldUnit_of_isSeparable
      F (SeparableClosure F) L p
  change
    relativeNorm (intrinsicAbsoluteUnits F)
        (intrinsicAbstractBase F) S' hS'B pi' =
      baseUnitsEquivGaloisAmbientFixed F (SeparableClosure F)
        (Additive.ofMul (normUnits F L p)) at hnorm
  exact htransport.symm.trans hnorm

/-- Translating an abstract relative fixed-field unit through the fixed-field
unit equivalences sends its abstract relative norm to its ordinary field norm. -/
theorem
    relativeNorm_preimage_abstractRelativeFixedFieldUnit
    (K : Type) [Field K]
    (H L : ClosedSubgroup Gal(SeparableClosure K/K))
    (hLH : L.toSubgroup ≤ H.toSubgroup)
    [Finite
      (H.toSubgroup ⧸ extensionSubgroup H L hLH)]
    [Finite
      ((baseField
        Gal(SeparableClosure K/K)).toSubgroup ⧸
        extensionSubgroup
          (baseField Gal(SeparableClosure K / K))
          H (le_baseField H))]
    (p : (abstractRelativeFixedField
      K (SeparableClosure K) hLH)ˣ)
    (x : (abstractFixedField K (SeparableClosure K) H)ˣ)
    (hnorm :
      normUnits
          (abstractFixedField K (SeparableClosure K) H)
          (abstractRelativeFixedField K (SeparableClosure K) hLH)
          p =
        x) :
    Additive.toMul
        ((abstractFixedFieldUnitsEquivGaloisFixed
          K (SeparableClosure K) H).symm
          (relativeNorm
            (galoisAmbientUnitsRep K (SeparableClosure K))
            H L hLH
            (abstractRelativeFixedFieldUnitsEquivGaloisFixed
              K (SeparableClosure K) H L hLH
                (Additive.ofMul p)))) =
      x := by
  have hrelative :
      relativeNorm
          (galoisAmbientUnitsRep K (SeparableClosure K))
          H L hLH
          (abstractRelativeFixedFieldUnitsEquivGaloisFixed
            K (SeparableClosure K) H L hLH
              (Additive.ofMul p)) =
        abstractFixedFieldUnitsEquivGaloisFixed
          K (SeparableClosure K) H
            (Additive.ofMul x) := by
    rw [relativeNorm_abstractFixedFieldUnit_eq_normUnits]
    rw [hnorm]
  apply Additive.ofMul.injective
  change
    (abstractFixedFieldUnitsEquivGaloisFixed
      K (SeparableClosure K) H).symm
        (relativeNorm
          (galoisAmbientUnitsRep K (SeparableClosure K))
          H L hLH
          (abstractRelativeFixedFieldUnitsEquivGaloisFixed
            K (SeparableClosure K) H L hLH
              (Additive.ofMul p))) =
      Additive.ofMul x
  rw [hrelative,
    (abstractFixedFieldUnitsEquivGaloisFixed
      K (SeparableClosure K) H).symm_apply_apply]

/-- Evaluates the abstract fixed-field norm-residue symbol on the norm of a
prime element as the abelianized restriction of its Frobenius element. -/
theorem
    abstractFixedFieldNormResidueSymbol_eq_of_primeNorm
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (H : FiniteAbstractField
      Gal(SeparableClosure K / K))
    (J : ClosedSubgroup
      Gal(SeparableClosure K / K))
    (hJH : J.toSubgroup ≤ H.field.toSubgroup)
    [hJnormal :
      (extensionSubgroup H.field J hJH).Normal]
    [hJfinite : Finite
      (H.field.toSubgroup ⧸
        extensionSubgroup H.field J hJH)]
    (sigma :
      (localResidueDatum K).FrobeniusElements
        (H.toFiniteResidueAbstractField (localResidueDatum K))
        J hJH) :
    let S :=
      (localResidueDatum K).frobeniusFixedField
        (H.toFiniteResidueAbstractField (localResidueDatum K))
        J hJH sigma
    let hSH :=
      (localResidueDatum K).frobeniusFixedField_le
        (H.toFiniteResidueAbstractField (localResidueDatum K))
        J hJH sigma
    let hSabsolute :=
      (localResidueDatum K).frobeniusFixedField_absoluteFinite
        H J hJH sigma
    ∀ (p : (abstractRelativeFixedField
        K (SeparableClosure K) hSH)ˣ)
      (x : (abstractFixedField
        K (SeparableClosure K) H.field)ˣ),
      (localHenselianValuation K).IsPrimeElement
          ⟨S, hSabsolute⟩
          (abstractRelativeFixedFieldUnitsEquivGaloisFixed
            K (SeparableClosure K) H.field S hSH
              (Additive.ofMul p)) →
      normUnits
          (abstractFixedField K (SeparableClosure K) H.field)
          (abstractRelativeFixedField K (SeparableClosure K) hSH)
          p =
        x →
      abstractFixedFieldNormResidueSymbol
          K (SeparableClosure K)
          (localResidueDatum K)
          (localHenselianValuation K)
          (separableClosureUnits_isClassFormation K)
          H.field J hJH (Additive.ofMul x) =
        Additive.ofMul
          ((abstractExtensionQuotientEquivGaloisGroup
            K (SeparableClosure K) H.field J hJH hJnormal
            ).abelianizationCongr
            (Abelianization.of
              ((localResidueDatum K).frobeniusRestriction
                (H.toFiniteResidueAbstractField (localResidueDatum K))
                J hJH sigma))) := by
  dsimp only
  intro p x hprime hnorm
  let hHabsolute : Finite
      ((baseField
        Gal(SeparableClosure K / K)).toSubgroup ⧸
        extensionSubgroup
          (baseField Gal(SeparableClosure K / K))
          H.field (le_baseField H.field)) :=
    H.finite
  let S :=
    (localResidueDatum K).frobeniusFixedField
      (H.toFiniteResidueAbstractField (localResidueDatum K))
      J hJH sigma
  let hSH :=
    (localResidueDatum K).frobeniusFixedField_le
      (H.toFiniteResidueAbstractField (localResidueDatum K))
      J hJH sigma
  let hSabsolute :=
    (localResidueDatum K).frobeniusFixedField_absoluteFinite
      H J hJH sigma
  let hSfinite : Finite
      (H.field.toSubgroup ⧸
        extensionSubgroup H.field S hSH) :=
    (localResidueDatum K).frobeniusFixedField_finite
      (H.toFiniteResidueAbstractField (localResidueDatum K))
      J hJH sigma
  let SigmaS : FiniteAbstractField
      Gal(SeparableClosure K / K) :=
    ⟨S, hSabsolute⟩
  let pi : ambientFixedAddSubgroup
      (galoisAmbientUnitsRep K (SeparableClosure K)) S :=
    abstractRelativeFixedFieldUnitsEquivGaloisFixed
      K (SeparableClosure K) H.field S hSH
        (Additive.ofMul p)
  let qAmbient :=
    (localResidueDatum K).frobeniusRestriction
      (H.toFiniteResidueAbstractField (localResidueDatum K))
      J hJH sigma
  let qH :=
    abstractExtensionQuotientEquivGaloisGroup
      K (SeparableClosure K) H.field J hJH hJnormal
  have hx :
      Additive.toMul
          ((abstractFixedFieldUnitsEquivGaloisFixed
            K (SeparableClosure K) H.field).symm
            (relativeNorm
              (galoisAmbientUnitsRep K (SeparableClosure K))
              H.field S hSH pi)) =
        x := by
    exact
      relativeNorm_preimage_abstractRelativeFixedFieldUnit
        K H.field S hSH p x hnorm
  have hsymbol :=
    abstractFixedFieldNormResidueSymbol_apply_primeNorm
      K (SeparableClosure K)
      (localResidueDatum K)
      (localHenselianValuation K)
      (separableClosureUnits_isClassFormation K)
      H.field J hJH qAmbient sigma rfl pi hprime
  change
    abstractFixedFieldNormResidueSymbol
        K (SeparableClosure K)
        (localResidueDatum K)
        (localHenselianValuation K)
        (separableClosureUnits_isClassFormation K)
        H.field J hJH
        (Additive.ofMul
          (Additive.toMul
            ((abstractFixedFieldUnitsEquivGaloisFixed
              K (SeparableClosure K) H.field).symm
              (relativeNorm
                (galoisAmbientUnitsRep K (SeparableClosure K))
                H.field S hSH pi)))) =
      Additive.ofMul
        (qH.abelianizationCongr
          (Abelianization.of qAmbient)) at hsymbol
  rw [hx] at hsymbol
  exact hsymbol

/-- Transporting a valuation-one unit and its norm through compatible ring
equivalences evaluates the ambient fixed-field norm-residue symbol at the
associated Frobenius restriction. -/
theorem
    abstractFixedFieldNormResidueSymbol_eq_of_transportedValuationOneUnit
    (K F L : Type)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field F] [Field L] [Algebra F L] [FiniteDimensional F L]
    [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    (H : FiniteAbstractField
      Gal(SeparableClosure K / K))
    (J : ClosedSubgroup
      Gal(SeparableClosure K / K))
    (hJH : J.toSubgroup ≤ H.field.toSubgroup)
    [hJnormal :
      (extensionSubgroup H.field J hJH).Normal]
    [hJfinite : Finite
      (H.field.toSubgroup ⧸
        extensionSubgroup H.field J hJH)]
    (sigma :
      (localResidueDatum K).FrobeniusElements
        (H.toFiniteResidueAbstractField (localResidueDatum K))
        J hJH) :
    let S :=
      (localResidueDatum K).frobeniusFixedField
        (H.toFiniteResidueAbstractField (localResidueDatum K))
        J hJH sigma
    let hSH :=
      (localResidueDatum K).frobeniusFixedField_le
        (H.toFiniteResidueAbstractField (localResidueDatum K))
        J hJH sigma
    let hSabsolute :=
      (localResidueDatum K).frobeniusFixedField_absoluteFinite
        H J hJH sigma
    let LH :=
      abstractRelativeFixedField K (SeparableClosure K) hSH
    let F₀ :=
      abstractFixedField K (SeparableClosure K) H.field
    ∀ [_hLHNorm : NontriviallyNormedField LH]
      [_hLHVal : ValuativeRel LH]
      [_hLHLocal : IsNonarchimedeanLocalField LH]
      [_hF₀LHFinite : FiniteDimensional F₀ LH]
      (phiF : F ≃+* F₀) (phi : L ≃+* LH)
      (_hcomm :
        RingHom.comp (algebraMap F₀ LH) phiF.toRingHom =
          RingHom.comp phi.toRingHom (algebraMap F L))
      (hmem : ∀ y : L,
        y ∈ (ValuativeRel.valuation L).valuationSubring ↔
          phi y ∈ (ValuativeRel.valuation LH).valuationSubring)
      (_hprime :
        (localHenselianValuation K).IsPrimeElement
          ⟨S, hSabsolute⟩
          (abstractRelativeFixedFieldUnitsEquivGaloisFixed
            K (SeparableClosure K) H.field S hSH
              (Additive.ofMul
                (Units.mapEquiv phi.toMulEquiv
                  (chosenValuationOneUnitOfRingEquiv
                    L LH phi hmem))))),
      abstractFixedFieldNormResidueSymbol
          K (SeparableClosure K)
          (localResidueDatum K)
          (localHenselianValuation K)
          (separableClosureUnits_isClassFormation K)
          H.field J hJH
          (Additive.ofMul
            (Units.mapEquiv phiF.toMulEquiv
              (normUnits F L
                (chosenValuationOneUnitOfRingEquiv
                  L LH phi hmem)))) =
        Additive.ofMul
          ((abstractExtensionQuotientEquivGaloisGroup
            K (SeparableClosure K) H.field J hJH hJnormal
            ).abelianizationCongr
            (Abelianization.of
              ((localResidueDatum K).frobeniusRestriction
                (H.toFiniteResidueAbstractField (localResidueDatum K))
                J hJH sigma))) := by
  dsimp only
  intro _hLHNorm _hLHVal _hLHLocal _hF₀LHFinite
    phiF phi hcomm hmem hprime
  let S :=
    (localResidueDatum K).frobeniusFixedField
      (H.toFiniteResidueAbstractField (localResidueDatum K))
      J hJH sigma
  let hSH :=
    (localResidueDatum K).frobeniusFixedField_le
      (H.toFiniteResidueAbstractField (localResidueDatum K))
      J hJH sigma
  let hSabsolute :=
    (localResidueDatum K).frobeniusFixedField_absoluteFinite
      H J hJH sigma
  let LH :=
    abstractRelativeFixedField K (SeparableClosure K) hSH
  let F₀ :=
    abstractFixedField K (SeparableClosure K) H.field
  let pF :=
    chosenValuationOneUnitOfRingEquiv L
      (abstractRelativeFixedField K (SeparableClosure K)
        ((localResidueDatum K).frobeniusFixedField_le
          (H.toFiniteResidueAbstractField (localResidueDatum K))
          J hJH sigma))
      phi hmem
  let pH :=
    Units.mapEquiv phi.toMulEquiv pF
  let SigmaH : FiniteAbstractField
      Gal(SeparableClosure K / K) :=
    ⟨(localResidueDatum K).frobeniusFixedField
        (H.toFiniteResidueAbstractField (localResidueDatum K))
        J hJH sigma,
      (localResidueDatum K).frobeniusFixedField_absoluteFinite
        H J hJH sigma⟩
  let piH :=
    abstractRelativeFixedFieldUnitsEquivGaloisFixed
      K (SeparableClosure K) H.field SigmaH.field
        ((localResidueDatum K).frobeniusFixedField_le
          (H.toFiniteResidueAbstractField (localResidueDatum K))
          J hJH sigma)
        (Additive.ofMul pH)
  let xPrime0 :=
    Units.mapEquiv phiF.toMulEquiv (normUnits F L pF)
  have hphiNorm :
      normUnits
          (abstractFixedField K (SeparableClosure K) H.field)
          (abstractRelativeFixedField K (SeparableClosure K)
            ((localResidueDatum K).frobeniusFixedField_le
              (H.toFiniteResidueAbstractField (localResidueDatum K))
              J hJH sigma))
          pH =
        xPrime0 := by
    exact
      normUnits_mapEquiv F L
        (abstractFixedField K (SeparableClosure K) H.field)
        (abstractRelativeFixedField K (SeparableClosure K)
          ((localResidueDatum K).frobeniusFixedField_le
            (H.toFiniteResidueAbstractField (localResidueDatum K))
            J hJH sigma))
        phiF phi hcomm pF
  exact
    abstractFixedFieldNormResidueSymbol_eq_of_primeNorm
      K H J hJH sigma pH xPrime0 hprime hphiNorm

end LocalClassFieldTheory
