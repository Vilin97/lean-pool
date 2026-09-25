/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.TotallyRamifiedCase.FrobeniusNorms
import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.TotallyRamified
/-!
# The fixed source in the totally ramified reciprocity argument

This file converts a finite cyclic extension to the canonical finite Galois
boundary and carries out the source-producing fixed-element calculation.
-/

noncomputable section

namespace ClassFormation

open KummerTheory
open CyclicCohomology

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

/-- If two commuting group elements act compatibly on a coboundary, the
standard corrected combination is fixed by the first element. -/
theorem abstractReciprocity_fixedCombination_of_commute
    {Q : IntegralRepGroupType} [Group Q] (B : Rep ℤ Q)
    (g t : Q) (hcomm : Commute g t) (c b a : B.V)
    (htc : B.ρ t c = c)
    (hgb : B.ρ g b = B.ρ t b)
    (hbc : b - c = B.ρ g a - a) :
    B.ρ g (b + a - B.ρ t a) = b + a - B.ρ t a := by
  have hcommAction : B.ρ g (B.ρ t a) = B.ρ t (B.ρ g a) := by
    calc
      B.ρ g (B.ρ t a) = B.ρ (g * t) a := by
        rw [map_mul]
        rfl
      _ = B.ρ (t * g) a := by rw [hcomm.eq]
      _ = B.ρ t (B.ρ g a) := by
        rw [map_mul]
        rfl
  have hb : b = c + B.ρ g a - a := by
    calc
      b = (b - c) + c := by abel
      _ = (B.ρ g a - a) + c := by rw [hbc]
      _ = c + B.ρ g a - a := by abel
  have htbc := congrArg (fun z : B.V ↦ B.ρ t z) hbc
  have htbc' : B.ρ t b - c = B.ρ t (B.ρ g a) - B.ρ t a := by
    simpa only [map_sub, htc] using htbc
  have htb : B.ρ t b = c + B.ρ t (B.ρ g a) - B.ρ t a := by
    calc
      B.ρ t b = (B.ρ t b - c) + c := by abel
      _ = (B.ρ t (B.ρ g a) - B.ρ t a) + c := by rw [htbc']
      _ = c + B.ρ t (B.ρ g a) - B.ρ t a := by abel
  calc
    B.ρ g (b + a - B.ρ t a) =
        B.ρ g b + B.ρ g a - B.ρ g (B.ρ t a) := by
      simp only [map_add, map_sub]
    _ = B.ρ t b + B.ρ g a - B.ρ t (B.ρ g a) := by
      rw [hgb, hcommAction]
    _ = c + B.ρ g a - B.ρ t a := by rw [htb]; abel
    _ = b + a - B.ρ t a := by rw [hb]; abel

namespace FiniteGaloisSubextension
/-- The lower inclusion homomorphism preserves the relative coset action. -/
theorem relativeCosetAction_lowerInclusionHom
    (A : Rep ℤ G) [IsTopologicalGroup G] {K : ClosedSubgroup G}
    (M : FiniteGaloisSubextension K) (S : Subgroup M.extensionQuotient)
    (a : ambientFixedAddSubgroup A M.field)
    (g : (M.intermediateField S).toSubgroup ⧸
      extensionSubgroup (M.intermediateField S) M.field
        (M.field_le_intermediateField S)) :
    relativeCosetAction A (M.intermediateField S) M.field
        (M.field_le_intermediateField S) a g =
      relativeCosetAction A K M.field M.below a
        (M.lowerInclusionHom S g) := by
  refine Quotient.inductionOn' g ?_
  intro m
  rfl
end FiniteGaloisSubextension

namespace FiniteCyclicSubextension
variable {K : FiniteAbstractField G}
/-- Forget only the chosen cyclic generator.  The resulting finite Galois
bundle is the canonical input to the finite reciprocity construction. -/
def toFiniteGaloisSubextension (E : FiniteCyclicSubextension K) :
    FiniteGaloisSubextension K.field where
  field := E.field
  below := E.below
  normal := E.normal
  finite := E.finite
/-- The cyclic generator transported across the finite Galois quotient
boundary. -/
def galoisGenerator (E : FiniteCyclicSubextension K) :
    E.toFiniteGaloisSubextension.extensionQuotient :=
  E.toFiniteGaloisSubextension.extensionQuotientMulEquiv.symm E.generator
/-- The transported generator still generates the whole finite Galois
quotient. -/
theorem galoisGenerator_generates (E : FiniteCyclicSubextension K) :
    ∀ x, x ∈ Subgroup.zpowers E.galoisGenerator := by
  intro x
  let e := E.toFiniteGaloisSubextension.extensionQuotientMulEquiv
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (E.generates (e x))
  apply Subgroup.mem_zpowers_iff.mpr
  refine ⟨n, ?_⟩
  apply e.injective
  change e (e.symm E.generator ^ n) = e x
  exact (map_zpow e _ n).trans
    ((congrArg (fun y => y ^ n) (e.apply_symm_apply E.generator)).trans hn)

end FiniteCyclicSubextension

namespace ValuationData

variable {D : DegreeData G} {A : Rep ℤ G}

-- The two fixed-field presentations have the same canonical addition.
-- Fix its homogeneous type before elaborating the bundled second operand.
local infixl:65 (priority := high) " + " =>
  (fun {α : Type _} [Add α] (a b : α) => HAdd.hAdd a b)

private theorem fixedRepresentation_action_eq_of_coset_eq
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    (g t : K.toSubgroup ⧸ extensionSubgroup K L hLK)
    (b : ambientFixedAddSubgroup A L)
    (h : relativeCosetAction A K L hLK b g = relativeCosetAction A K L hLK b t) :
    let B := extensionFixedRepresentation A K L hLK hnormal
    let e := extensionFixedRepresentationEquiv A K L hLK hnormal
    B.ρ g (e.symm b) = B.ρ t (e.symm b) := by
  apply Subtype.ext
  let e := extensionFixedRepresentationEquiv A K L hLK hnormal
  have hg := extensionFixedRepresentation_action_coe A K L hLK hnormal g (e.symm b)
  have ht := extensionFixedRepresentation_action_coe A K L hLK hnormal t (e.symm b)
  exact hg.trans (h.trans ht.symm)

private theorem fixedRepresentation_fixes_nsmul_of_coset_fixed
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    (g : K.toSubgroup ⧸ extensionSubgroup K L hLK)
    (b : ambientFixedAddSubgroup A L)
    (h : relativeCosetAction A K L hLK b g = b.1) (k : ℕ) :
    let B := extensionFixedRepresentation A K L hLK hnormal
    let e := extensionFixedRepresentationEquiv A K L hLK hnormal
    B.ρ g (e.symm (k • b)) = e.symm (k • b) := by
  let B := extensionFixedRepresentation A K L hLK hnormal
  let e := extensionFixedRepresentationEquiv A K L hLK hnormal
  have hfix : B.ρ g (e.symm b) = e.symm b := by
    apply Subtype.ext
    exact (extensionFixedRepresentation_action_coe A K L hLK hnormal g _).trans h
  simpa only [map_nsmul] using congrArg (fun z => k • z) hfix

private theorem fixedSource_of_cyclic_primitive
    (v : ValuationData D A) [IsTopologicalGroup G]
    (K : FiniteAbstractField G) (M : FiniteGaloisSubextension K.field)
    (S : Subgroup M.extensionQuotient)
    (g : (M.lowerFiniteGalois S).extensionQuotient)
    (hg : ∀ x, x ∈ Subgroup.zpowers g)
    (tB : K.field.toSubgroup ⧸ extensionSubgroup K.field M.field M.below)
    (bM cM : ambientFixedAddSubgroup A M.field) (k : ℕ) :
  let M₀ := M.intermediateField S
  let hMM₀ := M.field_le_intermediateField S
  let N := M.lowerFiniteGalois S
  letI : Finite (K.field.toSubgroup ⧸ extensionSubgroup K.field M.field M.below) := M.finite
  let EM := FiniteAbstractFieldExtension.ofInclusion M.field K M.below
  let MF := EM.field
  let B := extensionFixedRepresentation A K.field M.field M.below M.normal
  let B₀ := extensionFixedRepresentation A M₀ M.field hMM₀ N.normal
  let eB := extensionFixedRepresentationEquiv A K.field M.field M.below M.normal
  let eB₀ := extensionFixedRepresentationEquiv A M₀ M.field hMM₀ N.normal
  let gB := M.extensionQuotientMulEquiv (M.lowerInclusionHom S g)
  ∀ (aN : B₀.V),
    B₀.ρ g aN - aN = eB₀.symm (bM - cM) →
    B.ρ tB (eB.symm cM) = eB.symm cM →
    B.ρ gB (eB.symm bM) = B.ρ tB (eB.symm bM) →
    Commute gB tB → v.valuationAt MF bM = k • v.oneValue →
    ∃ x : ambientFixedAddSubgroup A M₀,
      ((v.valuationAt MF (fixedFieldInclusion A M₀ M.field hMM₀ x) :
        v.valueGroup) : ZHat) = Int.castRingHom ZHat (k : ℤ) := by
  dsimp only
  intro aN haN htc hgb hcomm hvalb
  let M₀ := M.intermediateField S
  let hMM₀ := M.field_le_intermediateField S
  let N := M.lowerFiniteGalois S
  let : Finite (K.field.toSubgroup ⧸ extensionSubgroup K.field M.field M.below) := M.finite
  let EM := FiniteAbstractFieldExtension.ofInclusion M.field K M.below
  let MF := EM.field
  let B := extensionFixedRepresentation A K.field M.field M.below M.normal
  let B₀ := extensionFixedRepresentation A M₀ M.field hMM₀ N.normal
  let eB := extensionFixedRepresentationEquiv A K.field M.field M.below M.normal
  let eB₀ := extensionFixedRepresentationEquiv A M₀ M.field hMM₀ N.normal
  let gB := M.extensionQuotientMulEquiv (M.lowerInclusionHom S g)
  let aB : B.V := eB.symm (eB₀ aN)
  let bB : B.V := eB.symm bM
  let cB : B.V := eB.symm cM
  have hActionPrimitive : eB (B.ρ gB aB) = eB₀ (B₀.ρ g aN) := by
    apply Subtype.ext
    calc
      (eB (B.ρ gB aB)).1 =
          relativeCosetAction A K.field M.field M.below (eB aB) gB :=
        extensionFixedRepresentation_action_coe
          A K.field M.field M.below M.normal gB aB
      _ = relativeCosetAction A M₀ M.field hMM₀ (eB₀ aN) g := by
        exact (M.relativeCosetAction_lowerInclusionHom A S (eB₀ aN) g).symm
      _ = (eB₀ (B₀.ρ g aN)).1 := by
        exact (extensionFixedRepresentation_action_coe
          A M₀ M.field hMM₀ N.normal g aN).symm
  have hprimitiveB : B.ρ gB aB - aB = eB.symm (bM - cM) := by
    apply eB.injective
    calc
      eB (B.ρ gB aB - aB) =
          eB₀ (B₀.ρ g aN) - eB₀ aN := by
        rw [map_sub, hActionPrimitive]
        simp [aB]
      _ = eB₀ (B₀.ρ g aN - aN) := by
        rw [map_sub]
      _ = eB₀ (eB₀.symm (bM - cM)) :=
        congrArg eB₀ haN
      _ = bM - cM := eB₀.apply_symm_apply _
      _ = eB (eB.symm (bM - cM)) :=
        (eB.apply_symm_apply _).symm
  have hbc : bB - cB = B.ρ gB aB - aB := by
    rw [hprimitiveB]
    exact (map_sub eB.symm bM cM).symm
  let xB : B.V := bB + aB - B.ρ tB aB
  have hxB : B.ρ gB xB = xB :=
    abstractReciprocity_fixedCombination_of_commute
      B gB tB hcomm cB bB aB htc hgb hbc
  let xB₀ : B₀.V := eB₀.symm (eB xB)
  have hActionX : eB₀ (B₀.ρ g xB₀) = eB (B.ρ gB xB) := by
    apply Subtype.ext
    calc
      (eB₀ (B₀.ρ g xB₀)).1 =
          relativeCosetAction A M₀ M.field hMM₀ (eB₀ xB₀) g :=
        extensionFixedRepresentation_action_coe
          A M₀ M.field hMM₀ N.normal g xB₀
      _ = relativeCosetAction A K.field M.field M.below (eB xB) gB :=
        M.relativeCosetAction_lowerInclusionHom A S (eB xB) g
      _ = (eB (B.ρ gB xB)).1 := by
        exact (extensionFixedRepresentation_action_coe
          A K.field M.field M.below M.normal gB xB).symm
  have hxB₀ : B₀.ρ g xB₀ = xB₀ := by
    apply eB₀.injective
    rw [hActionX, hxB]
    rfl
  let : Fintype N.extensionQuotient := Fintype.ofFinite _
  let : IsCyclic N.extensionQuotient :=
    isCyclic_iff_exists_zpowers_eq_top.mpr ⟨g, top_unique (fun x _ => hg x)⟩
  let : CommGroup N.extensionQuotient := IsCyclic.commGroup
  let T := Rep.FiniteCyclicGroup.normHomCompSub B₀ g
  let xCycle : T.moduleCatLeftHomologyData.K := ⟨xB₀, by
    change B₀.ρ g xB₀ - xB₀ = 0
    exact sub_eq_zero.mpr hxB₀⟩
  let x : ambientFixedAddSubgroup A M₀ :=
    (cyclicFixedCycleEquiv A M₀ M.field hMM₀
      N.normal N.finite g hg).symm xCycle
  refine ⟨x, ?_⟩
  have hxFormula : fixedFieldInclusion A M₀ M.field hMM₀ x = eB xB := by
    apply Subtype.ext
    rfl
  have hActionVal :=
    v.valuationAt_extensionFixedRepresentation_action
      EM M.normal tB aB
  change v.valuationAt MF (eB (B.ρ tB aB)) = v.valuationAt MF (eB aB) at hActionVal
  have hval : v.valuationAt MF
      (fixedFieldInclusion A M₀ M.field hMM₀ x) =
      k • v.oneValue := by
    rw [hxFormula]
    have hxBFormula : eB xB = bM + eB aB - eB (B.ρ tB aB) := by
      apply Subtype.ext
      rfl
    rw [hxBFormula]
    rw [map_sub, map_add, hvalb, hActionVal]
    abel
  calc
    ((v.valuationAt MF
        (fixedFieldInclusion A M₀ M.field hMM₀ x) :
          v.valueGroup) : ZHat) =
        ((k • v.oneValue : v.valueGroup) : ZHat) :=
      congrArg Subtype.val hval
    _ = k • (1 : ZHat) := rfl
    _ = Int.castRingHom ZHat (k : ℤ) := by
      simp

/-- The complete source-producing calculation in the cyclic totally
ramified case of the abstract reciprocity theorem. All fields, restriction
maps, norm identities, and action identities are constructed from the
original data; none is exposed as a hypothesis. -/
theorem abstractReciprocity_cyclicTotallyRamified_fixedSource
    (v : ValuationData D A) (hcf : SatisfiesClassFieldAxiom A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteAbstractField G)
    (E : FiniteCyclicSubextension K)
    (hTot : E.IsTotallyRamified D)
    (k : ℕ)
    (piSigma : ambientFixedAddSubgroup A
      (D.frobeniusFixedField (K.toFiniteResidueAbstractField D)
        E.field E.below
        (D.chosenDegreeOneFrobeniusLiftOfFiniteTotallyRamified
          (K.toFiniteResidueAbstractField D)
          E.toFiniteGaloisSubextension
          hTot
          E.galoisGenerator)))
    (piL : ambientFixedAddSubgroup A E.field) :
    let L := E.toFiniteAbstractFieldExtension.field
    let KR := K.toFiniteResidueAbstractField D
    letI : Finite
        ((baseField G).toSubgroup ⧸
          extensionSubgroup (baseField G) KR.field
            (le_baseField KR.field)) := K.finite
    let LG := E.toFiniteGaloisSubextension
    letI : Finite
        (KR.field.toSubgroup ⧸
          extensionSubgroup KR.field LG.field LG.below) :=
      LG.finite
    let q := E.galoisGenerator
    let hLGTot := hTot
    let σ := D.chosenDegreeOneFrobeniusLiftOfFiniteTotallyRamified
      KR LG hLGTot q
    let Sigma := D.frobeniusFixedField KR LG.field LG.below σ
    let hSigmaK := D.frobeniusFixedField_le KR LG.field LG.below σ
    letI : Finite
        (K.field.toSubgroup ⧸ extensionSubgroup K.field Sigma hSigmaK) :=
      D.frobeniusFixedField_finite KR LG.field LG.below σ
    ∀ (w : v.unitAddSubgroup L)
      (_hpiL : v.IsPrimeElement L piL)
      (_hnorm :
        relativeNorm A K.field E.field E.below (k • piL + w.1) =
          relativeNorm A K.field Sigma hSigmaK (k • piSigma)),
    let M := D.abstractReciprocityTotallyRamifiedFiniteGaloisExtension
      KR LG hLGTot q
    letI : Finite
        (KR.field.toSubgroup ⧸
          extensionSubgroup KR.field M.field M.below) :=
      M.finite
    letI : Finite ((baseField G).toSubgroup ⧸
        extensionSubgroup (baseField G) M.field
          (le_baseField M.field)) :=
      FiniteGaloisSubextension.finite_extension_trans M.below (le_baseField K.field)
    let MF : FiniteAbstractField G := ⟨M.field, inferInstance⟩
    let S := M.inertiaImage D
    let M₀ := M.maximalUnramifiedSubextension D
    let hMM₀ : M.field.toSubgroup ≤ M₀.toSubgroup :=
      M.field_le_intermediateField S
    ∃ x : ambientFixedAddSubgroup A M₀,
      ((v.valuationAt MF
        (fixedFieldInclusion A M₀ M.field hMM₀ x) :
          v.valueGroup) : ZHat) =
        Int.castRingHom ZHat (k : ℤ) := by
  dsimp only
  let L := E.toFiniteAbstractFieldExtension.field
  let KR := K.toFiniteResidueAbstractField D
  let LG := E.toFiniteGaloisSubextension
  let hLGfinite := LG.finite
  let q := E.galoisGenerator
  let hq := E.galoisGenerator_generates
  let hLGTot := hTot
  let hKRabsolute : Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) KR.field (le_baseField KR.field)) := K.finite
  let σ := D.chosenDegreeOneFrobeniusLiftOfFiniteTotallyRamified
    KR LG hLGTot q
  let Sigma := D.frobeniusFixedField KR LG.field LG.below σ
  let hSigmaK := D.frobeniusFixedField_le KR LG.field LG.below σ
  let hSigmaFinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field Sigma hSigmaK) :=
    D.frobeniusFixedField_finite KR LG.field LG.below σ
  intro w hpiL hnorm
  let M := D.abstractReciprocityTotallyRamifiedFiniteGaloisExtension
    KR LG hLGTot q
  let hMfinite := M.finite
  let hMabsolute : Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) M.field (le_baseField M.field)) :=
    FiniteGaloisSubextension.finite_extension_trans M.below (le_baseField K.field)
  let MF : FiniteAbstractField G := ⟨M.field, hMabsolute⟩
  let S := M.inertiaImage D
  let M₀ := M.maximalUnramifiedSubextension D
  let hML := D.abstractReciprocityTotallyRamifiedFiniteGaloisExtension_le_L
    KR LG hLGTot q
  let hMSigma :=
    D.abstractReciprocityTotallyRamifiedFiniteGaloisExtension_le_sigma
      KR LG hLGTot q
  let hMM₀ : M.field.toSubgroup ≤ M₀.toSubgroup :=
    M.field_le_intermediateField S
  let hM₀K : M₀.toSubgroup ≤ K.field.toSubgroup :=
    M.intermediateField_le_base S
  let N := M.lowerFiniteGalois S
  let hMnormal : (extensionSubgroup K.field M.field M.below).Normal := M.normal
  let hNnormal : (extensionSubgroup M₀ M.field hMM₀).Normal := N.normal
  let hNfinite : Finite (M₀.toSubgroup ⧸ extensionSubgroup M₀ M.field hMM₀) := N.finite
  let hMLfinite : Finite
      (E.field.toSubgroup ⧸ extensionSubgroup E.field M.field hML) :=
    FiniteGaloisSubextension.finite_extension_over_intermediate
      M.below E.below hML
  let hM₀finite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field M₀ hM₀K) := M.intermediateField_finite S
  let hM₀absolute : Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) M₀ (le_baseField M₀)) :=
    FiniteGaloisSubextension.finite_extension_trans hM₀K (le_baseField K.field)
  let M₀F : FiniteAbstractField G := ⟨M₀, hM₀absolute⟩
  let EN : FiniteAbstractFieldExtension G :=
    { field := MF
      base := M₀F
      below := hMM₀
      finiteQuotient := hNfinite }
  let EML : FiniteAbstractFieldExtension G :=
    { field := MF
      base := L
      below := hML
      finiteQuotient := hMLfinite }
  have hUnramifiedML :
      EML.IsUnramified D := by
    change EML.toFiniteAbstractExtension.IsUnramified D
    rw [EML.toFiniteAbstractExtension.isUnramified_iff_inertia_le D]
    intro x hx
    apply D.maximalUnramifiedField_le_abstractReciprocityTotallyRamifiedFiniteGaloisExtension
      KR LG hLGTot q
    exact hx
  let piSigmaM : ambientFixedAddSubgroup A M.field :=
    fixedFieldInclusion A Sigma M.field hMSigma piSigma
  let piLM : ambientFixedAddSubgroup A M.field :=
    fixedFieldInclusion A E.field M.field hML piL
  let wUnitM : v.unitAddSubgroup MF :=
    v.unitInclusion EML hUnramifiedML w
  let wM : ambientFixedAddSubgroup A M.field := wUnitM.1
  have hpiLM : v.IsPrimeElement MF piLM := by
    exact v.prime_of_unramified EML hUnramifiedML piL hpiL
  let cM : ambientFixedAddSubgroup A M.field := k • piSigmaM
  let bM : ambientFixedAddSubgroup A M.field := k • piLM + wM
  let uM : ambientFixedAddSubgroup A M.field := cM - k • piLM
  have hbM :
      bM = fixedFieldInclusion A E.field M.field hML (k • piL + w.1) := rfl
  have hcM :
      cM = fixedFieldInclusion A Sigma M.field hMSigma (k • piSigma) := rfl
  have hNormBC : relativeNorm A M₀ M.field hMM₀ bM =
      relativeNorm A M₀ M.field hMM₀ cM :=
    (D.abstractReciprocity_totallyRamified_relativeNorm_L
      A KR LG hLGTot q (k • piL + w.1)).trans
      ((congrArg (fixedFieldInclusion A K.field M₀ hM₀K) hnorm).trans
        (D.abstractReciprocity_totallyRamified_relativeNorm_sigma
          A KR LG hLGTot q (k • piSigma)).symm)
  have hnormWU : relativeNorm A M₀ M.field hMM₀ wM =
      relativeNorm A M₀ M.field hMM₀ uM := by
    dsimp only [bM, cM, uM] at hNormBC ⊢
    rw [map_add, map_nsmul, map_nsmul] at hNormBC
    rw [map_sub, map_nsmul, map_nsmul]
    exact eq_sub_of_add_eq' hNormBC
  let g := D.abstractReciprocityTotallyRamifiedLowerGenerator
    KR LG hLGTot q
  have hg : ∀ x, x ∈ Subgroup.zpowers g :=
    D.abstractReciprocityTotallyRamifiedLowerGenerator_generates
      KR LG hLGTot q hq
  let hNFintype : Fintype N.extensionQuotient := Fintype.ofFinite _
  let hNCyclic : IsCyclic N.extensionQuotient :=
    isCyclic_iff_exists_zpowers_eq_top.mpr ⟨g, top_unique (fun x _ => hg x)⟩
  let hNcomm : CommGroup N.extensionQuotient := IsCyclic.commGroup
  obtain ⟨aN, haN⟩ :=
    abstractReciprocity_exists_hMinusOne_primitive hcf
      EN N.normal g hg uM wM hnormWU
  let B := extensionFixedRepresentation A K.field M.field M.below M.normal
  let B₀ := extensionFixedRepresentation A M₀ M.field hMM₀ N.normal
  let eB := extensionFixedRepresentationEquiv A K.field M.field M.below M.normal
  let eB₀ := extensionFixedRepresentationEquiv A M₀ M.field hMM₀ N.normal
  let gB := M.extensionQuotientMulEquiv (M.lowerInclusionHom S g)
  let tB := M.extensionQuotientMulEquiv
    (D.abstractReciprocityTotallyRamifiedFrobeniusInM
      KR LG hLGTot q)
  let aB : B.V := eB.symm (eB₀ aN)
  let bB : B.V := eB.symm bM
  let cB : B.V := eB.symm cM
  have hprimitive : B₀.ρ g aN - aN = eB₀.symm (bM - cM) := by
    have hdiff : wM - uM = bM - cM := by
      dsimp only [wM, uM, bM]
      abel
    exact haN.trans (congrArg eB₀.symm hdiff)
  have htc : B.ρ tB cB = cB :=
    fixedRepresentation_fixes_nsmul_of_coset_fixed A K.field M.field M.below M.normal
      tB piSigmaM (D.abstractReciprocityTotallyRamified_frobenius_fixes_sigma
        A KR LG hLGTot q piSigma) k
  have hgb : B.ρ gB bB = B.ρ tB bB := by
    apply fixedRepresentation_action_eq_of_coset_eq A K.field M.field M.below M.normal
    rw [hbM]
    exact D.abstractReciprocityTotallyRamified_actions_agree_on_L A KR LG hLGTot q
      (k • piL + w.1)
  have hcomm : Commute gB tB :=
    (D.abstractReciprocityTotallyRamified_generator_commutes_frobenius
      KR LG hLGTot q).map M.extensionQuotientMulEquiv.toMonoidHom
  have hvalb : v.valuationAt MF bM = k • v.oneValue := by
    dsimp only [bM]
    rw [map_add, map_nsmul, hpiLM, wUnitM.2, add_zero]
  exact v.fixedSource_of_cyclic_primitive K M S g hg tB bM cM k
    aN hprimitive htc hgb hcomm hvalb

end ValuationData

end ClassFormation
