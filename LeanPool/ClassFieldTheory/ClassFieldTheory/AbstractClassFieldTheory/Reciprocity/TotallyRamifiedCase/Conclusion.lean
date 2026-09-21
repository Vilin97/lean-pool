/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.TotallyRamifiedCase.FixedSource
/-!
# Totally ramified reciprocity

This file derives exponent vanishing, injectivity, and finally bijectivity of
finite reciprocity from the constructed fixed source.
-/

noncomputable section

namespace ClassFormation

open KummerTheory
open CyclicCohomology

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace ValuationData

variable {D : DegreeData G} {A : Rep ℤ G}

-- The two fixed-field presentations have the same canonical addition.
-- Fix its homogeneous type before elaborating the bundled second operand.
local infixl:65 (priority := high) " + " =>
  (fun {α : Type _} [Add α] (a b : α) => HAdd.hAdd a b)

/-- The exponent in the chosen cyclic decomposition is zero. -/
theorem abstractReciprocity_cyclicTotallyRamified_exponent_eq_zero
    (v : ValuationData D A) (hcf : SatisfiesClassFieldAxiom A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteAbstractField G)
    (E : FiniteCyclicSubextension K)
    (hTot : E.IsTotallyRamified D)
    (k : ℕ)
    (hk : k < (E.toFiniteAbstractExtension.degree : ℕ))
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
            (le_baseField KR.field)) := by
      change Finite
        ((baseField G).toSubgroup ⧸
          extensionSubgroup (baseField G) K.field
            (le_baseField K.field))
      exact K.finite
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
      k = 0 := by
  dsimp only
  let L := E.toFiniteAbstractFieldExtension.field
  let KR := K.toFiniteResidueAbstractField D
  let LG := E.toFiniteGaloisSubextension
  let hLGfinite : Finite
      (KR.field.toSubgroup ⧸
        extensionSubgroup KR.field LG.field LG.below) :=
    LG.finite
  let hLGfiniteOverK : Finite
      (K.field.toSubgroup ⧸
        extensionSubgroup K.field LG.field LG.below) := by
    have h := hLGfinite
    change Finite
      (K.field.toSubgroup ⧸
        extensionSubgroup K.field LG.field LG.below) at h
    exact h
  let q := E.galoisGenerator
  let hLGTot := hTot
  let hKRabsolute : Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) KR.field (le_baseField KR.field)) := by
    change Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) K.field (le_baseField K.field))
    exact K.finite
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
  let hMfinite : Finite
      (KR.field.toSubgroup ⧸
        extensionSubgroup KR.field M.field M.below) :=
    M.finite
  let S := M.inertiaImage D
  let M₀ := M.maximalUnramifiedSubextension D
  let hMM₀ : M.field.toSubgroup ≤ M₀.toSubgroup :=
    M.field_le_intermediateField S
  let hM₀K : M₀.toSubgroup ≤ K.field.toSubgroup :=
    M.intermediateField_le_base S
  let N := M.lowerFiniteGalois S
  let hNnormal : (extensionSubgroup M₀ M.field hMM₀).Normal := N.normal
  let hNfinite : Finite
      (M₀.toSubgroup ⧸ extensionSubgroup M₀ M.field hMM₀) :=
    N.finite
  let hM₀finite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field M₀ hM₀K) :=
    M.intermediateField_finite S
  let hM₀absolute : Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) M₀ (le_baseField M₀)) :=
    FiniteGaloisSubextension.finite_extension_trans hM₀K (le_baseField K.field)
  let hMabsolute : Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) M.field (le_baseField M.field)) :=
    FiniteGaloisSubextension.finite_extension_trans M.below (le_baseField K.field)
  let MF : FiniteAbstractField G := ⟨M.field, hMabsolute⟩
  let M₀F : FiniteAbstractField G := ⟨M₀, hM₀absolute⟩
  let EN : FiniteAbstractFieldExtension G :=
    { field := MF
      base := M₀F
      below := hMM₀
      finiteQuotient := hNfinite }
  obtain ⟨x, hx⟩ :=
    v.abstractReciprocity_cyclicTotallyRamified_fixedSource hcf
      K E hTot k piSigma piL w hpiL hnorm
  have hkLower : k < (N.toFiniteAbstractExtension.degree : ℕ) := by
    rw [D.abstractReciprocityTotallyRamifiedLowerDegree_eq
      KR LG hLGTot q]
    exact hk
  exact abstractReciprocity_totallyRamified_valuation_forces_exponent_zero
    v EN (by
      simpa [EN, FiniteAbstractFieldExtension.IsTotallyRamified,
        FiniteAbstractFieldExtension.toFiniteAbstractExtension] using
          M.maximalUnramifiedSubextension_isTotallyRamified D)
      k hkLower x hx

/-- In the cyclic totally ramified case, the reciprocity homomorphism of
the finite reciprocity equivalence has trivial kernel.  This is the final kernel calculation. -/
theorem abstractReciprocity_cyclicTotallyRamified_finiteReciprocityHom_injective
    (v : ValuationData D A) (hcf : SatisfiesClassFieldAxiom A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D)
    (K : FiniteAbstractField G)
    (E : FiniteCyclicSubextension K)
    (hTot : E.IsTotallyRamified D) :
    Function.Injective
      (D.finiteReciprocityHom A v hAxiom K E.field E.below) := by
  let L := E.toFiniteAbstractFieldExtension.field
  let KR := K.toFiniteResidueAbstractField D
  let LG := E.toFiniteGaloisSubextension
  let hLGfinite : Finite
      (KR.field.toSubgroup ⧸
        extensionSubgroup KR.field LG.field LG.below) :=
    LG.finite
  let hLGfiniteOverK : Finite
      (K.field.toSubgroup ⧸
        extensionSubgroup K.field LG.field LG.below) := by
    have h := hLGfinite
    change Finite
      (K.field.toSubgroup ⧸
        extensionSubgroup K.field LG.field LG.below) at h
    exact h
  let q := E.galoisGenerator
  let qRaw := E.generator
  let hLGTot := hTot
  let hKRabsolute : Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) KR.field (le_baseField KR.field)) := by
    change Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) K.field (le_baseField K.field))
    exact K.finite
  let Q := K.field.toSubgroup ⧸
    extensionSubgroup K.field E.field E.below
  let EF := E.toFiniteAbstractExtension
  let hQFintype : Fintype Q := Fintype.ofFinite _
  let σ := D.chosenDegreeOneFrobeniusLiftOfFiniteTotallyRamified
    KR LG hLGTot q
  let Sigma := D.frobeniusFixedField KR LG.field LG.below σ
  let hSigmaK := D.frobeniusFixedField_le KR LG.field LG.below σ
  let hSigmaFinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field Sigma hSigmaK) :=
    D.frobeniusFixedField_finite KR LG.field LG.below σ
  let hSigmaAbsolute : Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) Sigma (le_baseField Sigma)) :=
    D.frobeniusFixedField_absoluteFinite K LG.field LG.below σ
  let SigmaF : FiniteAbstractField G := ⟨Sigma, hSigmaAbsolute⟩
  let piSigma : ambientFixedAddSubgroup A Sigma := v.chosenPrimeElement SigmaF
  let piL : ambientFixedAddSubgroup A E.field := v.chosenPrimeElement L
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨i, hi, _⟩ :=
    IsCyclic.unique_zpow_zmod (a := qRaw) E.generates x.toMul
  let k : ℕ := i.val
  have hcard : Fintype.card Q = (EF.degree : ℕ) := by
    calc
      Fintype.card Q = Nat.card Q := by
        rw [Nat.card_eq_fintype_card]
      _ = (extensionSubgroup K.field E.field E.below).index :=
        (Subgroup.index_eq_card
          (extensionSubgroup K.field E.field E.below)).symm
      _ = (EF.degree : ℕ) :=
        EF.extensionSubgroup_index_eq_degree
  have hk : k < (EF.degree : ℕ) := by
    rw [← hcard]
    exact i.val_lt
  have hxrepr : x = k • Additive.ofMul qRaw := by
    apply Additive.toMul.injective
    change x.toMul = qRaw ^ k
    exact hi
  rw [hxrepr, map_nsmul,
    D.finiteReciprocityHom_apply_eq_primeNormClass
      A v hAxiom K E.field E.below (Additive.ofMul qRaw) σ
      (by
        change D.frobeniusRestriction KR LG.field LG.below σ = qRaw
        exact
          (D.frobeniusRestriction_chosenDegreeOneFrobeniusLiftOfFiniteTotallyRamified_underlying
            KR LG hLGTot q).trans
            (E.toFiniteGaloisSubextension.extensionQuotientMulEquiv.apply_symm_apply
              E.generator))
      piSigma (v.chosenPrimeElement_isPrime SigmaF)] at hx
  have hclass :
      finiteNormClass A K.field E.field E.below
          (relativeNorm A K.field Sigma hSigmaK (k • piSigma)) = 0 := by
    have hx' := hx
    change k • finiteNormClass A K.field E.field E.below
        (relativeNorm A K.field Sigma hSigmaK piSigma) = 0 at hx'
    rw [map_nsmul, finiteNormClass_nsmul]
    exact hx'
  have hSigmaResidue :
      ((DegreeData.FiniteAbstractExtension.ofInclusion
        Sigma K.field hSigmaK).residueDegree D : ℕ) = 1 := by
    calc
      ((DegreeData.FiniteAbstractExtension.ofInclusion
          Sigma K.field hSigmaK).residueDegree D : ℕ) =
          D.frobeniusExponent KR LG.field LG.below σ :=
        D.frobeniusFixedField_residueDegreeOverBase KR LG.field LG.below σ
      _ = 1 :=
        D.frobeniusExponent_chosenDegreeOneFrobeniusLiftOfFiniteTotallyRamified
          KR LG hLGTot q
  let : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L.field E.below) := E.finite
  obtain ⟨w, hnorm⟩ :=
    v.primeNormClass_eq_zero_exists_unit_norm_eq
      K L SigmaF E.below hSigmaK hTot hSigmaResidue
      k piSigma piL (v.chosenPrimeElement_isPrime SigmaF)
      (v.chosenPrimeElement_isPrime L) hclass
  have hkzero := v.abstractReciprocity_cyclicTotallyRamified_exponent_eq_zero
    hcf K E hTot k hk piSigma piL
      w (v.chosenPrimeElement_isPrime L) hnorm
  rw [hxrepr, hkzero, zero_nsmul]

/-- The cyclic totally ramified instance of the abstract reciprocity theorem. -/
theorem abstractReciprocity_cyclicTotallyRamified_finiteReciprocityHom_bijective
    (v : ValuationData D A) (hcf : SatisfiesClassFieldAxiom A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D)
    (K : FiniteAbstractField G)
    (E : FiniteCyclicSubextension K)
    (hTot : E.IsTotallyRamified D) :
    Function.Bijective
      (D.finiteReciprocityHom A v hAxiom K E.field E.below) := by
  let EF := E.toFiniteAbstractExtension
  let hEbaseAbsolute : Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) EF.base (le_baseField EF.base)) := by
    simpa [EF, FiniteCyclicSubextension.toFiniteAbstractExtension] using K.finite
  let : Finite (FiniteNormQuotient A K.field E.field E.below) :=
    finiteNormQuotient_finite_of_classFieldAxiom
      A hcf EF E.normal E.generator E.generates
  apply (Nat.bijective_iff_injective_and_card
    (D.finiteReciprocityHom A v hAxiom K E.field E.below)).2
  exact ⟨v.abstractReciprocity_cyclicTotallyRamified_finiteReciprocityHom_injective
      hcf hAxiom K E hTot,
    cyclicReciprocity_card_equality
      A hcf EF E.normal E.generator E.generates⟩

end ValuationData

end ClassFormation
