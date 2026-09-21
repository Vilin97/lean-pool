/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.MainMultiplicativity.FrobeniusActionRemainder
import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.RelativeNormDoubleCoset
/-!
# Norms of primes in conjugate Frobenius fixed fields

This file transports prime elements across Frobenius-action conjugation and
proves equality of their relative norms in the base fixed field.
-/

universe u

namespace ClassFormation

open KummerTheory
open CyclicCohomology

noncomputable section

open CategoryTheory

section conjugatePrimeNorms

/-!
Mathlib's `Rep ℤ G` requires its coefficient ring and acting group in the
same universe, so this representation-bearing portion has `G : IntegralRepGroupType`.
-/
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- The prime used for the conjugate Frobenius fixed field may be chosen
as the conjugate of a prime in the original fixed field.  Conjugation compatibility of normalized valuations preserves primality, while conjugation equivariance of the relative
norm and the fact that the conjugating representative lies in `G_K` give
equality of the two norms in `A_K`. -/
theorem exists_primeElement_frobeniusActionConjugate_norm_eq
    (D : DegreeData G) (A : Rep ℤ G) (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    [hLfinite : Finite (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (φ σ : D.FrobeniusElements
      (K.toFiniteResidueAbstractField D) L hLK) (m : ℕ)
    (π : ambientFixedAddSubgroup A
      (D.frobeniusFixedField (K.toFiniteResidueAbstractField D) L hLK σ))
    (hπ :
      let KR := K.toFiniteResidueAbstractField D
      let Sigma : FiniteAbstractField G :=
        ⟨D.frobeniusFixedField KR L hLK σ,
          D.frobeniusFixedField_absoluteFinite K L hLK σ⟩
      v.IsPrimeElement Sigma π) :
    let KR := K.toFiniteResidueAbstractField D
    let σ' := D.frobeniusActionConjugate KR L hLK φ σ m
    let S := D.frobeniusFixedField KR L hLK σ
    let S' := D.frobeniusFixedField KR L hLK σ'
    let hSK := D.frobeniusFixedField_le KR L hLK σ
    let hS'K := D.frobeniusFixedField_le KR L hLK σ'
    letI : Finite (K.field.toSubgroup ⧸ extensionSubgroup K.field S hSK) :=
      D.frobeniusFixedField_finite KR L hLK σ
    letI : Finite (K.field.toSubgroup ⧸ extensionSubgroup K.field S' hS'K) :=
      D.frobeniusFixedField_finite KR L hLK σ'
    let Sigma' : FiniteAbstractField G :=
      ⟨S', D.frobeniusFixedField_absoluteFinite K L hLK σ'⟩
    ∃ π' : ambientFixedAddSubgroup A S',
      v.IsPrimeElement Sigma' π' ∧
        relativeNorm A K.field S' hS'K π' =
          relativeNorm A K.field S hSK π := by
  dsimp only
  let KR := K.toFiniteResidueAbstractField D
  let hLnormalKR : (extensionSubgroup KR.field L hLK).Normal := by
    simpa only [KR, FiniteAbstractField.toFiniteResidueAbstractField] using hLnormal
  let hLfiniteKR : Finite
      (KR.field.toSubgroup ⧸ extensionSubgroup KR.field L hLK) := by
    simpa only [KR, FiniteAbstractField.toFiniteResidueAbstractField] using hLfinite
  let σ' := D.frobeniusActionConjugate KR L hLK φ σ m
  let S := D.frobeniusFixedField KR L hLK σ
  let S' := D.frobeniusFixedField KR L hLK σ'
  let hSK := D.frobeniusFixedField_le KR L hLK σ
  let hS'K := D.frobeniusFixedField_le KR L hLK σ'
  let hSfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field S hSK) :=
    D.frobeniusFixedField_finite KR L hLK σ
  let hS'finite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field S' hS'K) :=
    D.frobeniusFixedField_finite KR L hLK σ'
  let hSabsolute : Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) S (le_baseField S)) :=
    D.frobeniusFixedField_absoluteFinite K L hLK σ
  let hS'absolute : Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) S' (le_baseField S')) :=
    D.frobeniusFixedField_absoluteFinite K L hLK σ'
  let Sigma : FiniteAbstractField G := ⟨S, hSabsolute⟩
  let Sigma' : FiniteAbstractField G := ⟨S', hS'absolute⟩
  let q := φ.1 ^ m
  let k : K.field.toSubgroup := Quotient.out q
  let s : G := k.1⁻¹
  let C := conjugateClosedSubgroup S s
  let Kc := conjugateClosedSubgroup K.field s
  let hCS := conjugateClosedSubgroup_mono hSK s
  have hC : C = S' := by
    simpa [C, S, S', σ', q, k, s] using
      D.conjugate_frobeniusFixedField_actionConjugate KR L hLK φ σ m
  have hKc : Kc = K.field := by
    ext x
    change x ∈ conjugateClosedSubgroup K.field s ↔ x ∈ K.field
    rw [conjugateClosedSubgroup_mem]
    constructor
    · intro hx
      change x ∈ K.field.toSubgroup
      simpa [s, mul_assoc] using K.field.toSubgroup.mul_mem
        (K.field.toSubgroup.mul_mem k.2 hx) (K.field.toSubgroup.inv_mem k.2)
    · intro hx
      change s * x * s⁻¹ ∈ K.field.toSubgroup
      simpa [s] using K.field.toSubgroup.mul_mem
        (K.field.toSubgroup.mul_mem (K.field.toSubgroup.inv_mem k.2) hx) k.2
  let hCabsolute : Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) C (le_baseField C)) :=
    Finite.of_equiv
      ((baseField G).toSubgroup ⧸
        extensionSubgroup (baseField G) S (le_baseField S))
      (by
        simpa [C, baseField] using
          (absoluteConjugateCosetEquiv S s).symm)
  let SigmaC : FiniteAbstractField G := Sigma.conjugate s
  let πC : ambientFixedAddSubgroup A C :=
    conjugateFixedElement A S s π
  let π' : ambientFixedAddSubgroup A S' :=
    ⟨πC.1, by rw [← hC]; exact πC.2⟩
  have hπC : v.IsPrimeElement SigmaC πC := by
    change v.valuationAt Sigma π = v.oneValue at hπ
    change v.valuationAt SigmaC πC = v.oneValue
    have hconj : v.valuationAt SigmaC πC = v.valuationAt Sigma π := by
      simpa [C, SigmaC, Sigma, πC] using
        v.normalizedValuation_conjugate Sigma s π
    exact hconj.trans hπ
  have hπ' : v.IsPrimeElement Sigma' π' := by
    change v.valuationAt SigmaC πC = v.oneValue at hπC
    change v.valuationAt Sigma' π' = v.oneValue
    have valuation_transport
        (C₀ S₀ : FiniteAbstractField G)
        (h : C₀.field = S₀.field)
        (aC : ambientFixedAddSubgroup A C₀.field)
        (aS : ambientFixedAddSubgroup A S₀.field)
        (ha : aC.1 = aS.1) :
        v.valuationAt S₀ aS = v.valuationAt C₀ aC := by
      cases C₀ with
      | mk C₀ hC₀ =>
          cases S₀ with
          | mk S₀ hS₀ =>
              dsimp only at h
              subst S₀
              congr 1
              exact Subtype.ext ha.symm
    have hSigmaField : SigmaC.field = Sigma'.field := by
      change C = S'
      exact hC
    have hv : v.valuationAt Sigma' π' = v.valuationAt SigmaC πC :=
      valuation_transport SigmaC Sigma' hSigmaField πC π' rfl
    exact hv.trans hπC
  refine ⟨π', hπ', ?_⟩
  let hCSfinite : Finite
      (Kc.toSubgroup ⧸ extensionSubgroup Kc C hCS) :=
    finite_conjugateExtension K.field S hSK s
  have hnormC := relativeNorm_conjugate_apply A K.field S hSK s π
  apply Subtype.ext
  have relativeNorm_transport
      (K₀ K₁ L₀ L₁ : ClosedSubgroup G)
      (h₀ : L₀.toSubgroup ≤ K₀.toSubgroup)
      (h₁ : L₁.toSubgroup ≤ K₁.toSubgroup)
      [Finite (K₀.toSubgroup ⧸ extensionSubgroup K₀ L₀ h₀)]
      [Finite (K₁.toSubgroup ⧸ extensionSubgroup K₁ L₁ h₁)]
      (hK₀ : K₀ = K₁) (hL₀ : L₀ = L₁)
      (a₀ : ambientFixedAddSubgroup A L₀)
      (a₁ : ambientFixedAddSubgroup A L₁)
      (ha : a₀.1 = a₁.1) :
      ((relativeNorm A K₀ L₀ h₀ a₀ :
        ambientFixedAddSubgroup A K₀) : A.V) =
      ((relativeNorm A K₁ L₁ h₁ a₁ :
        ambientFixedAddSubgroup A K₁) : A.V) := by
    subst K₁
    subst L₁
    have ha' : a₀ = a₁ := Subtype.ext ha
    subst a₁
    rfl
  have hleft :
      ((relativeNorm A K.field S' hS'K π' :
        ambientFixedAddSubgroup A K.field) : A.V) =
      ((relativeNorm A Kc C hCS πC :
        ambientFixedAddSubgroup A Kc) : A.V) := by
    exact (relativeNorm_transport Kc K.field C S' hCS hS'K
      hKc hC πC π' rfl).symm
  calc
    ((relativeNorm A K.field S' hS'K π' :
        ambientFixedAddSubgroup A K.field) : A.V) =
        ((relativeNorm A Kc C hCS πC :
          ambientFixedAddSubgroup A Kc) : A.V) := hleft
    _ = ((conjugateFixedElement A K.field s
        (relativeNorm A K.field S hSK π) :
          ambientFixedAddSubgroup A Kc) : A.V) :=
      congrArg Subtype.val hnormC
    _ = ((relativeNorm A K.field S hSK π :
        ambientFixedAddSubgroup A K.field) : A.V) := by
      rw [conjugateFixedElement_coe]
      have hs : s⁻¹ = k.1 := by simp [s]
      rw [hs]
      change A.ρ k.1 (relativeNorm A K.field S hSK π).1 =
        (relativeNorm A K.field S hSK π).1
      exact (relativeNorm A K.field S hSK π).2 k

end DegreeData

end conjugatePrimeNorms

end

end ClassFormation
