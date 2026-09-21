/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.MainMultiplicativity.FrobeniusActionRemainder
import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.CanonicalUnramifiedNormQuotient
/-!
# Norm-class relations for reciprocity multiplicativity

This file passes the alternating Frobenius power-sum norm relation to the
maximal-unramified norm quotient and then to the reciprocity map.
-/

universe u

namespace ClassFormation

open KummerTheory
open CyclicCohomology

noncomputable section

open CategoryTheory

variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- Applying the relative norm from the maximal unramified extension to the
alternating Frobenius power sum gives the alternating sum of the three
finite fixed-field norms. -/
theorem relativeNorm_frobeniusPowerSum_alternating
    (D : DegreeData G) (A : Rep ℤ G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    [hLfinite : Finite (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (φ σ₁ σ₂ : D.FrobeniusElements K L hLK)
    (hφ : D.frobeniusExponent K L hLK φ = 1)
    (π₁ : ambientFixedAddSubgroup A
      (D.frobeniusFixedField K L hLK σ₁))
    (π₃ : ambientFixedAddSubgroup A
      (D.frobeniusFixedField K L hLK (σ₁ * σ₂)))
    (π₄ : ambientFixedAddSubgroup A
      (D.frobeniusFixedField K L hLK
        (D.frobeniusActionConjugate K L hLK φ σ₂
          (D.frobeniusExponent K L hLK σ₁)))) :
    let σ₃ := σ₁ * σ₂
    let σ₄ := D.frobeniusActionConjugate K L hLK φ σ₂
      (D.frobeniusExponent K L hLK σ₁)
    let S₁ := D.frobeniusFixedField K L hLK σ₁
    let S₃ := D.frobeniusFixedField K L hLK σ₃
    let S₄ := D.frobeniusFixedField K L hLK σ₄
    let hS₁K := D.frobeniusFixedField_le K L hLK σ₁
    let hS₃K := D.frobeniusFixedField_le K L hLK σ₃
    let hS₄K := D.frobeniusFixedField_le K L hLK σ₄
    let p₁ := fixedFieldInclusion A S₁ (D.maximalUnramifiedField L)
      (D.fieldInertia_le_frobeniusFixedField K L hLK σ₁) π₁
    let p₃ := fixedFieldInclusion A S₃ (D.maximalUnramifiedField L)
      (D.fieldInertia_le_frobeniusFixedField K L hLK σ₃) π₃
    let p₄ := fixedFieldInclusion A S₄ (D.maximalUnramifiedField L)
      (D.fieldInertia_le_frobeniusFixedField K L hLK σ₄) π₄
    let u := D.frobeniusPowerSum A K.field L hLK φ.1
        (D.frobeniusExponent K L hLK σ₄) p₄ +
      D.frobeniusPowerSum A K.field L hLK φ.1
        (D.frobeniusExponent K L hLK σ₁) p₁ -
      D.frobeniusPowerSum A K.field L hLK φ.1
        (D.frobeniusExponent K L hLK σ₃) p₃
    letI : Finite (K.field.toSubgroup ⧸ extensionSubgroup K.field S₁ hS₁K) :=
      D.frobeniusFixedField_finite K L hLK σ₁
    letI : Finite (K.field.toSubgroup ⧸ extensionSubgroup K.field S₃ hS₃K) :=
      D.frobeniusFixedField_finite K L hLK σ₃
    letI : Finite (K.field.toSubgroup ⧸ extensionSubgroup K.field S₄ hS₄K) :=
      D.frobeniusFixedField_finite K L hLK σ₄
    letI : Finite
        ((D.maximalUnramifiedField K.field).toSubgroup ⧸
          extensionSubgroup (D.maximalUnramifiedField K.field)
            (D.maximalUnramifiedField L)
            (D.maximalUnramifiedField_mono hLK)) :=
      D.maximalUnramifiedExtension_finite K.field L hLK
    ((relativeNorm A (D.maximalUnramifiedField K.field)
      (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK) u :
        ambientFixedAddSubgroup A (D.maximalUnramifiedField K.field)) : A.V) =
      ((relativeNorm A K.field S₄ hS₄K π₄ +
        relativeNorm A K.field S₁ hS₁K π₁ -
        relativeNorm A K.field S₃ hS₃K π₃ :
          ambientFixedAddSubgroup A K.field) : A.V) := by
  dsimp only
  let σ₃ := σ₁ * σ₂
  let σ₄ := D.frobeniusActionConjugate K L hLK φ σ₂
    (D.frobeniusExponent K L hLK σ₁)
  let S₁ := D.frobeniusFixedField K L hLK σ₁
  let S₃ := D.frobeniusFixedField K L hLK σ₃
  let S₄ := D.frobeniusFixedField K L hLK σ₄
  let hS₁K := D.frobeniusFixedField_le K L hLK σ₁
  let hS₃K := D.frobeniusFixedField_le K L hLK σ₃
  let hS₄K := D.frobeniusFixedField_le K L hLK σ₄
  let p₁ := fixedFieldInclusion A S₁ (D.maximalUnramifiedField L)
    (D.fieldInertia_le_frobeniusFixedField K L hLK σ₁) π₁
  let p₃ := fixedFieldInclusion A S₃ (D.maximalUnramifiedField L)
    (D.fieldInertia_le_frobeniusFixedField K L hLK σ₃) π₃
  let p₄ := fixedFieldInclusion A S₄ (D.maximalUnramifiedField L)
    (D.fieldInertia_le_frobeniusFixedField K L hLK σ₄) π₄
  let s₁ := D.frobeniusPowerSum A K.field L hLK φ.1
    (D.frobeniusExponent K L hLK σ₁) p₁
  let s₃ := D.frobeniusPowerSum A K.field L hLK φ.1
    (D.frobeniusExponent K L hLK σ₃) p₃
  let s₄ := D.frobeniusPowerSum A K.field L hLK φ.1
    (D.frobeniusExponent K L hLK σ₄) p₄
  let u := s₄ + s₁ - s₃
  let hS₁finite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field S₁ hS₁K) :=
    D.frobeniusFixedField_finite K L hLK σ₁
  let hS₃finite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field S₃ hS₃K) :=
    D.frobeniusFixedField_finite K L hLK σ₃
  let hS₄finite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field S₄ hS₄K) :=
    D.frobeniusFixedField_finite K L hLK σ₄
  let hIfinite : Finite
      ((D.maximalUnramifiedField K.field).toSubgroup ⧸
        extensionSubgroup (D.maximalUnramifiedField K.field)
          (D.maximalUnramifiedField L)
          (D.maximalUnramifiedField_mono hLK)) :=
    D.maximalUnramifiedExtension_finite K.field L hLK
  have h₁ := (D.frobeniusNormIdentities A K L hLK φ σ₁ hφ π₁).1
  have h₃ := (D.frobeniusNormIdentities A K L hLK φ σ₃ hφ π₃).1
  have h₄ := (D.frobeniusNormIdentities A K L hLK φ σ₄ hφ π₄).1
  let N := relativeNorm A (D.maximalUnramifiedField K.field)
    (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK)
  change ((N (s₄ + s₁ - s₃) :
      ambientFixedAddSubgroup A (D.maximalUnramifiedField K.field)) : A.V) = _
  rw [map_sub, map_add]
  change (N s₄).1 + (N s₁).1 - (N s₃).1 = _
  rw [← h₄, ← h₁, ← h₃]
  rfl

/-- Final quotient step in reciprocity multiplicativity.  Once the maximal-unramified
norm of `u` descends to a universal norm in `A_K`, the alternating norm
relation is exactly the desired equality of reciprocity classes. -/
theorem maximalUnramifiedNormClass_add_eq_of_relativeNorm
    (D : DegreeData G) (A : Rep ℤ G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [Finite (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    [Finite
      ((D.maximalUnramifiedField K.field).toSubgroup ⧸
        extensionSubgroup (D.maximalUnramifiedField K.field)
          (D.maximalUnramifiedField L)
          (D.maximalUnramifiedField_mono hLK))]
    (r₁ r₂ r₃ : ambientFixedAddSubgroup A K.field)
    (u : ambientFixedAddSubgroup A (D.maximalUnramifiedField L))
    (hnorm :
      ((relativeNorm A (D.maximalUnramifiedField K.field)
        (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK) u :
          ambientFixedAddSubgroup A (D.maximalUnramifiedField K.field)) : A.V) =
        ((r₁ + r₂ - r₃ : ambientFixedAddSubgroup A K.field) : A.V))
    (huniversal : ∃ aK : ambientFixedAddSubgroup A K.field,
      fixedFieldInclusion A K.field (D.maximalUnramifiedField K.field)
          (D.maximalUnramifiedField_le K.field) aK =
        relativeNorm A (D.maximalUnramifiedField K.field)
          (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK) u ∧
      aK ∈ D.maximalUnramifiedNormSubgroup A K.field L) :
    D.maximalUnramifiedNormClass A K.field L r₁ +
        D.maximalUnramifiedNormClass A K.field L r₂ =
      D.maximalUnramifiedNormClass A K.field L r₃ := by
  obtain ⟨aK, hdescend, haK⟩ := huniversal
  have hsum : r₁ + r₂ - r₃ = aK := by
    apply Subtype.ext
    exact hnorm.symm.trans (congrArg Subtype.val hdescend).symm
  have hmem : r₁ + r₂ - r₃ ∈
      D.maximalUnramifiedNormSubgroup A K.field L := by
    rw [hsum]
    exact haK
  have hzero := (D.maximalUnramifiedNormClass_eq_zero_iff
    A K.field L (r₁ + r₂ - r₃)).2 hmem
  rw [map_sub, map_add] at hzero
  exact sub_eq_zero.mp hzero

/-- Prime-choice independence converts an equality of the three explicit
norm classes into reciprocity multiplicativity's equality for the canonical reciprocity
map. -/
theorem reciprocityMap_mul_of_primeNormClass_eq
    (D : DegreeData G) (A : Rep ℤ G) (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D)
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    [hLfinite : Finite (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (σ₁ σ₂ : D.FrobeniusElements
      (K.toFiniteResidueAbstractField D) L hLK)
    (π₁ : ambientFixedAddSubgroup A
      (D.frobeniusFixedField (K.toFiniteResidueAbstractField D) L hLK σ₁))
    (π₂ : ambientFixedAddSubgroup A
      (D.frobeniusFixedField (K.toFiniteResidueAbstractField D) L hLK σ₂))
    (π₃ : ambientFixedAddSubgroup A
      (D.frobeniusFixedField (K.toFiniteResidueAbstractField D) L hLK
        (σ₁ * σ₂)))
    (hπ₁ :
      let KR := K.toFiniteResidueAbstractField D
      let Sigma1 : FiniteAbstractField G :=
        ⟨D.frobeniusFixedField KR L hLK σ₁,
          D.frobeniusFixedField_absoluteFinite K L hLK σ₁⟩
      v.IsPrimeElement Sigma1 π₁)
    (hπ₂ :
      let KR := K.toFiniteResidueAbstractField D
      let Sigma2 : FiniteAbstractField G :=
        ⟨D.frobeniusFixedField KR L hLK σ₂,
          D.frobeniusFixedField_absoluteFinite K L hLK σ₂⟩
      v.IsPrimeElement Sigma2 π₂)
    (hπ₃ :
      let KR := K.toFiniteResidueAbstractField D
      let Sigma3 : FiniteAbstractField G :=
        ⟨D.frobeniusFixedField KR L hLK (σ₁ * σ₂),
          D.frobeniusFixedField_absoluteFinite K L hLK (σ₁ * σ₂)⟩
      v.IsPrimeElement Sigma3 π₃)
    (hclasses :
      let KR := K.toFiniteResidueAbstractField D
      let S₁ := D.frobeniusFixedField KR L hLK σ₁
      let S₂ := D.frobeniusFixedField KR L hLK σ₂
      let S₃ := D.frobeniusFixedField KR L hLK (σ₁ * σ₂)
      let hS₁K := D.frobeniusFixedField_le KR L hLK σ₁
      let hS₂K := D.frobeniusFixedField_le KR L hLK σ₂
      let hS₃K := D.frobeniusFixedField_le KR L hLK (σ₁ * σ₂)
      letI : Finite (K.field.toSubgroup ⧸ extensionSubgroup K.field S₁ hS₁K) :=
        D.frobeniusFixedField_finite KR L hLK σ₁
      letI : Finite (K.field.toSubgroup ⧸ extensionSubgroup K.field S₂ hS₂K) :=
        D.frobeniusFixedField_finite KR L hLK σ₂
      letI : Finite (K.field.toSubgroup ⧸ extensionSubgroup K.field S₃ hS₃K) :=
        D.frobeniusFixedField_finite KR L hLK (σ₁ * σ₂)
      D.maximalUnramifiedNormClass A K.field L
          (relativeNorm A K.field S₁ hS₁K π₁) +
        D.maximalUnramifiedNormClass A K.field L
          (relativeNorm A K.field S₂ hS₂K π₂) =
        D.maximalUnramifiedNormClass A K.field L
          (relativeNorm A K.field S₃ hS₃K π₃)) :
    D.reciprocityMap A v K L hLK (σ₁ * σ₂) =
      D.reciprocityMap A v K L hLK σ₁ +
        D.reciprocityMap A v K L hLK σ₂ := by
  let KR := K.toFiniteResidueAbstractField D
  let hLnormalKR : (extensionSubgroup KR.field L hLK).Normal := by
    simpa only [KR, FiniteAbstractField.toFiniteResidueAbstractField] using hLnormal
  let hLfiniteKR : Finite
      (KR.field.toSubgroup ⧸ extensionSubgroup KR.field L hLK) := by
    simpa only [KR, FiniteAbstractField.toFiniteResidueAbstractField] using hLfinite
  let hS₁finite : Finite (K.field.toSubgroup ⧸ extensionSubgroup K.field
      (D.frobeniusFixedField KR L hLK σ₁)
      (D.frobeniusFixedField_le KR L hLK σ₁)) :=
    D.frobeniusFixedField_finite KR L hLK σ₁
  let hS₂finite : Finite (K.field.toSubgroup ⧸ extensionSubgroup K.field
      (D.frobeniusFixedField KR L hLK σ₂)
      (D.frobeniusFixedField_le KR L hLK σ₂)) :=
    D.frobeniusFixedField_finite KR L hLK σ₂
  let hS₃finite : Finite (K.field.toSubgroup ⧸ extensionSubgroup K.field
      (D.frobeniusFixedField KR L hLK (σ₁ * σ₂))
      (D.frobeniusFixedField_le KR L hLK (σ₁ * σ₂))) :=
    D.frobeniusFixedField_finite KR L hLK (σ₁ * σ₂)
  have h₁ := D.reciprocityValueOfPrime_eq_reciprocityMap
    A v hAxiom K L hLK σ₁ π₁ hπ₁
  have h₂ := D.reciprocityValueOfPrime_eq_reciprocityMap
    A v hAxiom K L hLK σ₂ π₂ hπ₂
  have h₃ := D.reciprocityValueOfPrime_eq_reciprocityMap
    A v hAxiom K L hLK (σ₁ * σ₂) π₃ hπ₃
  rw [← h₃, ← h₁, ← h₂]
  simpa only [reciprocityValueOfPrime, KR,
    FiniteAbstractField.toFiniteResidueAbstractField] using hclasses.symm

end DegreeData

end

end ClassFormation
