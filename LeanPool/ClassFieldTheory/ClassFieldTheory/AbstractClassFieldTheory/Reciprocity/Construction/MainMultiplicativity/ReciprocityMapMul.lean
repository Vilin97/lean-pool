/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.MainMultiplicativity.ConjugatePrimeNorm
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.MainMultiplicativity.FrobeniusPowerSumRelation
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.MainMultiplicativity.NormClassRelation
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.MainMultiplicativity.FiniteStageCorrections
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.MainMultiplicativity.CorrectionSum
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.ChosenDegreeOneFrobenius
/-!
# Multiplicativity of the abstract reciprocity map

This file assembles the Frobenius conjugation, finite-stage unit, correction
sum, and universal norm-descent results into reciprocity-map multiplicativity.
-/

@[expose] public section

universe u

namespace ClassFormation

open KummerTheory
open CyclicCohomology

noncomputable section

open CategoryTheory
open scoped BigOperators

section reciprocityMapMultiplicativity

/-!
Mathlib's `Rep ℤ G` requires its coefficient ring and acting group in the
same universe, so this representation-bearing portion has `G : IntegralRepGroupType`.
-/
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- **reciprocity multiplicativity.** The reciprocity function is multiplicative on
Frobenius elements (written additively on the norm-class quotient).

This is the endpoint of the calculation: the
group-ring identity `(*)` supplies the hypothesis of the universal norm-descent lemma, whose
universal-unit norm descends the resulting norm relation to `K`. -/
theorem reciprocityMap_mul
    (D : DegreeData G) (A : Rep ℤ G) (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D)
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    [hLfinite : Finite (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (sigma1 sigma2 : D.FrobeniusElements
      (K.toFiniteResidueAbstractField D) L hLK) :
    D.reciprocityMap A v K L hLK (sigma1 * sigma2) =
      D.reciprocityMap A v K L hLK sigma1 +
        D.reciprocityMap A v K L hLK sigma2 := by
  let KR := K.toFiniteResidueAbstractField D
  let hLnormalKR : (extensionSubgroup KR.field L hLK).Normal := by
    simpa only [KR, FiniteAbstractField.toFiniteResidueAbstractField] using hLnormal
  let hLfiniteKR : Finite
      (KR.field.toSubgroup ⧸ extensionSubgroup KR.field L hLK) := by
    simpa only [KR, FiniteAbstractField.toFiniteResidueAbstractField] using hLfinite
  let phi := D.chosenDegreeOneFrobeniusElement KR L hLK
  have hphi : D.frobeniusExponent KR L hLK phi = 1 :=
    D.frobeniusExponent_chosenDegreeOneFrobeniusElement KR L hLK
  let sigma3 := sigma1 * sigma2
  let m := D.frobeniusExponent KR L hLK sigma1
  let sigma4 := D.frobeniusActionConjugate KR L hLK phi sigma2 m
  let S1 := D.frobeniusFixedField KR L hLK sigma1
  let S2 := D.frobeniusFixedField KR L hLK sigma2
  let S3 := D.frobeniusFixedField KR L hLK sigma3
  let S4 := D.frobeniusFixedField KR L hLK sigma4
  let hS1K := D.frobeniusFixedField_le KR L hLK sigma1
  let hS2K := D.frobeniusFixedField_le KR L hLK sigma2
  let hS3K := D.frobeniusFixedField_le KR L hLK sigma3
  let hS4K := D.frobeniusFixedField_le KR L hLK sigma4
  let hS1finite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field S1 hS1K) :=
    D.frobeniusFixedField_finite KR L hLK sigma1
  let hS2finite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field S2 hS2K) :=
    D.frobeniusFixedField_finite KR L hLK sigma2
  let hS3finite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field S3 hS3K) :=
    D.frobeniusFixedField_finite KR L hLK sigma3
  let hS4finite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field S4 hS4K) :=
    D.frobeniusFixedField_finite KR L hLK sigma4
  let hS1absolute : Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) S1 (le_baseField S1)) :=
    D.frobeniusFixedField_absoluteFinite K L hLK sigma1
  let hS2absolute : Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) S2 (le_baseField S2)) :=
    D.frobeniusFixedField_absoluteFinite K L hLK sigma2
  let hS3absolute : Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) S3 (le_baseField S3)) :=
    D.frobeniusFixedField_absoluteFinite K L hLK sigma3
  let hS4absolute : Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) S4 (le_baseField S4)) :=
    D.frobeniusFixedField_absoluteFinite K L hLK sigma4
  let Sigma1 : FiniteAbstractField G := ⟨S1, hS1absolute⟩
  let Sigma2 : FiniteAbstractField G := ⟨S2, hS2absolute⟩
  let Sigma3 : FiniteAbstractField G := ⟨S3, hS3absolute⟩
  let pi1 : ambientFixedAddSubgroup A S1 := by
    simpa [Sigma1] using v.chosenPrimeElement Sigma1
  let pi2 : ambientFixedAddSubgroup A S2 := by
    simpa [Sigma2] using v.chosenPrimeElement Sigma2
  let pi3 : ambientFixedAddSubgroup A S3 := by
    simpa [Sigma3] using v.chosenPrimeElement Sigma3
  have hpi1 : v.IsPrimeElement Sigma1 pi1 := by
    simpa [Sigma1, pi1] using v.chosenPrimeElement_isPrime Sigma1
  have hpi2 : v.IsPrimeElement Sigma2 pi2 := by
    simpa [Sigma2, pi2] using v.chosenPrimeElement_isPrime Sigma2
  have hpi3 : v.IsPrimeElement Sigma3 pi3 := by
    simpa [Sigma3, pi3] using v.chosenPrimeElement_isPrime Sigma3
  obtain ⟨pi4, hpi4, hnorm42⟩ :=
    D.exists_primeElement_frobeniusActionConjugate_norm_eq A v K L hLK
      phi sigma2 m pi2 hpi2
  let E := D.maximalUnramifiedField L
  let I := D.maximalUnramifiedField KR.field
  let hEI := D.maximalUnramifiedField_mono hLK
  let p1 := fixedFieldInclusion A S1 E
    (D.fieldInertia_le_frobeniusFixedField KR L hLK sigma1) pi1
  let p3 := fixedFieldInclusion A S3 E
    (D.fieldInertia_le_frobeniusFixedField KR L hLK sigma3) pi3
  let p4 := fixedFieldInclusion A S4 E
    (D.fieldInertia_le_frobeniusFixedField KR L hLK sigma4) pi4
  let u := D.frobeniusPowerSum A KR.field L hLK phi.1
        (D.frobeniusExponent KR L hLK sigma4) p4 +
      D.frobeniusPowerSum A KR.field L hLK phi.1
        (D.frobeniusExponent KR L hLK sigma1) p1 -
      D.frobeniusPowerSum A KR.field L hLK phi.1
        (D.frobeniusExponent KR L hLK sigma3) p3
  let tau1 := D.frobeniusActionRemainder KR L hLK phi sigma1
  let tau4 := D.frobeniusActionRemainder KR L hLK phi sigma4
  let B := D.frobeniusQuotientRepresentation A KR.field L hLK
  let correction : Fin 3 → ambientFixedAddSubgroup A E :=
    frobeniusMultiplicativityCorrectionTerm B tau1 p1 p3 p4
  have hcorrectionMem : ∀ i : Fin 3,
      correction i ∈ v.infiniteUnitAddSubgroup E K
        (D.maximalUnramifiedField_le_of_le hLK) := by
    have hmem :=
      D.frobeniusCorrectionTerms_mem_infiniteUnitAddSubgroup
        A v K L hLK phi sigma1 sigma2 pi1 pi3 pi4 hpi1 hpi3 hpi4
    change ∀ i : Fin 3,
      (![p4 - p3, p1 - p3,
          p3 - D.frobeniusQuotientAction A KR.field L hLK tau1 p3] :
        Fin 3 → ambientFixedAddSubgroup A E) i ∈
          v.infiniteUnitAddSubgroup E K
            (D.maximalUnramifiedField_le_of_le hLK)
    change ∀ i : Fin 3,
      (![p4 - p3, p1 - p3,
          p3 - D.frobeniusQuotientAction A KR.field L hLK tau1 p3] :
        Fin 3 → ambientFixedAddSubgroup A E) i ∈
          v.infiniteUnitAddSubgroup E K
            (D.maximalUnramifiedField_le_of_le hLK) at hmem
    exact hmem
  have huMem : u ∈ v.infiniteUnitAddSubgroup E K
      (D.maximalUnramifiedField_le_of_le hLK) := by
    simpa [u, p1, p3, p4, E, S1, S3, S4, sigma3, sigma4, m,
      pi1, pi3] using
      D.frobeniusPowerSum_alternating_mem_infiniteUnitAddSubgroup
        A v K L hLK phi sigma1 sigma2 pi1 pi3 pi4 hpi1 hpi3 hpi4
  have hactionMem :=
    D.frobeniusMultiplicativityCorrectionAction_mem_degreeKernel
      KR L hLK phi sigma1 sigma2 hphi
  let tau : Fin 3 →
      (D.extensionNormalizedDegreeContinuous KR L hLK).toMonoidHom.ker :=
    fun i ↦ ⟨frobeniusMultiplicativityCorrectionAction tau1 tau4 i, by
      simpa [tau1, tau4, sigma4, m] using hactionMem i⟩
  let uU : v.infiniteUnitAddSubgroup E K
      (D.maximalUnramifiedField_le_of_le hLK) := ⟨u, huMem⟩
  let uiU : Fin 3 → v.infiniteUnitAddSubgroup E K
      (D.maximalUnramifiedField_le_of_le hLK) :=
    fun i ↦ ⟨correction i, hcorrectionMem i⟩
  have hraw := D.frobeniusPowerSum_mul_action_sub A KR L hLK
    phi sigma1 sigma2 pi1 pi3 pi4
  have hdiff :=
    frobeniusMultiplicativity_actionDifference_eq_correctionSum
      B tau1 tau4 p1 p3 p4
  change
      (D.frobeniusQuotientAction A KR.field L hLK tau4 p4 - p4) +
          (D.frobeniusQuotientAction A KR.field L hLK tau1 p1 - p1) +
        (p3 - D.frobeniusQuotientAction A KR.field L hLK (tau4 * tau1) p3) =
      ∑ i : Fin 3,
        (D.frobeniusQuotientAction A KR.field L hLK
            (frobeniusMultiplicativityCorrectionAction tau1 tau4 i)
            (correction i) - correction i) at hdiff
  have hstar :
      D.frobeniusQuotientAction A KR.field L hLK phi.1 uU.1 - uU.1 =
        ∑ i ∈ (Finset.univ : Finset (Fin 3)),
          (D.frobeniusQuotientAction A KR.field L hLK (tau i).1 (uiU i).1 -
            (uiU i).1) := by
    change D.frobeniusQuotientAction A KR.field L hLK phi.1 u - u = _
    rw [show D.frobeniusQuotientAction A KR.field L hLK phi.1 u - u =
      (D.frobeniusQuotientAction A KR.field L hLK tau4 p4 - p4) +
      (D.frobeniusQuotientAction A KR.field L hLK tau1 p1 - p1) +
      (p3 - D.frobeniusQuotientAction A KR.field L hLK (tau4 * tau1) p3) by
        simpa [u, p1, p3, p4, tau1, tau4, sigma3, sigma4, m,
          E, S1, S3, S4, pi1, pi3] using hraw]
    simpa only [tau, uiU, correction, B,
      D.frobeniusQuotientRepresentation_apply] using hdiff
  let hIfinite : Finite
      (I.toSubgroup ⧸ extensionSubgroup I E hEI) :=
    D.maximalUnramifiedExtension_finite KR.field L hLK
  obtain ⟨aK, haKdescend, haKunitNorm⟩ :=
    v.universalNormDescent hAxiom K L hLK phi hphi
      (Finset.univ : Finset (Fin 3)) tau uU uiU hstar
  have haKnormRaw : aK.1 ∈ infiniteNormSubgroup A E K.field :=
    v.infiniteUnitNormSubgroup_le_normSubgroup E K haKunitNorm
  let r1 := relativeNorm A K.field S1 hS1K pi1
  let r2 := relativeNorm A K.field S2 hS2K pi2
  let r3 := relativeNorm A K.field S3 hS3K pi3
  let r4 := relativeNorm A K.field S4 hS4K pi4
  have hnormu := D.relativeNorm_frobeniusPowerSum_alternating A KR L hLK
    phi sigma1 sigma2 hphi pi1 pi3 pi4
  have hclasses41 :
      D.maximalUnramifiedNormClass A K.field L r4 +
        D.maximalUnramifiedNormClass A K.field L r1 =
          D.maximalUnramifiedNormClass A K.field L r3 := by
    apply D.maximalUnramifiedNormClass_add_eq_of_relativeNorm A KR L hLK
      r4 r1 r3 u hnormu
    refine ⟨aK.1, haKdescend, ?_⟩
    exact (D.mem_maximalUnramifiedNormSubgroup_iff A K.field L aK.1).2 (by
      simpa only [E] using haKnormRaw)
  have hclasses12 :
      D.maximalUnramifiedNormClass A K.field L r1 +
        D.maximalUnramifiedNormClass A K.field L r2 =
          D.maximalUnramifiedNormClass A K.field L r3 := by
    have hr42 : r4 = r2 := by
      simpa [r4, r2, S4, S2, sigma4, m] using hnorm42
    rw [← hr42, add_comm]
    exact hclasses41
  apply D.reciprocityMap_mul_of_primeNormClass_eq
    A v hAxiom K L hLK sigma1 sigma2 pi1 pi2 pi3
      hpi1 hpi2 hpi3
  simpa [r1, r2, r3, E, S1, S2, S3, sigma3, pi1, pi2, pi3]
    using hclasses12

end DegreeData
end reciprocityMapMultiplicativity

end

end ClassFormation
