/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.MainMultiplicativity.PrimeUnitDifferences
/-!
# Finite-stage correction terms for reciprocity multiplicativity

This file proves that the alternating Frobenius power sum and each coefficient
of the three-term correction identity are genuine finite-stage units.
-/

universe u

namespace ClassFormation

open KummerTheory
open CyclicCohomology

noncomputable section

open CategoryTheory

variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- The alternating Frobenius power sum used in multiplicativity is a genuine
finite-stage unit. Splitting the long sum into two blocks expresses it as
power sums of differences of prime elements. -/
theorem frobeniusPowerSum_alternating_mem_infiniteUnitAddSubgroup
    (D : DegreeData G) (A : Rep ℤ G) (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    [hLfinite : Finite (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (φ σ₁ σ₂ : D.FrobeniusElements
      (K.toFiniteResidueAbstractField D) L hLK)
    (π₁ : ambientFixedAddSubgroup A
      (D.frobeniusFixedField (K.toFiniteResidueAbstractField D) L hLK σ₁))
    (π₃ : ambientFixedAddSubgroup A
      (D.frobeniusFixedField (K.toFiniteResidueAbstractField D) L hLK
        (σ₁ * σ₂)))
    (π₄ : ambientFixedAddSubgroup A
      (D.frobeniusFixedField (K.toFiniteResidueAbstractField D) L hLK
        (D.frobeniusActionConjugate (K.toFiniteResidueAbstractField D)
          L hLK φ σ₂
          (D.frobeniusExponent (K.toFiniteResidueAbstractField D)
            L hLK σ₁))))
    (hπ₁ :
      let KR := K.toFiniteResidueAbstractField D
      let Sigma1 : FiniteAbstractField G :=
        ⟨D.frobeniusFixedField KR L hLK σ₁,
          D.frobeniusFixedField_absoluteFinite K L hLK σ₁⟩
      v.IsPrimeElement Sigma1 π₁)
    (hπ₃ :
      let KR := K.toFiniteResidueAbstractField D
      let Sigma3 : FiniteAbstractField G :=
        ⟨D.frobeniusFixedField KR L hLK (σ₁ * σ₂),
          D.frobeniusFixedField_absoluteFinite K L hLK (σ₁ * σ₂)⟩
      v.IsPrimeElement Sigma3 π₃)
    (hπ₄ :
      let KR := K.toFiniteResidueAbstractField D
      let σ₄ := D.frobeniusActionConjugate KR L hLK φ σ₂
        (D.frobeniusExponent KR L hLK σ₁)
      let Sigma4 : FiniteAbstractField G :=
        ⟨D.frobeniusFixedField KR L hLK σ₄,
          D.frobeniusFixedField_absoluteFinite K L hLK σ₄⟩
      v.IsPrimeElement Sigma4 π₄) :
    let KR := K.toFiniteResidueAbstractField D
    let σ₃ := σ₁ * σ₂
    let σ₄ := D.frobeniusActionConjugate KR L hLK φ σ₂
      (D.frobeniusExponent KR L hLK σ₁)
    let p₁ := fixedFieldInclusion A
      (D.frobeniusFixedField KR L hLK σ₁)
      (D.maximalUnramifiedField L)
      (D.fieldInertia_le_frobeniusFixedField KR L hLK σ₁) π₁
    let p₃ := fixedFieldInclusion A
      (D.frobeniusFixedField KR L hLK σ₃)
      (D.maximalUnramifiedField L)
      (D.fieldInertia_le_frobeniusFixedField KR L hLK σ₃) π₃
    let p₄ := fixedFieldInclusion A
      (D.frobeniusFixedField KR L hLK σ₄)
      (D.maximalUnramifiedField L)
      (D.fieldInertia_le_frobeniusFixedField KR L hLK σ₄) π₄
    let u := D.frobeniusPowerSum A KR.field L hLK φ.1
        (D.frobeniusExponent KR L hLK σ₄) p₄ +
      D.frobeniusPowerSum A KR.field L hLK φ.1
        (D.frobeniusExponent KR L hLK σ₁) p₁ -
      D.frobeniusPowerSum A KR.field L hLK φ.1
        (D.frobeniusExponent KR L hLK σ₃) p₃
    u ∈ v.infiniteUnitAddSubgroup (D.maximalUnramifiedField L) K
      (D.maximalUnramifiedField_le_of_le hLK) := by
  dsimp only
  let KR := K.toFiniteResidueAbstractField D
  let hLnormalKR : (extensionSubgroup KR.field L hLK).Normal := by
    simpa only [KR, FiniteAbstractField.toFiniteResidueAbstractField] using hLnormal
  let hLfiniteKR : Finite
      (KR.field.toSubgroup ⧸ extensionSubgroup KR.field L hLK) := by
    simpa only [KR, FiniteAbstractField.toFiniteResidueAbstractField] using hLfinite
  let σ₃ := σ₁ * σ₂
  let σ₄ := D.frobeniusActionConjugate KR L hLK φ σ₂
    (D.frobeniusExponent KR L hLK σ₁)
  let p₁ := fixedFieldInclusion A
    (D.frobeniusFixedField KR L hLK σ₁)
    (D.maximalUnramifiedField L)
    (D.fieldInertia_le_frobeniusFixedField KR L hLK σ₁) π₁
  let p₃ := fixedFieldInclusion A
    (D.frobeniusFixedField KR L hLK σ₃)
    (D.maximalUnramifiedField L)
    (D.fieldInertia_le_frobeniusFixedField KR L hLK σ₃) π₃
  let p₄ := fixedFieldInclusion A
    (D.frobeniusFixedField KR L hLK σ₄)
    (D.maximalUnramifiedField L)
    (D.fieldInertia_le_frobeniusFixedField KR L hLK σ₄) π₄
  let n₁ := D.frobeniusExponent KR L hLK σ₁
  let n₃ := D.frobeniusExponent KR L hLK σ₃
  let n₄ := D.frobeniusExponent KR L hLK σ₄
  let U := v.infiniteUnitAddSubgroup (D.maximalUnramifiedField L) K
    (D.maximalUnramifiedField_le_of_le hLK)
  have h₄₃ : p₄ - p₃ ∈ U := by
    exact D.frobeniusPrimeDifference_mem_infiniteUnitAddSubgroup
      A v K L hLK σ₄ σ₃ π₄ π₃ hπ₄ hπ₃
  have h₁₃ : p₁ - p₃ ∈ U := by
    exact D.frobeniusPrimeDifference_mem_infiniteUnitAddSubgroup
      A v K L hLK σ₁ σ₃ π₁ π₃ hπ₁ hπ₃
  have h₃action : p₃ - D.frobeniusQuotientAction A KR.field L hLK
      (φ.1 ^ n₄) p₃ ∈ U := by
    exact D.frobeniusPrime_actionDifference_mem_infiniteUnitAddSubgroup
      A v K L hLK σ₃ π₃ hπ₃ (φ.1 ^ n₄)
  have h₁shift : p₁ - D.frobeniusQuotientAction A KR.field L hLK
      (φ.1 ^ n₄) p₃ ∈ U := by
    have heq : p₁ - D.frobeniusQuotientAction A KR.field L hLK
        (φ.1 ^ n₄) p₃ = (p₁ - p₃) +
          (p₃ - D.frobeniusQuotientAction A KR.field L hLK
            (φ.1 ^ n₄) p₃) := by
      abel
    rw [heq]
    exact U.add_mem h₁₃ h₃action
  have hn₃ : n₃ = n₄ + n₁ := by
    simp [n₁, n₃, n₄, σ₃, σ₄, Nat.add_comm]
  let u := D.frobeniusPowerSum A KR.field L hLK φ.1 n₄ p₄ +
    D.frobeniusPowerSum A KR.field L hLK φ.1 n₁ p₁ -
    D.frobeniusPowerSum A KR.field L hLK φ.1 n₃ p₃
  have huEq : u =
      D.frobeniusPowerSum A KR.field L hLK φ.1 n₄ (p₄ - p₃) +
      D.frobeniusPowerSum A KR.field L hLK φ.1 n₁
        (p₁ - D.frobeniusQuotientAction A KR.field L hLK
          (φ.1 ^ n₄) p₃) := by
    dsimp [u]
    rw [D.frobeniusPowerSum_sub_universalNormDescent,
      D.frobeniusPowerSum_sub_universalNormDescent, hn₃,
      D.frobeniusPowerSum_add]
    abel
  have hsum₄₃ : D.frobeniusPowerSum A KR.field L hLK φ.1 n₄
      (p₄ - p₃) ∈ U :=
    v.frobeniusPowerSum_mem_infiniteUnit_universalNormDescent
      K L hLK φ.1 n₄ (p₄ - p₃) h₄₃
  have hsum₁ : D.frobeniusPowerSum A KR.field L hLK φ.1 n₁
      (p₁ - D.frobeniusQuotientAction A KR.field L hLK
        (φ.1 ^ n₄) p₃) ∈ U :=
    v.frobeniusPowerSum_mem_infiniteUnit_universalNormDescent
      K L hLK φ.1 n₁ _ h₁shift
  rw [show D.frobeniusPowerSum A KR.field L hLK φ.1 n₄ p₄ +
      D.frobeniusPowerSum A KR.field L hLK φ.1 n₁ p₁ -
      D.frobeniusPowerSum A KR.field L hLK φ.1 n₃ p₃ = u from rfl,
    huEq]
  exact U.add_mem hsum₄₃ hsum₁

/-- Each of the three correction coefficients in the group-ring
identity is a finite-stage unit.  In the left-action translation the
product is `τ₄τ₁`, so the third coefficient is `p₃-τ₁p₃`; it is
acted on by `τ₄` in `frobeniusMultiplicativityCorrectionAction`. -/
theorem frobeniusCorrectionTerms_mem_infiniteUnitAddSubgroup
    (D : DegreeData G) (A : Rep ℤ G) (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    [hLfinite : Finite (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (φ σ₁ σ₂ : D.FrobeniusElements
      (K.toFiniteResidueAbstractField D) L hLK)
    (π₁ : ambientFixedAddSubgroup A
      (D.frobeniusFixedField (K.toFiniteResidueAbstractField D) L hLK σ₁))
    (π₃ : ambientFixedAddSubgroup A
      (D.frobeniusFixedField (K.toFiniteResidueAbstractField D) L hLK
        (σ₁ * σ₂)))
    (π₄ : ambientFixedAddSubgroup A
      (D.frobeniusFixedField (K.toFiniteResidueAbstractField D) L hLK
        (D.frobeniusActionConjugate (K.toFiniteResidueAbstractField D)
          L hLK φ σ₂
          (D.frobeniusExponent (K.toFiniteResidueAbstractField D)
            L hLK σ₁))))
    (hπ₁ :
      let KR := K.toFiniteResidueAbstractField D
      let Sigma1 : FiniteAbstractField G :=
        ⟨D.frobeniusFixedField KR L hLK σ₁,
          D.frobeniusFixedField_absoluteFinite K L hLK σ₁⟩
      v.IsPrimeElement Sigma1 π₁)
    (hπ₃ :
      let KR := K.toFiniteResidueAbstractField D
      let Sigma3 : FiniteAbstractField G :=
        ⟨D.frobeniusFixedField KR L hLK (σ₁ * σ₂),
          D.frobeniusFixedField_absoluteFinite K L hLK (σ₁ * σ₂)⟩
      v.IsPrimeElement Sigma3 π₃)
    (hπ₄ :
      let KR := K.toFiniteResidueAbstractField D
      let σ₄ := D.frobeniusActionConjugate KR L hLK φ σ₂
        (D.frobeniusExponent KR L hLK σ₁)
      let Sigma4 : FiniteAbstractField G :=
        ⟨D.frobeniusFixedField KR L hLK σ₄,
          D.frobeniusFixedField_absoluteFinite K L hLK σ₄⟩
      v.IsPrimeElement Sigma4 π₄) :
    let KR := K.toFiniteResidueAbstractField D
    let σ₃ := σ₁ * σ₂
    let σ₄ := D.frobeniusActionConjugate KR L hLK φ σ₂
      (D.frobeniusExponent KR L hLK σ₁)
    let p₁ := fixedFieldInclusion A
      (D.frobeniusFixedField KR L hLK σ₁)
      (D.maximalUnramifiedField L)
      (D.fieldInertia_le_frobeniusFixedField KR L hLK σ₁) π₁
    let p₃ := fixedFieldInclusion A
      (D.frobeniusFixedField KR L hLK σ₃)
      (D.maximalUnramifiedField L)
      (D.fieldInertia_le_frobeniusFixedField KR L hLK σ₃) π₃
    let p₄ := fixedFieldInclusion A
      (D.frobeniusFixedField KR L hLK σ₄)
      (D.maximalUnramifiedField L)
      (D.fieldInertia_le_frobeniusFixedField KR L hLK σ₄) π₄
    let τ₁ := D.frobeniusActionRemainder KR L hLK φ σ₁
    ∀ i : Fin 3,
      (![p₄ - p₃, p₁ - p₃,
          p₃ - D.frobeniusQuotientAction A KR.field L hLK τ₁ p₃] :
        Fin 3 → ambientFixedAddSubgroup A
          (D.maximalUnramifiedField L)) i ∈
        v.infiniteUnitAddSubgroup (D.maximalUnramifiedField L) K
      (D.maximalUnramifiedField_le_of_le hLK) := by
  dsimp only
  let KR := K.toFiniteResidueAbstractField D
  let hLnormalKR : (extensionSubgroup KR.field L hLK).Normal := by
    simpa only [KR, FiniteAbstractField.toFiniteResidueAbstractField] using hLnormal
  let hLfiniteKR : Finite
      (KR.field.toSubgroup ⧸ extensionSubgroup KR.field L hLK) := by
    simpa only [KR, FiniteAbstractField.toFiniteResidueAbstractField] using hLfinite
  let σ₃ := σ₁ * σ₂
  let σ₄ := D.frobeniusActionConjugate KR L hLK φ σ₂
    (D.frobeniusExponent KR L hLK σ₁)
  let p₁ := fixedFieldInclusion A
    (D.frobeniusFixedField KR L hLK σ₁)
    (D.maximalUnramifiedField L)
    (D.fieldInertia_le_frobeniusFixedField KR L hLK σ₁) π₁
  let p₃ := fixedFieldInclusion A
    (D.frobeniusFixedField KR L hLK σ₃)
    (D.maximalUnramifiedField L)
    (D.fieldInertia_le_frobeniusFixedField KR L hLK σ₃) π₃
  let p₄ := fixedFieldInclusion A
    (D.frobeniusFixedField KR L hLK σ₄)
    (D.maximalUnramifiedField L)
    (D.fieldInertia_le_frobeniusFixedField KR L hLK σ₄) π₄
  let τ₁ := D.frobeniusActionRemainder KR L hLK φ σ₁
  have h₄₃ := D.frobeniusPrimeDifference_mem_infiniteUnitAddSubgroup
    A v K L hLK σ₄ σ₃ π₄ π₃ hπ₄ hπ₃
  have h₁₃ := D.frobeniusPrimeDifference_mem_infiniteUnitAddSubgroup
    A v K L hLK σ₁ σ₃ π₁ π₃ hπ₁ hπ₃
  have h₃action :=
    D.frobeniusPrime_actionDifference_mem_infiniteUnitAddSubgroup
      A v K L hLK σ₃ π₃ hπ₃ τ₁
  intro i
  fin_cases i
  · change p₄ - p₃ ∈ _
    exact h₄₃
  · change p₁ - p₃ ∈ _
    exact h₁₃
  · change p₃ - D.frobeniusQuotientAction A KR.field L hLK τ₁ p₃ ∈ _
    exact h₃action


end DegreeData

end

end ClassFormation
