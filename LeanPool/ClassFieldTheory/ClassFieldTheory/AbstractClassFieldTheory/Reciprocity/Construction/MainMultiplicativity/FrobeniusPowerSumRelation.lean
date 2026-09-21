/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.MainMultiplicativity.FrobeniusActionRemainder
/-!
# The Frobenius power-sum relation for reciprocity multiplicativity

This file proves the three-term action identity obtained from the Frobenius
action remainders and their associated fixed-field prime elements.
-/

universe u

namespace ClassFormation

open KummerTheory
open CyclicCohomology

noncomputable section

open CategoryTheory

variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- The three Frobenius power sums attached to `σ₁`, `σ₁σ₂`, and the
left-action conjugate of `σ₂` satisfy the action-difference relation used by
universal norm descent. -/
theorem frobeniusPowerSum_mul_action_sub (D : DegreeData G) (A : Rep ℤ G)
    [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (φ σ₁ σ₂ : D.FrobeniusElements K L hLK)
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
    let p₁ := fixedFieldInclusion A
      (D.frobeniusFixedField K L hLK σ₁)
      (D.maximalUnramifiedField L)
      (D.fieldInertia_le_frobeniusFixedField K L hLK σ₁) π₁
    let p₃ := fixedFieldInclusion A
      (D.frobeniusFixedField K L hLK σ₃)
      (D.maximalUnramifiedField L)
      (D.fieldInertia_le_frobeniusFixedField K L hLK σ₃) π₃
    let p₄ := fixedFieldInclusion A
      (D.frobeniusFixedField K L hLK σ₄)
      (D.maximalUnramifiedField L)
      (D.fieldInertia_le_frobeniusFixedField K L hLK σ₄) π₄
    let τ₁ := D.frobeniusActionRemainder K L hLK φ σ₁
    let τ₄ := D.frobeniusActionRemainder K L hLK φ σ₄
    let u := D.frobeniusPowerSum A K.field L hLK φ.1
        (D.frobeniusExponent K L hLK σ₄) p₄ +
      D.frobeniusPowerSum A K.field L hLK φ.1
        (D.frobeniusExponent K L hLK σ₁) p₁ -
      D.frobeniusPowerSum A K.field L hLK φ.1
        (D.frobeniusExponent K L hLK σ₃) p₃
    D.frobeniusQuotientAction A K.field L hLK φ.1 u - u =
      (D.frobeniusQuotientAction A K.field L hLK τ₄ p₄ - p₄) +
      (D.frobeniusQuotientAction A K.field L hLK τ₁ p₁ - p₁) +
      (p₃ - D.frobeniusQuotientAction A K.field L hLK (τ₄ * τ₁) p₃) := by
  let σ₃ := σ₁ * σ₂
  let σ₄ := D.frobeniusActionConjugate K L hLK φ σ₂
    (D.frobeniusExponent K L hLK σ₁)
  let p₁ := fixedFieldInclusion A
    (D.frobeniusFixedField K L hLK σ₁)
    (D.maximalUnramifiedField L)
    (D.fieldInertia_le_frobeniusFixedField K L hLK σ₁) π₁
  let p₃ := fixedFieldInclusion A
    (D.frobeniusFixedField K L hLK σ₃)
    (D.maximalUnramifiedField L)
    (D.fieldInertia_le_frobeniusFixedField K L hLK σ₃) π₃
  let p₄ := fixedFieldInclusion A
    (D.frobeniusFixedField K L hLK σ₄)
    (D.maximalUnramifiedField L)
    (D.fieldInertia_le_frobeniusFixedField K L hLK σ₄) π₄
  let s₁ := D.frobeniusPowerSum A K.field L hLK φ.1
    (D.frobeniusExponent K L hLK σ₁) p₁
  let s₃ := D.frobeniusPowerSum A K.field L hLK φ.1
    (D.frobeniusExponent K L hLK σ₃) p₃
  let s₄ := D.frobeniusPowerSum A K.field L hLK φ.1
    (D.frobeniusExponent K L hLK σ₄) p₄
  let τ₁ := D.frobeniusActionRemainder K L hLK φ σ₁
  let τ₃ := D.frobeniusActionRemainder K L hLK φ σ₃
  let τ₄ := D.frobeniusActionRemainder K L hLK φ σ₄
  have h₁ :
      D.frobeniusQuotientAction A K.field L hLK τ₁ p₁ =
        D.frobeniusQuotientAction A K.field L hLK
          (φ.1 ^ D.frobeniusExponent K L hLK σ₁) p₁ := by
    exact D.frobeniusActionRemainder_apply_fixedField
      A K L hLK φ σ₁ π₁
  have h₃ :
      D.frobeniusQuotientAction A K.field L hLK τ₃ p₃ =
        D.frobeniusQuotientAction A K.field L hLK
          (φ.1 ^ D.frobeniusExponent K L hLK σ₃) p₃ := by
    exact D.frobeniusActionRemainder_apply_fixedField
      A K L hLK φ σ₃ π₃
  have h₄ :
      D.frobeniusQuotientAction A K.field L hLK τ₄ p₄ =
        D.frobeniusQuotientAction A K.field L hLK
          (φ.1 ^ D.frobeniusExponent K L hLK σ₄) p₄ := by
    exact D.frobeniusActionRemainder_apply_fixedField
      A K L hLK φ σ₄ π₄
  have hτ : τ₃ = τ₄ * τ₁ := by
    exact D.frobeniusActionRemainder_mul K L hLK φ σ₁ σ₂
  change
    D.frobeniusQuotientAction A K.field L hLK φ.1
          (s₄ + s₁ - s₃) - (s₄ + s₁ - s₃) =
      (D.frobeniusQuotientAction A K.field L hLK τ₄ p₄ - p₄) +
        (D.frobeniusQuotientAction A K.field L hLK τ₁ p₁ - p₁) +
        (p₃ -
          D.frobeniusQuotientAction A K.field L hLK (τ₄ * τ₁) p₃)
  have hmap :
      D.frobeniusQuotientAction A K.field L hLK φ.1 (s₄ + s₁ - s₃) =
        D.frobeniusQuotientAction A K.field L hLK φ.1 s₄ +
          D.frobeniusQuotientAction A K.field L hLK φ.1 s₁ -
          D.frobeniusQuotientAction A K.field L hLK φ.1 s₃ := by
    change
      D.frobeniusQuotientActionLinearMap A K.field L hLK φ.1
          (s₄ + s₁ - s₃) =
        D.frobeniusQuotientActionLinearMap A K.field L hLK φ.1 s₄ +
          D.frobeniusQuotientActionLinearMap A K.field L hLK φ.1 s₁ -
          D.frobeniusQuotientActionLinearMap A K.field L hLK φ.1 s₃
    rw [map_sub, map_add]
  rw [hmap]
  calc
    _ =
        (D.frobeniusQuotientAction A K.field L hLK φ.1 s₄ - s₄) +
          (D.frobeniusQuotientAction A K.field L hLK φ.1 s₁ - s₁) -
          (D.frobeniusQuotientAction A K.field L hLK φ.1 s₃ - s₃) := by
      abel
    _ =
        (D.frobeniusQuotientAction A K.field L hLK
            (φ.1 ^ D.frobeniusExponent K L hLK σ₄) p₄ - p₄) +
          (D.frobeniusQuotientAction A K.field L hLK
            (φ.1 ^ D.frobeniusExponent K L hLK σ₁) p₁ - p₁) -
          (D.frobeniusQuotientAction A K.field L hLK
            (φ.1 ^ D.frobeniusExponent K L hLK σ₃) p₃ - p₃) := by
      dsimp only [s₁, s₃, s₄]
      rw [D.frobeniusPowerSum_action_sub,
        D.frobeniusPowerSum_action_sub,
        D.frobeniusPowerSum_action_sub]
    _ =
        (D.frobeniusQuotientAction A K.field L hLK τ₄ p₄ - p₄) +
          (D.frobeniusQuotientAction A K.field L hLK τ₁ p₁ - p₁) +
          (p₃ -
            D.frobeniusQuotientAction A K.field L hLK (τ₄ * τ₁) p₃) := by
      rw [← h₄, ← h₁, ← h₃, hτ]
      abel

end DegreeData

end

end ClassFormation
