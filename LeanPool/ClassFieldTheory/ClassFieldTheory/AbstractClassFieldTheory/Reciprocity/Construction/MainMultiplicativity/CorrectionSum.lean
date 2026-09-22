/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.MainMultiplicativity.FrobeniusActionRemainder
/-!
# Correction sums for reciprocity multiplicativity

This file packages the three correction coefficients and action elements,
proves their degree-zero property, and identifies their action-difference sum.
-/

universe u

namespace ClassFormation

open KummerTheory
open CyclicCohomology

noncomputable section

open CategoryTheory
open scoped BigOperators

/-- Correction coefficients in the order produced by the left-action
translation of the Frobenius multiplicativity identity. -/
def frobeniusMultiplicativityCorrectionTerm
    {R : IntegralRepGroupType} [Group R]
    (B : Rep ℤ R) (τ₁ : R) (p₁ p₃ p₄ : B.V) : Fin 3 → B.V :=
  ![p₄ - p₃, p₁ - p₃, p₃ - B.ρ τ₁ p₃]

/-- The corresponding left-action elements are `τ₄,τ₁,τ₄`.
The last action is `τ₄` because the product in the actual `(*)`
identity is `τ₄τ₁`. -/
def frobeniusMultiplicativityCorrectionAction {R : Type*}
    (τ₁ τ₄ : R) : Fin 3 → R :=
  ![τ₄, τ₁, τ₄]

section correctionActionDegrees

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- All three actual correction actions have normalized degree zero, as
required by the universal norm-descent lemma. -/
theorem frobeniusMultiplicativityCorrectionAction_mem_degreeKernel
    (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (φ σ₁ σ₂ : D.FrobeniusElements K L hLK)
    (hφ : D.frobeniusExponent K L hLK φ = 1) :
    let σ₄ := D.frobeniusActionConjugate K L hLK φ σ₂
      (D.frobeniusExponent K L hLK σ₁)
    let τ₁ := D.frobeniusActionRemainder K L hLK φ σ₁
    let τ₄ := D.frobeniusActionRemainder K L hLK φ σ₄
    ∀ i : Fin 3,
      frobeniusMultiplicativityCorrectionAction τ₁ τ₄ i ∈
        (D.extensionNormalizedDegreeContinuous K L hLK).toMonoidHom.ker := by
  dsimp only
  let σ₄ := D.frobeniusActionConjugate K L hLK φ σ₂
    (D.frobeniusExponent K L hLK σ₁)
  let τ₁ := D.frobeniusActionRemainder K L hLK φ σ₁
  let τ₄ := D.frobeniusActionRemainder K L hLK φ σ₄
  have hτ₁ := D.frobeniusActionRemainder_mem_degreeKernel
    K L hLK φ σ₁ hφ
  have hτ₄ := D.frobeniusActionRemainder_mem_degreeKernel
    K L hLK φ σ₄ hφ
  intro i
  fin_cases i
  · exact hτ₄
  · exact hτ₁
  · exact hτ₄

end DegreeData

end correctionActionDegrees

/-- Explicit left-action form of the group-ring identity, with the factor
order and the first two terms arranged as they occur in `(*)`. -/
theorem frobeniusMultiplicativity_actionDifference_eq_correctionSum
    {R : IntegralRepGroupType} [Group R] (B : Rep ℤ R)
    (τ₁ τ₄ : R) (p₁ p₃ p₄ : B.V) :
    (B.ρ τ₄ p₄ - p₄) + (B.ρ τ₁ p₁ - p₁) +
        (p₃ - B.ρ (τ₄ * τ₁) p₃) =
      ∑ i : Fin 3,
        (B.ρ (frobeniusMultiplicativityCorrectionAction τ₁ τ₄ i)
          (frobeniusMultiplicativityCorrectionTerm B τ₁ p₁ p₃ p₄ i) -
          frobeniusMultiplicativityCorrectionTerm B τ₁ p₁ p₃ p₄ i) := by
  have hmul : B.ρ (τ₄ * τ₁) p₃ = B.ρ τ₄ (B.ρ τ₁ p₃) := by
    rw [map_mul]
    rfl
  rw [hmul]
  simp [frobeniusMultiplicativityCorrectionAction,
    frobeniusMultiplicativityCorrectionTerm, Fin.sum_univ_succ, map_sub]
  abel

end

end ClassFormation
