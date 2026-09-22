/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.PrincipalSubring

import Mathlib.Tactic.NormNum

/-!
# API checks for `P̂`

The two-grade fixture verifies that intrinsic `P̂` is an external direct sum rather than a single
space `P_α`: independently nonzero vectors in grades zero and one remain visible in exactly those
two homogeneous components. The embedding preserves both components and their grades.

A strictly negative monomial gives the decisive range separator. Its nonzero degree-zero
class lies in `RV̂`, but its image in the intrinsic ordinal-value component `P_0` is zero. Hence it
does
not belong to the principal graded subalgebra. This distinguishes LM24, Definition 6.1.1 from the
nearby wrong definition in which `P̂` is all of `RV̂`.
-/

universe v

public noncomputable section

namespace Tests

open scoped DirectSum HahnSeries NatOrdinal

variable {K : Type v} [Field K]

section TwoGrades

/-- A principal graded element with prescribed components in grades zero and one. -/
def principalTwoGradeElement (x₀ : Berarducci.PrincipalComponent K 0)
    (x₁ : Berarducci.PrincipalComponent K 1) :
    Berarducci.PrincipalSubring K :=
  DirectSum.of (Berarducci.PrincipalComponent K) 0 x₀ +
    DirectSum.of (Berarducci.PrincipalComponent K) 1 x₁

/-- The two-grade fixture has the prescribed components and vanishes in every other grade. -/
theorem principalTwoGradeElement_components (x₀ : Berarducci.PrincipalComponent K 0)
    (x₁ : Berarducci.PrincipalComponent K 1) :
    principalTwoGradeElement x₀ x₁ 0 = x₀ ∧
      principalTwoGradeElement x₀ x₁ 1 = x₁ ∧
      ∀ α, α ≠ 0 → α ≠ 1 → principalTwoGradeElement x₀ x₁ α = 0 := by
  constructor
  · simp [principalTwoGradeElement, DirectSum.of_apply]
  constructor
  · simp [principalTwoGradeElement, DirectSum.of_apply]
  · intro α hα0 hα1
    have h0α : (0 : NatOrdinal) ≠ α := Ne.symm hα0
    have h1α : (1 : NatOrdinal) ≠ α := Ne.symm hα1
    simp [principalTwoGradeElement, DirectSum.of_apply, h0α, h1α]

/-- Nonzero inputs remain independently visible in grades zero and one. -/
theorem principalTwoGradeElement_nonzero_components (x₀ : Berarducci.PrincipalComponent K 0)
    (x₁ : Berarducci.PrincipalComponent K 1)
    (hx₀ : x₀ ≠ 0) (hx₁ : x₁ ≠ 0) :
    principalTwoGradeElement x₀ x₁ 0 ≠ 0 ∧
      principalTwoGradeElement x₀ x₁ 1 ≠ 0 := by
  rw [(principalTwoGradeElement_components x₀ x₁).1,
    (principalTwoGradeElement_components x₀ x₁).2.1]
  exact ⟨hx₀, hx₁⟩

section Embedding

variable [CharZero K]

/-- The graded embedding preserves both prescribed components and their grades. -/
theorem principalTwoGradeElement_embedding_components (x₀ : Berarducci.PrincipalComponent K 0)
    (x₁ : Berarducci.PrincipalComponent K 1) :
    Berarducci.principalSubringEmbedding K
        (principalTwoGradeElement x₀ x₁) 0 =
      Berarducci.principalComponentToHahnDegreeLayer K 0 x₀ ∧
    Berarducci.principalSubringEmbedding K
        (principalTwoGradeElement x₀ x₁) 1 =
      Berarducci.principalComponentToHahnDegreeLayer K 1 x₁ ∧
    ∀ α, α ≠ 0 → α ≠ 1 →
      Berarducci.principalSubringEmbedding K
        (principalTwoGradeElement x₀ x₁) α = 0 := by
  simp only [Berarducci.principalSubringEmbedding_apply]
  rw [(principalTwoGradeElement_components x₀ x₁).1,
    (principalTwoGradeElement_components x₀ x₁).2.1]
  refine ⟨rfl, rfl, ?_⟩
  intro α hα0 hα1
  rw [(principalTwoGradeElement_components x₀ x₁).2.2 α hα0 hα1,
    map_zero]

/-- The public algebra equivalence exposes the embedding and projection without unfolding. -/
theorem principalSubringEquiv_evaluation (x : Berarducci.PrincipalSubring K)
    (y : Berarducci.principalSubringSubalgebra K) :
    ((Berarducci.principalSubringEquivSubalgebra K x :
        Berarducci.principalSubringSubalgebra K) :
      Berarducci.DegreeGraded K) =
        Berarducci.principalSubringEmbedding K x ∧
      (Berarducci.principalSubringEquivSubalgebra K).symm y =
        Berarducci.rvProjection K y := by
  exact ⟨Berarducci.principalSubringEquivSubalgebra_apply x,
    Berarducci.principalSubringEquivSubalgebra_symm_apply y⟩

end Embedding

end TwoGrades

section ProperRange

/-- The monomial `t⁻¹` used to separate the principal graded subring from the full degree-graded
ring. -/
def negativeMonomialForPrincipalGraded : Berarducci.Series K :=
  HahnSeries.Nonpositive.single (-1 : ℝ) 1 (by norm_num)

theorem negativeMonomialForPrincipalGraded_degree :
    ((negativeMonomialForPrincipalGraded (K := K) : Berarducci.Series K) :
      K⟦ℝ⟧).degree = (0 : WithBot NatOrdinal) := by
  apply HahnSeries.degree_eq_zero.mpr
  constructor
  · simp [negativeMonomialForPrincipalGraded]
  · rw [negativeMonomialForPrincipalGraded,
      HahnSeries.Nonpositive.coe_single]
    exact (Set.finite_singleton (-1 : ℝ)).subset
      HahnSeries.support_single_subset

theorem negativeMonomialForPrincipalGraded_ordinalValue :
    Berarducci.ordinalValue (negativeMonomialForPrincipalGraded (K := K)) = 0 := by
  apply Berarducci.ordinalValue_of_mem_negativeMonomialIdeal
  exact HahnSeries.Nonpositive.single_one_mem_negativeMonomialIdeal (by norm_num)

variable (K) in
/-- The nonzero degree-zero class of the strictly negative monomial in `RV̂`. -/
def negativeMonomialDegreeClass :
    (HahnSeries.Nonpositive.degreeValuation K).Component 0 :=
  Berarducci.degreeLayerMk 0
    (negativeMonomialForPrincipalGraded (K := K))
    (negativeMonomialForPrincipalGraded_degree (K := K)).le

variable (K) in
theorem negativeMonomialDegreeClass_ne_zero :
    negativeMonomialDegreeClass K ≠ 0 := by
  rw [negativeMonomialDegreeClass, ne_eq,
    Berarducci.degreeLayerMk_eq_zero_iff,
    negativeMonomialForPrincipalGraded_degree]
  exact (lt_irrefl (0 : WithBot NatOrdinal))

variable (K) in
/-- The homogeneous realization of the strictly negative monomial class in `RV̂`. -/
def negativeMonomialDegreeGraded : Berarducci.DegreeGraded K :=
  DirectSum.of
    (HahnSeries.Nonpositive.degreeValuation K).Component 0
    (negativeMonomialDegreeClass K)

variable (K) in
theorem negativeMonomialDegreeGraded_ne_zero :
    negativeMonomialDegreeGraded K ≠ 0 := by
  rw [negativeMonomialDegreeGraded,
    ← map_zero (DirectSum.of
      (HahnSeries.Nonpositive.degreeValuation K).Component 0)]
  exact (DirectSum.of_injective 0).ne
    (negativeMonomialDegreeClass_ne_zero K)

variable (K) in
theorem negativeMonomialDegreeClass_projection_eq_zero :
    Berarducci.degreeLayerToPrincipalComponent K 0
      (negativeMonomialDegreeClass K) = 0 := by
  rw [negativeMonomialDegreeClass,
    Berarducci.degreeLayerToPrincipalComponent_mk]
  rw [Berarducci.principalComponentMk_eq_zero_iff,
    negativeMonomialForPrincipalGraded_ordinalValue]
  exact NatOrdinal.wpow_pos 0

variable (K) in
theorem negativeMonomialDegreeGraded_projection_eq_zero :
    Berarducci.rvProjection K
      (negativeMonomialDegreeGraded K) = 0 := by
  rw [negativeMonomialDegreeGraded,
    Berarducci.rvProjection_of,
    negativeMonomialDegreeClass_projection_eq_zero]
  exact map_zero _

variable (K) [CharZero K] in
/-- The principal graded subalgebra is strictly smaller than the full degree-graded
graded ring. -/
theorem negativeMonomialDegreeGraded_not_mem_principalGradedSubalgebra :
    negativeMonomialDegreeGraded K ∉
      Berarducci.principalSubringSubalgebra K := by
  intro hmem
  have hprincipal :=
    (Berarducci.mem_principalGradedSubalgebra_iff
      (negativeMonomialDegreeGraded K)).mp hmem
  rw [Berarducci.isPrincipalGraded_iff] at hprincipal
  have hprincipalZero := hprincipal 0
  rw [negativeMonomialDegreeGraded, DirectSum.of_apply] at hprincipalZero
  have hprincipalZero' : Berarducci.IsPrincipalDegreeClass 0
      (negativeMonomialDegreeClass K) := by
    simpa using hprincipalZero
  have hinverse :=
    Berarducci.principalComponentToHahnDegreeLayer_degreeLayerToPrincipalComponent_of_isPrincipal 0
      (negativeMonomialDegreeClass K) hprincipalZero'
  rw [negativeMonomialDegreeClass_projection_eq_zero, map_zero] at hinverse
  exact negativeMonomialDegreeClass_ne_zero K hinverse.symm

end ProperRange

end Tests
