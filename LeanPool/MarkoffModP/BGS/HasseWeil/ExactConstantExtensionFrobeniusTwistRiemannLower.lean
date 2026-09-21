/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.HasseWeil.ExactConstantExtensionFrobeniusTwistConstants
import LeanPool.MarkoffModP.BGS.HasseWeil.GeneralFiniteExtensionRiemannLower

/-!
# A common Riemann budget for Frobenius-twist fields

For a fixed finite constant extension `S / C`, there are only finitely many
Frobenius-twist fields attached to the elements of `Gal(N / C(X))`.  The
primitive-element Riemann inequality supplies a finite-place budget for each
twist.  Summing these finitely many budgets gives one budget which works for
every twist field simultaneously.

This file also records that the same twist fields have exact constant field
`C`, so the common budget and the constant-field input needed by the intrinsic
Stepanov estimate are available at the same boundary.
-/

namespace BGS.HasseWeil

open BGS.CorvajaZannier
open scoped TensorProduct

noncomputable section


variable (C N S : Type*) [Field C] [Fintype C] [DecidableEq C]
  [DecidableEq (RatFunc C)]
  [Field N] [Algebra (RatFunc C) N] [Algebra C N]
  [IsScalarTower C (RatFunc C) N]
  [FiniteDimensional (RatFunc C) N]
  [Algebra.IsSeparable (RatFunc C) N]
  [Field S] [Algebra C S] [FiniteDimensional C S] [IsGalois C S]
  [Finite S]

omit [DecidableEq C] [DecidableEq (RatFunc C)]
  [Algebra.IsSeparable (RatFunc C) N] [Finite S] in
/-- A twist fixed field is finite-dimensional over the rational-function
base because it embeds into the finite exact constant extension. -/
theorem finiteDimensional_frobeniusTwistField_over_ratFunc
    (hExact : algebraicClosure C N =
      (⊥ : IntermediateField C N))
    (g : N ≃ₐ[RatFunc C] N) :
    letI := exactConstantExtensionField C N S hExact
    letI := exactConstantExtensionBaseAlgebra C (RatFunc C) N S
    let F := exactConstantExtensionFrobeniusTwistField
      C (RatFunc C) N S hExact g
    FiniteDimensional (RatFunc C) F := by
  let T := ExactConstantExtension C N S
  letI : Field T := exactConstantExtensionField C N S hExact
  letI : Algebra (RatFunc C) T :=
    exactConstantExtensionBaseAlgebra C (RatFunc C) N S
  letI : Algebra N T := exactConstantExtensionAlgebra C N S
  letI : IsScalarTower (RatFunc C) N T :=
    exactConstantExtensionBaseTower C (RatFunc C) N S
  let tensorEquiv := exactConstantExtensionLinearEquiv C N S
  letI : Module.Finite N (N ⊗[C] S) := Module.Finite.base_change C N S
  letI : Module.Finite N T := Module.Finite.equiv tensorEquiv
  letI : Module.Finite (RatFunc C) T := Module.Finite.trans N T
  let F := exactConstantExtensionFrobeniusTwistField
    C (RatFunc C) N S hExact g
  exact Module.Finite.left (RatFunc C) F T

omit [DecidableEq C] [DecidableEq (RatFunc C)]
  [FiniteDimensional (RatFunc C) N] [Finite S] in
/-- Separability descends from the finite separable exact constant extension
to each intermediate twist fixed field. -/
theorem isSeparable_frobeniusTwistField_over_ratFunc
    (hExact : algebraicClosure C N =
      (⊥ : IntermediateField C N))
    (g : N ≃ₐ[RatFunc C] N) :
    letI := exactConstantExtensionField C N S hExact
    letI := exactConstantExtensionBaseAlgebra C (RatFunc C) N S
    let F := exactConstantExtensionFrobeniusTwistField
      C (RatFunc C) N S hExact g
    Algebra.IsSeparable (RatFunc C) F := by
  let T := ExactConstantExtension C N S
  letI : Field T := exactConstantExtensionField C N S hExact
  letI : Algebra (RatFunc C) T :=
    exactConstantExtensionBaseAlgebra C (RatFunc C) N S
  let F := exactConstantExtensionFrobeniusTwistField
    C (RatFunc C) N S hExact g
  letI : SMul (RatFunc C) T := Algebra.toSMul
  letI : Module (RatFunc C) T := Algebra.toModule
  letI : Algebra N T := exactConstantExtensionAlgebra C N S
  letI : SMul N T := Algebra.toSMul
  letI : Module N T := Algebra.toModule
  letI : IsScalarTower (RatFunc C) N T :=
    exactConstantExtensionBaseTower C (RatFunc C) N S
  letI : IsGalois N T :=
    exactConstantExtension_isGalois C N N S hExact
  letI : Algebra.IsSeparable (RatFunc C) T :=
    Algebra.IsSeparable.trans (RatFunc C) N T
  exact Algebra.isSeparable_tower_bot_of_isSeparable (RatFunc C) F T

omit [Finite S] in
/-- Each Frobenius-twist field is a finite separable function field over
`C(X)`, hence has a finite-place Riemann budget. -/
private theorem exists_frobeniusTwistField_finitePlace_riemann_lower_budget
    (hExact : algebraicClosure C N =
      (⊥ : IntermediateField C N))
    (g : N ≃ₐ[RatFunc C] N) :
    letI := exactConstantExtensionField C N S hExact
    letI := exactConstantExtensionBaseAlgebra C (RatFunc C) N S
    let F := exactConstantExtensionFrobeniusTwistField
      C (RatFunc C) N S hExact g
    letI : FiniteDimensional (RatFunc C) F :=
      finiteDimensional_frobeniusTwistField_over_ratFunc C N S hExact g
    letI : Algebra.IsSeparable (RatFunc C) F :=
      isSeparable_frobeniusTwistField_over_ratFunc C N S hExact g
    ∃ budget : ℕ,
      ∀ (q : FiniteExtensionFinitePlace C F) (poleOrder : ℕ),
        poleOrder * finiteExtensionPlaceDegree C F (.inl q) + 1 ≤
          Module.finrank C
              (finiteExtensionOnePointRiemannSpace C F (.inl q) poleOrder) +
            budget := by
  letI := exactConstantExtensionField C N S hExact
  letI := exactConstantExtensionBaseAlgebra C (RatFunc C) N S
  let F := exactConstantExtensionFrobeniusTwistField
    C (RatFunc C) N S hExact g
  letI : FiniteDimensional (RatFunc C) F :=
    finiteDimensional_frobeniusTwistField_over_ratFunc C N S hExact g
  letI : Algebra.IsSeparable (RatFunc C) F :=
    isSeparable_frobeniusTwistField_over_ratFunc C N S hExact g
  exact exists_finitePlace_riemann_lower_budget C F

omit [Finite S] in
/-- For one fixed finite extension of the constants, a single natural-number
budget works for the finite-place Riemann inequality in every Frobenius-twist
field. -/
theorem exists_common_frobeniusTwistField_finitePlace_riemann_lower_budget
    (hExact : algebraicClosure C N =
      (⊥ : IntermediateField C N)) :
    letI := exactConstantExtensionField C N S hExact
    letI := exactConstantExtensionBaseAlgebra C (RatFunc C) N S
    ∃ budget : ℕ,
      ∀ (g : N ≃ₐ[RatFunc C] N),
        let F := exactConstantExtensionFrobeniusTwistField
          C (RatFunc C) N S hExact g
        letI : FiniteDimensional (RatFunc C) F :=
          finiteDimensional_frobeniusTwistField_over_ratFunc C N S hExact g
        letI : Algebra.IsSeparable (RatFunc C) F :=
          isSeparable_frobeniusTwistField_over_ratFunc C N S hExact g
        ∀ (q : FiniteExtensionFinitePlace C F) (poleOrder : ℕ),
          poleOrder * finiteExtensionPlaceDegree C F (.inl q) + 1 ≤
            Module.finrank C
                (finiteExtensionOnePointRiemannSpace C F (.inl q) poleOrder) +
              budget := by
  letI := exactConstantExtensionField C N S hExact
  letI := exactConstantExtensionBaseAlgebra C (RatFunc C) N S
  choose twistBudget htwistBudget using fun g : N ≃ₐ[RatFunc C] N =>
    exists_frobeniusTwistField_finitePlace_riemann_lower_budget
      C N S hExact g
  let budget : ℕ := ∑ g : N ≃ₐ[RatFunc C] N, twistBudget g
  refine ⟨budget, ?_⟩
  intro g
  dsimp only
  have hle : twistBudget g ≤ budget := by
    dsimp only [budget]
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ g)
  intro q poleOrder
  exact (htwistBudget g q poleOrder).trans
    (Nat.add_le_add_left hle _)

/-- The common Riemann budget can be chosen simultaneously with the statement
that every Frobenius-twist field has exact constant field `C`. -/
theorem exists_common_frobeniusTwistField_exactConstants_and_riemann_budget
    (hExact : algebraicClosure C N =
      (⊥ : IntermediateField C N)) :
    letI := exactConstantExtensionField C N S hExact
    letI := exactConstantExtensionBaseAlgebra C (RatFunc C) N S
    ∃ budget : ℕ,
      ∀ (g : N ≃ₐ[RatFunc C] N),
        let F := exactConstantExtensionFrobeniusTwistField
          C (RatFunc C) N S hExact g
        letI : FiniteDimensional (RatFunc C) F :=
          finiteDimensional_frobeniusTwistField_over_ratFunc C N S hExact g
        letI : Algebra.IsSeparable (RatFunc C) F :=
          isSeparable_frobeniusTwistField_over_ratFunc C N S hExact g
        letI : Algebra C F := Algebra.restrictScalars C (RatFunc C) F
        algebraicClosure C F = (⊥ : IntermediateField C F) ∧
          ∀ (q : FiniteExtensionFinitePlace C F) (poleOrder : ℕ),
            poleOrder * finiteExtensionPlaceDegree C F (.inl q) + 1 ≤
              Module.finrank C
                  (finiteExtensionOnePointRiemannSpace C F (.inl q) poleOrder) +
                budget := by
  letI := exactConstantExtensionField C N S hExact
  letI := exactConstantExtensionBaseAlgebra C (RatFunc C) N S
  obtain ⟨budget, hbudget⟩ :=
    exists_common_frobeniusTwistField_finitePlace_riemann_lower_budget
      C N S hExact
  refine ⟨budget, ?_⟩
  intro g
  dsimp only
  refine ⟨?_, hbudget g⟩
  exact exactConstantExtensionFrobeniusTwistField_algebraicClosure_eq_bot
    C (RatFunc C) N S hExact g

end

end BGS.HasseWeil
