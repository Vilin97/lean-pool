/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.IntegerPart.Assumptions

/-!
# API checks for LM24 assumptions `(A1)_σ` and `(A2)_σ`

This separately compiled client exercises both clauses of `(A1)_σ` and all three clauses of
`(A2)_σ`. The finite-class checks keep the real-stratum, cofinality, and degenerate
fraction-field alternatives distinct; the full-class checks confirm that the class of zero is
accepted independently.
-/

universe u v

public noncomputable section

open Cardinal

namespace Tests

theorem assumptionA1_zero_class
    {K : Type*} {G : Type u}
    [DivisionRing K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]
    [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
    [Module K G] [IsOrderedModule K G]
    (s : HahnEmbedding.ArchimedeanStrata K G) :
    LM24.AssumptionA1 s (⊤ : ArchimedeanClass G) := by
  rw [LM24.assumptionA1_iff]
  exact Or.inl rfl

theorem assumptionA1_finite_of_orderAddMonoidIso_real
    {K : Type*} {G : Type u}
    [DivisionRing K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]
    [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
    [Module K G] [IsOrderedModule K G]
    (s : HahnEmbedding.ArchimedeanStrata K G) (c : FiniteArchimedeanClass G)
    (e : s.stratum c ≃+o ℝ) :
    LM24.AssumptionA1AtFiniteClass s c := by
  rw [LM24.assumptionA1AtFiniteClass_iff]
  exact ⟨e⟩

theorem assumptionA2_zero_class
    {G : Type u} {R : Type v}
    [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G] [Field R]
    (κ : Cardinal.{u}) (Z : Subring R) :
    LM24.AssumptionA2 κ Z (⊤ : ArchimedeanClass G) := by
  rw [LM24.assumptionA2_iff]
  exact Or.inr (Or.inr rfl)

theorem assumptionA2_finite_of_cofinality
    {K : Type*} {G : Type u} {R : Type v}
    [DivisionRing K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]
    [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
    [Module K G] [IsOrderedModule K G] [Field R]
    (κ : Cardinal.{u}) (Z : Subring R) (σ : FiniteArchimedeanClass G)
    (hcof : κ ≤ Order.cof ↥(FiniteArchimedeanClass.ball K σ)) :
    LM24.AssumptionA2AtFiniteClass (K := K) κ Z σ := by
  rw [LM24.assumptionA2AtFiniteClass_iff]
  exact Or.inl hcof

theorem assumptionA2_finite_of_zero_inner_group
    {K : Type*} {G : Type u} {R : Type v}
    [DivisionRing K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]
    [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
    [Module K G] [IsOrderedModule K G] [Field R]
    (κ : Cardinal.{u}) (Z : Subring R) (σ : FiniteArchimedeanClass G)
    (hzero : Subsingleton ↥(FiniteArchimedeanClass.ball K σ))
    (hfrac : Subring.fracSubring Z = ⊤) :
    LM24.AssumptionA2AtFiniteClass (K := K) κ Z σ := by
  rw [LM24.assumptionA2AtFiniteClass_iff]
  exact Or.inr ⟨hzero, hfrac⟩

theorem assumptionA2_finite_fraction_consequence
    {K : Type*} {G : Type u} {R : Type v} {κ : Cardinal.{u}}
    [DivisionRing K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]
    [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
    [Module K G] [IsOrderedModule K G] [Field R] [Fact (ℵ₀ < κ)]
    (Z : Subring R) (σ : FiniteArchimedeanClass G)
    (hA2 : LM24.AssumptionA2AtFiniteClass (K := K) κ Z σ) :
    Subring.fracSubring
      (HahnSeries.cardSuppLTTruncationIntegerPart
        (G := ↥(FiniteArchimedeanClass.ball K σ)) (R := R) (κ := κ) Z) = ⊤ :=
  LM24.fracSubring_cardSuppLTTruncationIntegerPart_eq_top_of_assumptionA2AtFiniteClass
    Z σ hA2

end Tests
