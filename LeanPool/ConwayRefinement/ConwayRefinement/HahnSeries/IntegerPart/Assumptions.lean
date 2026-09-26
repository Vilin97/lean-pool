/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.CardinalTruncation
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.ArchimedeanSplitting
public import Mathlib.Algebra.Order.Module.Archimedean
public import Mathlib.Basic.Real.Embedding

/-!
# LM24 assumptions at an Archimedean class

This module records assumptions `(A1)_σ` and `(A2)_σ` from LM24, Theorem 9.0.1. Assumption
`(A1)_σ` says that the chosen complement at a nonzero class is isomorphic, as an ordered
additive group, to `ℝ`. Assumption `(A2)_σ` is the paper's cofinality or degenerate-inner-group
disjunction. Both full predicates retain the paper's zero-class clause; their finite-class
specializations remove precisely that clause.

The elimination theorem supplies the fraction-field conclusion of LM24, Proposition 2.4.5 for
the cardinal-bounded inner truncation integer part. It does not replace `(A2)_σ` by that
conclusion: both the printed assumption and its consequence remain visible in the public API.
-/

universe u v

public noncomputable section

open Cardinal

namespace LM24

variable {K : Type*} {G : Type u} {R : Type v}
variable [DivisionRing K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]
variable [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
variable [Module K G] [IsOrderedModule K G]
variable [Field R]

/-! ### Assumption `(A1)_σ` -/

/-- LM24 assumption `(A1)_σ`: the chosen stratum at `σ` is order-additively isomorphic to
`ℝ`, or `σ` is the class of zero. Mathlib orders Archimedean classes oppositely to LM24, so
the zero class is `⊤`. -/
def AssumptionA1 (u : HahnEmbedding.ArchimedeanStrata K G)
    (σ : ArchimedeanClass G) : Prop :=
  σ = ⊤ ∨
    ∃ c : FiniteArchimedeanClass G,
      FiniteArchimedeanClass.withTopOrderIso G c = σ ∧
        Nonempty (u.stratum c ≃+o ℝ)

/-- The defining zero-class/isomorphic-stratum disjunction for `(A1)_σ`. -/
theorem assumptionA1_iff (u : HahnEmbedding.ArchimedeanStrata K G)
    (σ : ArchimedeanClass G) :
    AssumptionA1 u σ ↔
      σ = ⊤ ∨
        ∃ c : FiniteArchimedeanClass G,
          FiniteArchimedeanClass.withTopOrderIso G c = σ ∧
            Nonempty (u.stratum c ≃+o ℝ) :=
  (Iff.rfl)

/-- The nonzero-class specialization of LM24 assumption `(A1)_σ`. -/
def AssumptionA1AtFiniteClass (u : HahnEmbedding.ArchimedeanStrata K G)
    (c : FiniteArchimedeanClass G) : Prop :=
  Nonempty (u.stratum c ≃+o ℝ)

/-- The defining ordered-additive isomorphism for `(A1)_σ` at a nonzero class. -/
theorem assumptionA1AtFiniteClass_iff (u : HahnEmbedding.ArchimedeanStrata K G)
    (c : FiniteArchimedeanClass G) :
    AssumptionA1AtFiniteClass u c ↔ Nonempty (u.stratum c ≃+o ℝ) :=
  (Iff.rfl)

/-! ### Assumption `(A2)_σ` -/

/-- LM24 assumption `(A2)_σ`: the inner exponent group has cofinality at least `κ`, or it
is zero and `Frac(Z) = R`, or `σ` is the class of zero. -/
def AssumptionA2 (κ : Cardinal.{u}) (Z : Subring R) (σ : ArchimedeanClass G) : Prop :=
  κ ≤ Order.cof ↥(ArchimedeanClass.ballAddSubgroup σ) ∨
    (Subsingleton ↥(ArchimedeanClass.ballAddSubgroup σ) ∧
      Subring.fracSubring Z = ⊤) ∨ σ = ⊤

/-- The defining disjunction for `(A2)_σ`. -/
theorem assumptionA2_iff (κ : Cardinal.{u}) (Z : Subring R) (σ : ArchimedeanClass G) :
    AssumptionA2 κ Z σ ↔
      κ ≤ Order.cof ↥(ArchimedeanClass.ballAddSubgroup σ) ∨
        (Subsingleton ↥(ArchimedeanClass.ballAddSubgroup σ) ∧
          Subring.fracSubring Z = ⊤) ∨ σ = ⊤ :=
  (Iff.rfl)

/-- The nonzero-class specialization of LM24 assumption `(A2)_σ`. -/
def AssumptionA2AtFiniteClass (κ : Cardinal.{u}) (Z : Subring R)
    (σ : FiniteArchimedeanClass G) : Prop :=
  κ ≤ Order.cof ↥(FiniteArchimedeanClass.ball K σ) ∨
    (Subsingleton ↥(FiniteArchimedeanClass.ball K σ) ∧ Subring.fracSubring Z = ⊤)

/-- The defining disjunction for `(A2)_σ` at a nonzero Archimedean class. -/
theorem assumptionA2AtFiniteClass_iff (κ : Cardinal.{u}) (Z : Subring R)
    (σ : FiniteArchimedeanClass G) :
    AssumptionA2AtFiniteClass (K := K) κ Z σ ↔
      κ ≤ Order.cof ↥(FiniteArchimedeanClass.ball K σ) ∨
        (Subsingleton ↥(FiniteArchimedeanClass.ball K σ) ∧ Subring.fracSubring Z = ⊤) :=
  (Iff.rfl)

/-- The cofinality clause implies the bounded inner fraction-field equality. -/
theorem fracSubring_cardSuppLTTruncationIntegerPart_eq_top_of_assumptionA2AtFiniteClass
    {κ : Cardinal.{u}} [Fact (ℵ₀ < κ)] (Z : Subring R) (σ : FiniteArchimedeanClass G)
    (hA2 : AssumptionA2AtFiniteClass (K := K) κ Z σ) :
    Subring.fracSubring
      (HahnSeries.cardSuppLTTruncationIntegerPart
        (G := ↥(FiniteArchimedeanClass.ball K σ)) (R := R) (κ := κ) Z) = ⊤ := by
  rcases (assumptionA2AtFiniteClass_iff (K := K) κ Z σ).mp hA2 with hcof | ⟨hzero, hfrac⟩
  · exact HahnSeries.fracSubring_cardSuppLTTruncationIntegerPart_eq_top_of_le_cof Z hcof
  · let : Subsingleton ↥(FiniteArchimedeanClass.ball K σ) := hzero
    exact HahnSeries.fracSubring_cardSuppLTTruncationIntegerPart_eq_top_of_subsingleton Z hfrac

end LM24
