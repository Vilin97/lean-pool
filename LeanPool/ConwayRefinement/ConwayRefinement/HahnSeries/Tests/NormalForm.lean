/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Tests.Fixtures.ApproachZero
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Domain
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Multiplicativity

/-!
# API checks for LM24 principal series and normal forms

The series `approachZero` has coefficient one at every exponent `-1/(n+1)`. Its support has order
type `ω`, has supremum zero, and does not contain zero. It therefore certifies that support
supremum is a genuine least upper bound rather than a maximum and gives a nonconstant principal
series.

Adding the constant term gives the exact example from LM24, Remark 3.3.10. Its normal form has an
infinite principal coefficient at exponent zero followed by the constant principal coefficient at
the same exponent. This separates the source definition from the incorrect variant requiring
strictly increasing exponents.

The series supported on `ℕ ⊆ ℝ` is unbounded above. The final certificate proves that it has
no finite normal form, exercising the obstruction in LM24, Remark 3.3.9 instead of merely checking
the existence theorem on its nonpositive domain.

The same `approachZero` fixture exercises the weak-support, positive-degree branch of the repaired
LM24, Lemma 3.4.2 at its minimum exponent.
-/

public noncomputable section

namespace Tests

open scoped HahnSeries

/-- The empty list is the normal form of the zero series. -/
theorem zero_normalForm :
    HahnSeries.IsNormalForm (0 : ℚ⟦ℝ⟧) [] := by
  rw [HahnSeries.isNormalForm_iff]
  simp [List.sortedLE_iff_pairwise, List.sortedGE_iff_pairwise]

/-- Every normal form of the zero series is empty. -/
theorem zero_normalForm_unique (terms : List (HahnSeries.NormalForm.Term ℚ))
    (hterms : HahnSeries.IsNormalForm (0 : ℚ⟦ℝ⟧) terms) :
    terms = [] :=
  hterms.unique zero_normalForm

private theorem approachZero_support_subset_Ici_neg_one :
    (approachZeroNonpositive : ℚ⟦ℝ⟧).support ⊆ Set.Ici (-1) := by
  rw [coe_approachZeroNonpositive, approachZero_support]
  rintro _ ⟨n, rfl⟩
  rw [approachZeroEmbedding_apply]
  change -1 ≤ -(1 / (n + 1 : ℝ))
  apply neg_le_neg
  simpa using one_div_le_one_div_of_le (a := (1 : ℝ))
    (b := n + 1) (by norm_num) (by norm_num)

private theorem approachZero_degree :
    (approachZeroNonpositive : ℚ⟦ℝ⟧).degree =
      (1 : WithBot NatOrdinal) := by
  rw [HahnSeries.degree_eq_cantorDegree, coe_approachZeroNonpositive,
    approachZero_supportOrderType, Ordinal.cantorDegree_omega]

/-- The positive-degree branch of repaired LM24, Lemma 3.4.2 applies at the attained minimum
exponent of the infinite principal series. -/
theorem approachZero_positiveDegree_truncation_degree_lt :
    (HahnSeries.truncLE (-1)
      (((1 : HahnSeries.Nonpositive ℝ ℚ) * approachZeroNonpositive :
        HahnSeries.Nonpositive ℝ ℚ) : ℚ⟦ℝ⟧)).degree <
      ((1 : HahnSeries.Nonpositive ℝ ℚ) : ℚ⟦ℝ⟧).degree +
        (approachZeroNonpositive : ℚ⟦ℝ⟧).degree := by
  apply HahnSeries.Nonpositive.degree_truncLE_mul_lt
  · exact HahnSeries.Nonpositive.isPrincipal_one
  · exact approachZero_ne_zero
  · right
    refine ⟨approachZero_support_subset_Ici_neg_one, ?_⟩
    rw [approachZero_degree]
    norm_num

/-- The constant series one in the nonpositive Hahn ring. -/
def constantOneNonpositive : HahnSeries.Nonpositive ℝ ℚ :=
  HahnSeries.Nonpositive.C 1

private theorem constantOne_supportOrderType :
    (constantOneNonpositive : ℚ⟦ℝ⟧).supportOrderType = 1 := by
  simpa [constantOneNonpositive, HahnSeries.Nonpositive.coe_C,
    HahnSeries.C_apply] using
      HahnSeries.supportOrderType_single (a := (0 : ℝ)) (r := (1 : ℚ)) one_ne_zero

/-- The constant series one is principal. -/
theorem constantOne_isPrincipal :
    HahnSeries.Nonpositive.IsPrincipal constantOneNonpositive := by
  exact HahnSeries.Nonpositive.isPrincipal_C one_ne_zero

/-- The infinite principal term at exponent zero. -/
def approachZeroTerm : HahnSeries.NormalForm.Term ℚ :=
  ⟨approachZeroNonpositive, 0⟩

/-- The constant principal term at exponent zero. -/
def constantOneTerm : HahnSeries.NormalForm.Term ℚ :=
  ⟨constantOneNonpositive, 0⟩

/-- LM24's `ω + 1` example has a two-term normal form in which exponent zero occurs twice. -/
theorem repeatedZeroExponentNormalForm :
    HahnSeries.IsNormalForm
      (approachZero + 1) [approachZeroTerm, constantOneTerm] := by
  rw [HahnSeries.isNormalForm_iff_isChain]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · ext x
    simp [approachZeroTerm, constantOneTerm,
      coe_approachZeroNonpositive, constantOneNonpositive]
  · simp [approachZeroTerm, constantOneTerm, List.sortedLE_iff_pairwise]
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · exact approachZero_isPrincipal
    · exact constantOne_isPrincipal
  · simp only [approachZeroTerm, constantOneTerm, List.map_cons, List.map_nil,
      constantOne_supportOrderType, coe_approachZeroNonpositive,
      approachZero_supportOrderType]
    rw [List.sortedGE_iff_pairwise]
    simp [Ordinal.one_lt_omega0.le]
  · apply List.isChain_pair.mpr
    rw [HahnSeries.supportBelow_iff]
    intro i hi j hj
    have hj0 : j = 0 := by
      simpa [constantOneTerm, constantOneNonpositive,
        HahnSeries.NormalForm.Term.series_eq_translate] using hj
    subst j
    rw [approachZeroTerm, HahnSeries.NormalForm.Term.series_eq_translate,
      HahnSeries.translate_zero_apply] at hi
    rw [coe_approachZeroNonpositive, approachZero_support] at hi
    obtain ⟨n, rfl⟩ := hi
    rw [approachZeroEmbedding_apply]
    change -(1 / (n + 1 : ℝ)) < 0
    exact neg_lt_zero.mpr (by positivity)

/-- The order embedding of the natural numbers into the reals. -/
def natCastEmbedding : ℕ ↪o ℝ :=
  OrderEmbedding.ofStrictMono _ Nat.strictMono_cast

/-- The coefficient-one series on the unbounded support `ℕ ⊆ ℝ`. -/
def unboundedSeries : ℚ⟦ℝ⟧ :=
  HahnSeries.embDomain natCastEmbedding natOnes

private theorem unboundedSeries_support :
    unboundedSeries.support = Set.range natCastEmbedding := by
  rw [unboundedSeries, HahnSeries.support_embDomain]
  simp

private theorem unboundedSeries_supportOrderType :
    unboundedSeries.supportOrderType = Ordinal.omega0 := by
  rw [HahnSeries.supportOrderType_eq_setOrderType]
  have e : unboundedSeries.support ≃o ℕ :=
    (Set.orderIsoOfEq unboundedSeries.support (Set.range natCastEmbedding)
      unboundedSeries_support).trans natCastEmbedding.orderIso.symm
  exact unboundedSeries.isPWO_support.orderType_eq_typeLT_of_orderIso e |>.trans
    Ordinal.type_nat_lt

/-- The unbounded coefficient-one series is weakly principal of support order type `ω`. -/
theorem unboundedSeries_isWeaklyPrincipal :
    HahnSeries.IsWeaklyPrincipal unboundedSeries := by
  rw [HahnSeries.isWeaklyPrincipal_iff, unboundedSeries_supportOrderType]
  simpa using Ordinal.isAdditivelyPrincipal_omega0_opow 1

/-- The unbounded weakly principal series in LM24, Remark 3.3.9 has no finite normal form. -/
theorem unboundedSeries_has_no_normalForm :
    ∀ terms : List (HahnSeries.NormalForm.Term ℚ),
      ¬HahnSeries.IsNormalForm unboundedSeries terms := by
  intro terms hnormal
  obtain ⟨a, ha⟩ := hnormal.bddAbove_support
  rw [unboundedSeries_support] at ha
  obtain ⟨n, hn⟩ := exists_nat_gt a
  have hle := ha ⟨n, rfl⟩
  exact (not_le_of_gt hn) hle

end Tests
