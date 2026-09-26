/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.Valuation.QuotientDegree
public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.Valuation.Tests.Fixtures.PolynomialDegree
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.RingTheory.Ideal.Maps

/-!
# Polynomial quotient-degree fixture

This module packages the least-representative degree on `ℚ[X] / (X - 1)`. It is shared by the
quotient-degree and associated-graded-quotient API clients.
-/

public noncomputable section

namespace Tests

open Polynomial

/-- The ideal imposing the relation `X = 1`. -/
def evaluationAtOneIdeal : Ideal ℚ[X] :=
  Ideal.span {X - C 1}

/-- Evaluation of the ideal imposing `X = 1`. -/
theorem evaluationAtOneIdeal_eq_span :
    evaluationAtOneIdeal = Ideal.span {X - C 1} :=
  (rfl)

theorem evaluationAtOneIdeal_le_ker_evalAtOne :
    evaluationAtOneIdeal ≤ RingHom.ker (Polynomial.evalRingHom (1 : ℚ)) := by
  rw [evaluationAtOneIdeal, Ideal.span_le]
  intro p hp
  rw [Set.mem_singleton_iff.mp hp]
  change Polynomial.evalRingHom (1 : ℚ) (X - C 1) = 0
  simp

/-- The quotient degree on `ℚ[X] / (X - 1)`. -/
def evaluationAtOneQuotientDegree : MaxAddDegree (ℚ[X] ⧸ evaluationAtOneIdeal) ℕ :=
  polynomialDegree.quotient evaluationAtOneIdeal polynomialDegree_isSeparated

@[simp]
theorem evaluationAtOneQuotientDegree_apply (q : ℚ[X] ⧸ evaluationAtOneIdeal) :
    evaluationAtOneQuotientDegree q =
      polynomialDegree.quotientValue evaluationAtOneIdeal
        polynomialDegree_isSeparated q := by
  rw [evaluationAtOneQuotientDegree, polynomialDegree.quotient_apply]

theorem quotientMk_X_eq_quotientMk_one :
    Ideal.Quotient.mk evaluationAtOneIdeal X =
      Ideal.Quotient.mk evaluationAtOneIdeal (C 1) := by
  rw [Ideal.Quotient.eq, evaluationAtOneIdeal]
  exact Ideal.subset_span (Set.mem_singleton _)

theorem quotientMk_one_ne_zero :
    Ideal.Quotient.mk evaluationAtOneIdeal (C 1) ≠ 0 := by
  intro hzero
  have hmem : C (1 : ℚ) ∈ evaluationAtOneIdeal :=
    Ideal.Quotient.eq_zero_iff_mem.mp hzero
  have hker := evaluationAtOneIdeal_le_ker_evalAtOne hmem
  rw [RingHom.mem_ker] at hker
  simp at hker

theorem quotientMk_X_sub_one_eq_zero :
    Ideal.Quotient.mk evaluationAtOneIdeal (X - C 1) = 0 := by
  rw [Ideal.Quotient.eq_zero_iff_mem, evaluationAtOneIdeal]
  exact Ideal.subset_span (Set.mem_singleton _)

end Tests
