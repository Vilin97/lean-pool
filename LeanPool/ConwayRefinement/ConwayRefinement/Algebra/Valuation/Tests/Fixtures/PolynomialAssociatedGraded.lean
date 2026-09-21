/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.Valuation.DegreeAssociatedGraded
public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.Valuation.Tests.Fixtures.PolynomialDegree

/-!
# Polynomial associated-graded fixture

This module supplies the degree-one initial class of `X` shared by associated-graded API clients.
-/

public noncomputable section

namespace Tests

open Polynomial

/-- The class of `X` in the degree-one homogeneous component. -/
def polynomialXInitial : polynomialDegree.Component 1 :=
  polynomialDegree.componentMk 1
    ⟨X, (polynomialDegree.mem_filtrationLE_iff 1 X).mpr (by
      rw [polynomialDegree_apply, Polynomial.degree_X]
      simp)⟩

/-- Evaluation of the polynomial initial-class fixture. -/
theorem polynomialXInitial_eq_componentMk :
    polynomialXInitial = polynomialDegree.componentMk 1
      ⟨X, (polynomialDegree.mem_filtrationLE_iff 1 X).mpr (by
        rw [polynomialDegree_apply, Polynomial.degree_X]
        simp)⟩ :=
  (rfl)

/-- The degree-one initial class of `X` is nonzero. -/
theorem polynomialXInitial_ne_zero : polynomialXInitial ≠ 0 := by
  rw [polynomialXInitial_eq_componentMk, ne_eq,
    polynomialDegree.componentMk_eq_zero_iff,
    polynomialDegree_apply, Polynomial.degree_X]
  exact lt_irrefl _

end Tests
