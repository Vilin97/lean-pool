/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.Valuation.MaxAddDegree
public import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Degree.Operations

/-!
# Polynomial-degree fixture

This module packages ordinary degree on `ℚ[X]` as a separated `MaxAddDegree`. It is shared by
the quotient-degree and associated-graded API clients.
-/

public noncomputable section

namespace Tests

open Polynomial

/-- The ordinary degree on `ℚ[X]` as a submultiplicative max-additive degree. -/
def polynomialDegree : MaxAddDegree ℚ[X] ℕ where
  toFun := Polynomial.degree
  map_zero' := Polynomial.degree_zero
  map_one_le_zero' := Polynomial.degree_one_le
  map_neg' := Polynomial.degree_neg
  map_add_le_max' := Polynomial.degree_add_le
  map_mul_le_add' := Polynomial.degree_mul_le

@[simp]
theorem polynomialDegree_apply (p : ℚ[X]) :
    polynomialDegree p = p.degree := (rfl)

/-- Ordinary polynomial degree is separated. -/
theorem polynomialDegree_isSeparated : polynomialDegree.IsSeparated := by
  rw [MaxAddDegree.isSeparated_iff]
  intro p
  rw [polynomialDegree_apply, Polynomial.degree_eq_bot]

/-- Ordinary polynomial degree is exactly multiplicative over `ℚ`. -/
instance polynomialDegree_isMultiplicative : polynomialDegree.IsMultiplicative :=
  ⟨fun _ _ ↦ Polynomial.degree_mul⟩

end Tests
