/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.Valuation.DegreeAssociatedGradedDomain
public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.Valuation.Tests.Fixtures.PolynomialAssociatedGraded

import Mathlib.Algebra.Polynomial.Degree.Operations

/-!
# API checks for the associated graded ring of a degree function

The class of `X` in grade one is nonzero, and its homogeneous square is represented by `X ^ 2`
in grade two. The square is nonzero because its polynomial degree is exactly two. This checks
multiplication on a genuinely nonconstant representative and distinguishes the intended strict
lower filtration from a quotient that kills all positive-degree elements.

The zero polynomial still maps to zero in a positive component, checking the bottom-degree branch.
-/

public noncomputable section

namespace Tests

open Polynomial
open scoped MaxAddDegree

/-- Exact multiplication of polynomial degree gives the generic homogeneous
non-zero-divisor condition. -/
theorem polynomialDegree_homogeneousNoZeroDivisors :
    polynomialDegree.HomogeneousNoZeroDivisors :=
  polynomialDegree.homogeneousNoZeroDivisors_of_isMultiplicative

/-- Homogeneous squaring is represented by polynomial squaring. -/
theorem polynomialInitial_sq :
    polynomialDegree.componentMul polynomialXInitial polynomialXInitial =
      polynomialDegree.componentMk 2
        ⟨X ^ 2, (polynomialDegree.mem_filtrationLE_iff 2 (X ^ 2)).mpr (by
          rw [polynomialDegree_apply, Polynomial.degree_X_pow]
          simp)⟩ := by
  rw [polynomialXInitial_eq_componentMk, polynomialDegree.componentMul_componentMk]
  apply congrArg (polynomialDegree.componentMk 2)
  apply Subtype.ext
  rw [polynomialDegree.coe_mulFiltrationLE]
  exact (pow_two (X : ℚ[X])).symm

/-- The square of the nonzero degree-one test class is nonzero. -/
theorem polynomialInitial_sq_ne_zero :
    polynomialDegree.componentMul polynomialXInitial polynomialXInitial ≠ 0 := by
  rw [polynomialInitial_sq, ne_eq, polynomialDegree.componentMk_eq_zero_iff,
    polynomialDegree_apply, Polynomial.degree_X_pow]
  exact lt_irrefl _

/-- Bottom degree maps the zero polynomial to zero in a positive component. -/
theorem polynomialZeroInitial_eq_zero :
    polynomialDegree.componentMk 1 ⟨(0 : ℚ[X]), by simp⟩ = 0 := by
  rw [polynomialDegree.componentMk_eq_zero_iff, polynomialDegree_apply]
  simp

end Tests
