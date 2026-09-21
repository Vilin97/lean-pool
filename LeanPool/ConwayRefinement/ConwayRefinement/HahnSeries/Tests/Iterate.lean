/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Iterate
public import Mathlib.Algebra.Order.Group.Int

/-!
# API checks for iterated Hahn series

This file checks the public ring equivalence on nested monomials. Both exponent coordinates are
nonzero and unequal. Their product appears at the coordinatewise sum in outer-then-inner order and
not at the swapped coordinate, separating the intended flattening from the nearest orientation
error.
-/

public noncomputable section

namespace Tests

open HahnSeries

/-- A nested monomial with outer exponent `2` and inner exponent `3`. -/
def firstIteratedMonomial : ℚ⟦ℤ⟧⟦ℤ⟧ := single 2 (single 3 5)

/-- A nested monomial with outer exponent `7` and inner exponent `11`. -/
def secondIteratedMonomial : ℚ⟦ℤ⟧⟦ℤ⟧ := single 7 (single 11 13)

theorem iterateRingEquiv_product_coeff :
    (iterateRingEquiv (firstIteratedMonomial * secondIteratedMonomial)).coeff
      (toLex ((9 : ℤ), (14 : ℤ))) = 65 := by
  simp [firstIteratedMonomial, secondIteratedMonomial, single_mul_single]
  norm_num

theorem iterateRingEquiv_product_coeff_swapped :
    (iterateRingEquiv (firstIteratedMonomial * secondIteratedMonomial)).coeff
      (toLex ((14 : ℤ), (9 : ℤ))) = 0 := by
  simp [firstIteratedMonomial, secondIteratedMonomial, single_mul_single]

end Tests
