/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.Valuation.Tests.Fixtures.PolynomialQuotientDegree

/-!
# API checks for least-representative quotient degree

The ordinary degree on `ℚ[X]` gives a separated max-additive degree. We quotient by `(X - 1)`.
The nonzero class of `X` also has the constant representative `1`, so its quotient degree is zero
rather than the degree one of `X`. Conversely, the zero class has the nonzero representative
`X - 1` of degree one but receives bottom degree. These two checks distinguish minimization over
all representatives and the explicit zero-class branch from the nearby wrong construction that
uses one arbitrarily chosen representative.
-/

public noncomputable section

namespace Tests

open Polynomial

/-- The class of `X` has quotient degree zero because the same class has constant representative
`1`; a construction using the displayed representative `X` would assign degree one. -/
theorem evaluationAtOneQuotientDegree_X_eq_zero :
    evaluationAtOneQuotientDegree
      (Ideal.Quotient.mk evaluationAtOneIdeal X) = 0 := by
  rw [quotientMk_X_eq_quotientMk_one, evaluationAtOneQuotientDegree_apply]
  have hle := polynomialDegree.quotientValue_mk_le evaluationAtOneIdeal
    polynomialDegree_isSeparated (C (1 : ℚ))
  rw [polynomialDegree_apply, Polynomial.degree_C one_ne_zero] at hle
  have hne : polynomialDegree.quotientValue evaluationAtOneIdeal
      polynomialDegree_isSeparated (Ideal.Quotient.mk evaluationAtOneIdeal (C 1)) ≠ ⊥ := by
    rw [ne_eq, polynomialDegree.quotientValue_eq_bot_iff]
    exact quotientMk_one_ne_zero
  obtain ⟨n, hn⟩ := WithBot.ne_bot_iff_exists.mp hne
  rw [← hn] at hle ⊢
  have hn0 : n = 0 := Nat.eq_zero_of_le_zero (WithBot.coe_le_coe.mp hle)
  simp [hn0]

/-- The zero quotient class has bottom degree even when displayed by the degree-one representative
`X - 1`; a construction minimizing only nonzero classes without a zero branch would fail here. -/
theorem evaluationAtOneQuotientDegree_X_sub_one_eq_bot :
    evaluationAtOneQuotientDegree
      (Ideal.Quotient.mk evaluationAtOneIdeal (X - C 1)) = ⊥ ∧
      (X - C (1 : ℚ)).degree = 1 := by
  constructor
  · rw [quotientMk_X_sub_one_eq_zero]
    exact MaxAddDegree.map_zero evaluationAtOneQuotientDegree
  · apply le_antisymm (Polynomial.degree_X_sub_C_le 1)
    apply Polynomial.le_degree_of_ne_zero
    norm_num [Polynomial.coeff_X, Polynomial.coeff_one]

end Tests
