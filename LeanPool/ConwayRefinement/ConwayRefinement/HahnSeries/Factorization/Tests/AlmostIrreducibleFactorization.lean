/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Factorization.AlmostIrreducibleFactorization

/-!
# API checks for exponent-subgroup factorisation

The scalar series `2` has a corrected factorisation with no almost irreducible factors. The same
series is not the unscaled product with normalized finite-support factor `1`, monomial exponent
`0`, and an empty factor list. This is the smallest boundary example that detects the coefficient
scalar missing from the printed formula in LM24, Theorem 6.5.7.
-/

open scoped HahnSeries

namespace Tests

public noncomputable section

open HahnSeries.Nonpositive

abbrev FactorizationExponentSubgroup : AddSubgroup ℝ := ⊤

abbrev FactorizationSeries :=
  HahnSeries.Nonpositive FactorizationExponentSubgroup ℚ

/-- The zero exponent as an element of the nonpositive exponent monoid. -/
def factorizationZeroExponent :
    HahnSeries.Nonpositive.exponentMonoid FactorizationExponentSubgroup :=
  ⟨(0 : FactorizationExponentSubgroup), by
    change (0 : FactorizationExponentSubgroup) ≤ 0
    exact le_rfl⟩

/-- The scalar series `2` has a corrected factorisation with an explicit coefficient scalar. -/
theorem scalarTwo_almostIrreducibleFactorization :
    IsAlmostIrreducibleFactorization
      (C 2 : FactorizationSeries) (Units.mk0 2 (by norm_num))
      (1 : ConstantTermOneFiniteSupport
        (G := FactorizationExponentSubgroup) (K := ℚ))
      factorizationZeroExponent [] := by
  rw [isAlmostIrreducibleFactorization_iff]
  constructor
  · apply Subtype.ext
    simp [factorizationZeroExponent, coe_finiteSupportMonomial, coe_C]
  · simp

/-- Omitting the coefficient scalar makes the corresponding empty factorisation of `2` false. -/
theorem scalarTwo_ne_unscaled_empty_factorization :
    (C 2 : FactorizationSeries) ≠
      (((1 : ConstantTermOneFiniteSupport
          (G := FactorizationExponentSubgroup) (K := ℚ)) :
            FiniteSupportRing (G := FactorizationExponentSubgroup) (K := ℚ)) :
          FactorizationSeries) *
        (finiteSupportMonomial (K := ℚ) factorizationZeroExponent :
          FactorizationSeries) * ([] : List FactorizationSeries).prod := by
  intro h
  have hconstant := congrArg constantCoeff h
  norm_num [factorizationZeroExponent, coe_finiteSupportMonomial,
    constantCoeff_apply] at hconstant

end

end Tests
