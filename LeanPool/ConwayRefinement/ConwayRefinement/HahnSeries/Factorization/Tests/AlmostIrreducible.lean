/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Factorization.AlmostIrreducible

/-!
# API checks for almost-irreducible Hahn series

The identity fixture preserves the exact boundary omitted from the second assertion of LM24,
Remark 6.5.1: `1` is almost irreducible and has real support supremum zero, but is not
irreducible. The negative monomial `t⁻¹` exercises the strict-negative-supremum assertion over
the divisible exponent group `ℝ` and is visibly nonzero and nonconstant.
-/

open scoped HahnSeries

namespace Tests

public noncomputable section

open HahnSeries.Nonpositive

abbrev RealExponentSubgroup : AddSubgroup ℝ := ⊤

abbrev RealExponentSeries :=
  HahnSeries.Nonpositive RealExponentSubgroup ℚ

noncomputable local instance : DivisibleBy RealExponentSubgroup ℤ where
  div a n := ⟨DivisibleBy.div (a : ℝ) n, Set.mem_univ _⟩
  div_zero a := Subtype.ext (DivisibleBy.div_zero (a : ℝ))
  div_cancel a hn := Subtype.ext (DivisibleBy.div_cancel (a : ℝ) hn)

/-- The printed support-supremum-zero implication in LM24, Remark 6.5.1 is false for the
multiplicative identity. -/
theorem one_almostIrreducible_counterexample :
    IsAlmostIrreducible (1 : RealExponentSeries) ∧
      realSupportSup RealExponentSubgroup (1 : RealExponentSeries) = 0 ∧
        ¬Irreducible (1 : RealExponentSeries) :=
  ⟨one_isAlmostIrreducible,
    realSupportSup_one RealExponentSubgroup (K := ℚ), not_irreducible_one⟩

/-- The exponent `-1`, regarded as an element of the full real exponent subgroup. -/
def minusOneExponent : RealExponentSubgroup := ⟨-1, Set.mem_univ _⟩

/-- The exponent `-1` is nonpositive. -/
theorem minusOneExponent_nonpos : minusOneExponent ≤ 0 := by
  change (-1 : ℝ) ≤ 0
  norm_num

/-- The nonconstant monomial `t⁻¹`. -/
def almostIrreducibleNegativeMonomial : RealExponentSeries :=
  single minusOneExponent 1 minusOneExponent_nonpos

/-- The support of `t⁻¹` is exactly the singleton containing `-1`. -/
theorem almostIrreducibleNegativeMonomial_support :
    (almostIrreducibleNegativeMonomial : ℚ⟦RealExponentSubgroup⟧).support =
      {minusOneExponent} := by
  rw [almostIrreducibleNegativeMonomial, coe_single,
    HahnSeries.support_single_of_ne one_ne_zero]

/-- The real support supremum of `t⁻¹` is `-1`. -/
theorem almostIrreducibleNegativeMonomial_realSupportSup :
    realSupportSup RealExponentSubgroup almostIrreducibleNegativeMonomial = (-1 : ℝ) := by
  rw [almostIrreducibleNegativeMonomial]
  exact realSupportSup_single RealExponentSubgroup one_ne_zero
    minusOneExponent_nonpos

/-- The strict-negative-supremum clause of LM24, Remark 6.5.1 rejects the nonconstant
monomial `t⁻¹` as irreducible. -/
theorem almostIrreducibleNegativeMonomial_not_irreducible :
    ¬Irreducible almostIrreducibleNegativeMonomial := by
  apply not_irreducible_of_realSupportSup_lt_zero
  rw [almostIrreducibleNegativeMonomial_realSupportSup]
  norm_num

end

end Tests
