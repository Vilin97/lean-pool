/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Factorization.NormalizedHPartMultiplicativity

/-!
# API checks for multiplication of normalized exponent-subgroup parts

For the trivial exponent subgroup, every normalized finite-support subgroup series is `1`.
The real finite-support series `1 + t⁻¹` is nevertheless nonconstant, so its normalized trivial-
subgroup part is genuinely smaller than the original series. Applying the multiplication theorem
to its square checks both directions of the divisor characterization and the product orientation.
-/

open scoped HahnSeries

namespace Tests

public noncomputable section

open HahnSeries.Nonpositive

/-- The zero exponent subgroup used to test multiplicativity of normalized factors. -/
abbrev TrivialExponentSubgroup : AddSubgroup ℝ := ⊥

/-- Every normalized finite-support series over the trivial exponent subgroup is the identity. -/
theorem normalized_trivialExponentSubgroup_eq_one
    (p : ConstantTermOneFiniteSupport (G := TrivialExponentSubgroup) (K := ℚ)) :
    p = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply HahnSeries.coeff_injective
  funext g
  have hg : g = 0 := Subsingleton.elim _ _
  subst g
  simpa [constantCoeff_apply] using p.constantCoeff_eq_one

/-- Normalized divisors over the trivial exponent subgroup satisfy the required product
refinement property. -/
theorem trivialExponentSubgroup_hasNormalizedHDivisorRefinement :
    HasNormalizedHDivisorRefinement TrivialExponentSubgroup (K := ℚ) := by
  rw [hasNormalizedHDivisorRefinement_iff]
  intro p q r _
  refine ⟨1, 1, ?_, ?_, ?_⟩ <;>
    simp [normalized_trivialExponentSubgroup_eq_one r]

/-- The identity is the normalized trivial-subgroup part of every finite-support real series. -/
theorem one_isNormalizedTrivialExponentSubgroupPart
    (p : FiniteSupportRing (G := ℝ) (K := ℚ)) :
    IsNormalizedHPart TrivialExponentSubgroup p 1 := by
  rw [isNormalizedHPart_iff]
  intro r
  rw [normalized_trivialExponentSubgroup_eq_one r]
  simp

/-- The real exponent `-1` as a nonpositive exponent. -/
def normalizedPartMinusOneExponent : exponentMonoid ℝ :=
  ⟨-1, show (-1 : ℝ) ≤ 0 by norm_num⟩

/-- The nonconstant finite-support real series `1 + t⁻¹`. -/
def normalizedPartNonconstantSeries : FiniteSupportRing (G := ℝ) (K := ℚ) :=
  1 + finiteSupportMonomial normalizedPartMinusOneExponent

/-- The fixture `1 + t⁻¹` is not the identity. -/
theorem normalizedPartNonconstantSeries_ne_one :
    normalizedPartNonconstantSeries ≠ 1 := by
  intro h
  have hcoeff := congrArg
    (fun p : FiniteSupportRing (G := ℝ) (K := ℚ) ↦
      (((p : HahnSeries.Nonpositive ℝ ℚ) : ℚ⟦ℝ⟧).coeff (-1))) h
  norm_num [normalizedPartNonconstantSeries, normalizedPartMinusOneExponent,
    coe_finiteSupportMonomial] at hcoeff

/-- The normalized trivial-subgroup part is not merely the original nonconstant series. -/
theorem normalizedPartNonconstantSeries_ne_embeddedPart :
    normalizedPartNonconstantSeries ≠
      finiteSupportToReal TrivialExponentSubgroup
        (1 : FiniteSupportRing (G := TrivialExponentSubgroup) (K := ℚ)) := by
  simpa using normalizedPartNonconstantSeries_ne_one

/-- The product theorem computes the normalized trivial-subgroup part of
`(1 + t⁻¹)²` as `1`. -/
theorem normalizedPartNonconstantSeries_mul_isNormalizedPart :
    IsNormalizedHPart TrivialExponentSubgroup
      (normalizedPartNonconstantSeries * normalizedPartNonconstantSeries) 1 := by
  simpa using
    (isNormalizedHPart_mul TrivialExponentSubgroup
      trivialExponentSubgroup_hasNormalizedHDivisorRefinement
      (one_isNormalizedTrivialExponentSubgroupPart normalizedPartNonconstantSeries)
      (one_isNormalizedTrivialExponentSubgroupPart normalizedPartNonconstantSeries))

end

end Tests
