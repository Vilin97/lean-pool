/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Factorization.NormalizedHPart

/-!
# API checks for normalized exponent-subgroup parts

The identity fixture exercises the existence-and-uniqueness predicate for a case that is proved
without Ritt factorisation. The second fixture constructs the genuinely nonconstant normalized
series `1 + t⁻¹` and proves that it is not the normalized subgroup part of `1`, separating the
divisor-characterization predicate from mere constant-term normalization.
-/

open scoped HahnSeries

namespace Tests

public noncomputable section

open HahnSeries.Nonpositive

/-- The full real exponent subgroup used to test normalized finite-support factors. -/
abbrev HPartExponentSubgroup : AddSubgroup ℝ := ⊤

/-- The ring of rational Hahn series with finite nonpositive real support. -/
abbrev HPartFiniteSupportRing :=
  FiniteSupportRing (G := HPartExponentSubgroup) (K := ℚ)

/-- Finite-support rational Hahn series with nonpositive real exponents and constant coefficient
one. -/
abbrev HPartNormalizedFiniteSupport :=
  ConstantTermOneFiniteSupport (G := HPartExponentSubgroup) (K := ℚ)

/-- The exponent `-1` in the nonpositive exponent monoid of the full real subgroup. -/
def hPartMinusOneExponent : exponentMonoid HPartExponentSubgroup :=
  ⟨⟨-1, Set.mem_univ _⟩, by
    change (-1 : ℝ) ≤ 0
    norm_num⟩

/-- The underlying subgroup exponent `-1` differs from zero. -/
theorem hPartMinusOneExponent_coe_ne_zero :
    (hPartMinusOneExponent : HPartExponentSubgroup) ≠ 0 := by
  intro h
  have hval := congrArg (fun g : HPartExponentSubgroup ↦ (g : ℝ)) h
  norm_num [hPartMinusOneExponent] at hval

/-- The normalized nonconstant finite-support series `1 + t⁻¹`. -/
def onePlusNegativeMonomial : HPartNormalizedFiniteSupport :=
  ⟨1 + finiteSupportMonomial (K := ℚ) hPartMinusOneExponent, by
    rw [mem_constantTermOneSubmonoid_iff]
    change constantCoeff
      ((1 : HahnSeries.Nonpositive HPartExponentSubgroup ℚ) +
        (finiteSupportMonomial (K := ℚ) hPartMinusOneExponent :
          HahnSeries.Nonpositive HPartExponentSubgroup ℚ)) = 1
    rw [map_add, map_one, constantCoeff_apply,
      coe_finiteSupportMonomial]
    rw [HahnSeries.coeff_single_of_ne
      hPartMinusOneExponent_coe_ne_zero.symm]
    simp⟩

/-- The normalized series `1 + t⁻¹` is not the identity. -/
theorem onePlusNegativeMonomial_ne_one :
    onePlusNegativeMonomial ≠ 1 := by
  intro h
  have hcoeff := congrArg
    (fun p : HPartNormalizedFiniteSupport ↦
      ((((p : HPartFiniteSupportRing) :
        HahnSeries.Nonpositive HPartExponentSubgroup ℚ) :
          ℚ⟦HPartExponentSubgroup⟧).coeff hPartMinusOneExponent)) h
  simp [onePlusNegativeMonomial, hPartMinusOneExponent,
    HahnSeries.Nonpositive.coe_finiteSupportMonomial] at hcoeff

/-- The normalized `H`-part of one exists uniquely and is one. -/
theorem one_unique_normalizedHPart :
    ∃! q : HPartNormalizedFiniteSupport,
      IsNormalizedHPart HPartExponentSubgroup
        (1 : FiniteSupportRing (G := ℝ) (K := ℚ)) q :=
  existsUnique_normalizedHPart_one HPartExponentSubgroup

/-- Constant-term normalization alone does not make `1 + t⁻¹` the normalized `H`-part of
one. -/
theorem onePlusNegativeMonomial_not_normalizedHPart_one :
    ¬IsNormalizedHPart HPartExponentSubgroup
      (1 : FiniteSupportRing (G := ℝ) (K := ℚ))
        onePlusNegativeMonomial := by
  intro hpart
  apply onePlusNegativeMonomial_ne_one
  apply ConstantTermOneFiniteSupport.eq_one_of_finiteSupportToReal_dvd_one
  exact (Iff.mp (isNormalizedHPart_iff HPartExponentSubgroup
    (1 : FiniteSupportRing (G := ℝ) (K := ℚ)) onePlusNegativeMonomial) hpart
      onePlusNegativeMonomial).mpr (dvd_refl _)

end

end Tests
