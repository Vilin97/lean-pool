/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.FiniteSupport

import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.FiniteSupportGCDProof
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.FiniteSupportUnit

/-!
# API checks for LM24, Fact 2.5.2

The monomial `t⁻¹` is a unit in the finite-support ring on the whole exponent group `ℤ`, with
inverse `t`. The same underlying Hahn series is not a unit in the nonpositive finite-support
ring, because its inverse has positive exponent. This distinguishes LM24's unit statement from
the nearby incorrect statement for the full group ring.

The gcd fixture uses the pair `(0, t⁻¹)`, with a witness associated to `t⁻¹`. Its exact
characterization is `e ∣ 0 ∧ e ∣ t⁻¹ ↔ e ∣ d`. This checks the zero boundary and the
greatest-common-divisor orientation in the second part of Fact 2.5.2.
-/

open scoped HahnSeries

public noncomputable section

namespace Tests

/-- The ring of rational finite-support Hahn series with nonpositive integer exponents. -/
abbrev IntegerNonpositiveFiniteSupportRing :=
  HahnSeries.Nonpositive.finiteSupportSubring (G := ℤ) (K := ℚ)

/-- The ring of rational finite-support Hahn series with arbitrary integer exponents. -/
abbrev IntegerFiniteSupportRing :=
  (HahnSeries.finiteSupportSubring : Subring ℚ⟦ℤ⟧)

/-- The nonpositive exponent `-1`. -/
def negativeExponent : HahnSeries.Nonpositive.exponentMonoid ℤ :=
  ⟨-1, show (-1 : ℤ) ≤ 0 by norm_num⟩

/-- The monomial `t⁻¹` in the nonpositive finite-support ring. -/
def nonpositiveNegativeMonomial : IntegerNonpositiveFiniteSupportRing :=
  HahnSeries.Nonpositive.finiteSupportMonomial (K := ℚ) negativeExponent

/-- The monomial `t⁻¹` is not a unit in the nonpositive finite-support ring. -/
theorem nonpositiveNegativeMonomial_not_isUnit :
    ¬ IsUnit nonpositiveNegativeMonomial := by
  rw [HahnSeries.Nonpositive.isUnit_finiteSupport_iff_exists_scalar]
  rintro ⟨k, -, h⟩
  have hcoeff := congrArg
    (fun p : IntegerNonpositiveFiniteSupportRing ↦
      (((p : HahnSeries.Nonpositive ℤ ℚ) : ℚ⟦ℤ⟧).coeff (-1))) h
  simp [nonpositiveNegativeMonomial, negativeExponent] at hcoeff

/-- The monomial `t⁻¹` in the finite-support ring on the whole exponent group. -/
def fullNegativeMonomial : IntegerFiniteSupportRing :=
  ⟨HahnSeries.single (-1) 1, by
    rw [HahnSeries.mem_finiteSupportSubring_iff]
    exact Set.Finite.subset (Set.finite_singleton (-1))
      HahnSeries.support_single_subset⟩

/-- The monomial `t` in the finite-support ring on the whole exponent group. -/
def fullPositiveMonomial : IntegerFiniteSupportRing :=
  ⟨HahnSeries.single 1 1, by
    rw [HahnSeries.mem_finiteSupportSubring_iff]
    exact Set.Finite.subset (Set.finite_singleton 1)
      HahnSeries.support_single_subset⟩

theorem fullNegativeMonomial_mul_fullPositiveMonomial :
    fullNegativeMonomial * fullPositiveMonomial = 1 := by
  apply Subtype.ext
  simp [fullNegativeMonomial, fullPositiveMonomial, HahnSeries.single_mul_single]

theorem fullPositiveMonomial_mul_fullNegativeMonomial :
    fullPositiveMonomial * fullNegativeMonomial = 1 := by
  apply Subtype.ext
  simp [fullNegativeMonomial, fullPositiveMonomial, HahnSeries.single_mul_single]

/-- In the full exponent-group finite-support ring, `t⁻¹` is a unit with inverse `t`. -/
theorem fullNegativeMonomial_isUnit : IsUnit fullNegativeMonomial := by
  exact ⟨{
    val := fullNegativeMonomial
    inv := fullPositiveMonomial
    val_inv := fullNegativeMonomial_mul_fullPositiveMonomial
    inv_val := fullPositiveMonomial_mul_fullNegativeMonomial
  }, rfl⟩

/-- The full-ring and nonpositive-ring fixtures have the same underlying Hahn series. -/
theorem fullNegativeMonomial_eq_nonpositiveNegativeMonomial :
    (fullNegativeMonomial : ℚ⟦ℤ⟧) =
      ((nonpositiveNegativeMonomial : HahnSeries.Nonpositive ℤ ℚ) : ℚ⟦ℤ⟧) := by
  simp [fullNegativeMonomial, nonpositiveNegativeMonomial, negativeExponent]

/-- The gcd supplied for `(0, t⁻¹)` is associated to `t⁻¹` and satisfies the exact defining
orientation from LM24, Fact 2.5.2. -/
theorem finiteSupportGCD_zero_left :
    ∃ d : IntegerNonpositiveFiniteSupportRing,
      (d ∣ nonpositiveNegativeMonomial ∧ nonpositiveNegativeMonomial ∣ d) ∧
        ∀ e : IntegerNonpositiveFiniteSupportRing,
          e ∣ 0 ∧ e ∣ nonpositiveNegativeMonomial ↔ e ∣ d := by
  obtain ⟨d, hd⟩ := HahnSeries.Nonpositive.finiteSupport_pairwise_gcd_exists
    (0 : IntegerNonpositiveFiniteSupportRing) nonpositiveNegativeMonomial
  refine ⟨d, ⟨?_, ?_⟩, hd⟩
  · exact ((hd d).mpr dvd_rfl).2
  · exact (hd nonpositiveNegativeMonomial).mp ⟨dvd_zero _, dvd_rfl⟩

end Tests
