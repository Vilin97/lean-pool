/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Factorization.InfiniteSupport

/-!
# API checks for infinite-support factorisation

The zero series separates `HasOnlyUnitFiniteSupportDivisors` from a predicate that ignores the
zero finite-support divisor. The nonzero-scalar client runs the full parameterized factorisation
theorem and uses its Cantor-term bound to force the factor list to be empty. Thus the client
checks the degree-zero branch, the normalized maximal finite-support factor in the product, and
the exact orientation of the numerical bound.

Pairwise gcd existence and the unit classification of the finite-support ring remain explicit
parameters of the generic theorem; the coefficient field has characteristic zero.
-/

open scoped HahnSeries NatOrdinal

universe v

namespace Tests

public noncomputable section

open Berarducci

/-- Zero does not have only unit finite-support divisors because zero itself is a nonunit
finite-support divisor. -/
theorem zero_not_hasOnlyUnitFiniteSupportDivisors :
    ¬HasOnlyUnitFiniteSupportDivisors (0 : Series ℚ) := by
  intro hzero
  have hzeroSpec := (hasOnlyUnitFiniteSupportDivisors_iff (0 : Series ℚ)).mp hzero
  exact not_isUnit_zero (hzeroSpec 0 (dvd_zero 0))

/-- The factorisation theorem produces no infinite-support factor for a nonzero scalar series. -/
theorem scalar_factorization_has_no_infinite_support_factors {K : Type v} [Field K] [CharZero K]
    (hgcd : ∀ p q : FiniteSupportRing (K := K),
      ∃ d : FiniteSupportRing (K := K),
        ∀ e : FiniteSupportRing (K := K), e ∣ p ∧ e ∣ q ↔ e ∣ d)
    (hunits : ∀ p : FiniteSupportRing (K := K),
      IsUnit p ↔ ∃ a : K, a ≠ 0 ∧
        p = HahnSeries.Nonpositive.finiteSupportScalarHom (G := ℝ) a)
    {k : K} (hk : k ≠ 0) :
    ∃ (factors : List (Series K)) (a : K),
      a ≠ 0 ∧
        HahnSeries.Nonpositive.C k =
          HahnSeries.Nonpositive.C a *
            (seriesNormalizedMaximalFiniteSupportDivisor
              (HahnSeries.Nonpositive.C k) : Series K) *
              factors.prod ∧
        (∀ c ∈ factors,
          Irreducible c ∧ (c : K⟦ℝ⟧).support.Infinite) ∧
        factors = [] := by
  have hb : (HahnSeries.Nonpositive.C k : Series K) ≠ 0 := by
    intro hzero
    apply HahnSeries.C_ne_zero (R := K) (Γ := ℝ) hk
    simpa [HahnSeries.Nonpositive.coe_C] using congrArg
      (fun b : Series K ↦ (b : K⟦ℝ⟧)) hzero
  obtain ⟨a, factors, ha, hfactor, hfactors, hbound⟩ :=
    exists_series_infinite_support_factorization_of_exists_gcd hgcd hunits hb
  have hbDegree :
      ((HahnSeries.Nonpositive.C k : Series K) : K⟦ℝ⟧).degree = 0 := by
    rw [HahnSeries.degree_eq_zero]
    refine ⟨?_, ?_⟩
    · simpa only [HahnSeries.Nonpositive.coe_C] using
        HahnSeries.C_ne_zero (R := K) (Γ := ℝ) hk
    · rw [HahnSeries.Nonpositive.coe_C, HahnSeries.C_apply,
        HahnSeries.support_single_of_ne hk]
      exact Set.finite_singleton 0
  have hcount :
      HahnSeries.degreeCantorTermCount
          ((HahnSeries.Nonpositive.C k : Series K) : K⟦ℝ⟧) = 0 := by
    rw [HahnSeries.degreeCantorTermCount_eq_of_degree hbDegree,
      NatOrdinal.cantorTermCount_zero]
  have hlength : factors.length = 0 :=
    Nat.eq_zero_of_le_zero (hcount ▸ hbound)
  exact ⟨factors, a, ha, hfactor, hfactors,
    List.length_eq_zero_iff.mp hlength⟩

end

end Tests
