/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Factorization.FiniteSupportFactorUniqueness

import Mathlib.Tactic.NormNum

/-!
# API checks for LM24 Section 6.4

The empty-list fixture certifies that the source natural number `n` may be zero. The sign-change
fixture gives two factorisations of the same series with finite-support factors `1` and `-1`.
Those factors are unequal but differ by a nonzero coefficient scalar, separating the source's
uniqueness up to scalar from the stronger and false assertion of literal equality.

The full uniqueness statement retains every unresolved mathematical prerequisite as an explicit
hypothesis.
-/

open scoped HahnSeries

namespace Tests

public noncomputable section

open Berarducci HahnSeries.Nonpositive

/-- The multiplicative identity has a Section 6.4 factorisation with no infinite-support
factors. -/
theorem one_empty_infiniteSupportIrreducibleFactorization :
    IsInfiniteSupportIrreducibleFactorization
      (1 : Series ℚ) (1 : FiniteSupportRing (K := ℚ)) [] := by
  rw [isInfiniteSupportIrreducibleFactorization_iff]
  simp

private theorem neg_irreducible {c : Series ℚ} (hc : Irreducible c) :
    Irreducible (-c) :=
  Associated.irreducible ⟨-1, mul_neg_one c⟩ hc

private theorem neg_support_infinite {c : Series ℚ}
    (hc : (c : ℚ⟦ℝ⟧).support.Infinite) :
    ((-c : Series ℚ) : ℚ⟦ℝ⟧).support.Infinite := by
  change (-((c : Series ℚ) : ℚ⟦ℝ⟧)).support.Infinite
  simpa only [HahnSeries.support_neg] using hc

/-- A sign change may be transferred between the finite-support factor and the sole listed
infinite-support factor. -/
theorem neg_one_neg_factorization {c : Series ℚ}
    (hcIrreducible : Irreducible c)
    (hcInfinite : (c : ℚ⟦ℝ⟧).support.Infinite) :
    IsInfiniteSupportIrreducibleFactorization c
      (-1 : FiniteSupportRing (K := ℚ)) [-c] := by
  rw [isInfiniteSupportIrreducibleFactorization_iff]
  constructor
  · simp
  · simp only [List.mem_singleton, forall_eq]
    exact ⟨neg_irreducible hcIrreducible, neg_support_infinite hcInfinite⟩

/-- The two sign-related finite-support factors are not literally equal. -/
theorem neg_one_finiteSupportFactor_ne_one :
    (-1 : FiniteSupportRing (K := ℚ)) ≠ 1 := by
  intro h
  have hcoeff := congrArg
    (fun p : FiniteSupportRing (K := ℚ) ↦
      ((p : Series ℚ) : ℚ⟦ℝ⟧).coeff 0) h
  norm_num at hcoeff

/-- The Section 6.4 uniqueness theorem identifies the sign-related finite-support factors up to
a nonzero coefficient scalar. -/
theorem sign_changed_factorizations_are_unique_up_to_scalar
    (hgcd : ∀ p q : FiniteSupportRing (K := ℚ),
      ∃ d : FiniteSupportRing (K := ℚ),
        ∀ e : FiniteSupportRing (K := ℚ), e ∣ p ∧ e ∣ q ↔ e ∣ d)
    (hunits : ∀ p : FiniteSupportRing (K := ℚ),
      IsUnit p ↔ ∃ k : ℚ, k ≠ 0 ∧
        p = finiteSupportScalarHom (G := ℝ) k)
    (hmaxMul : ∀ b c : Series ℚ,
      seriesNormalizedMaximalFiniteSupportDivisor (b * c) =
        seriesNormalizedMaximalFiniteSupportDivisor b *
          seriesNormalizedMaximalFiniteSupportDivisor c)
    {c : Series ℚ} (hcIrreducible : Irreducible c)
    (hcInfinite : (c : ℚ⟦ℝ⟧).support.Infinite) :
    ∃ k : ℚ, k ≠ 0 ∧
      (-1 : FiniteSupportRing (K := ℚ)) =
        finiteSupportScalarHom (G := ℝ) k * 1 := by
  have hpositive : IsInfiniteSupportIrreducibleFactorization c
      (1 : FiniteSupportRing (K := ℚ)) [c] := by
    rw [isInfiniteSupportIrreducibleFactorization_iff]
    constructor
    · simp
    · simp only [List.mem_singleton, forall_eq]
      exact ⟨hcIrreducible, hcInfinite⟩
  exact finiteSupportFactor_eq_scalar_mul_of_factorizations
    (b := c) (p := (1 : FiniteSupportRing (K := ℚ)))
    (q := (-1 : FiniteSupportRing (K := ℚ)))
    (factors := [c]) (otherFactors := [-c])
      hgcd hunits hmaxMul hpositive (neg_one_neg_factorization hcIrreducible hcInfinite)

end

end Tests
