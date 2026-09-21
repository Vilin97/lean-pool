/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Factorization.NormalizedMaximalFinite

import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.Valuation.AssociatedGradedDivisibility

/-!
# Multiplicativity of normalized maximal finite-support divisors

This module proves the field-generic reduction underlying LM24, Corollary 6.3.7. If every
finite-support divisor of a product in `RV̂` factors into finite-support divisors of the two
factors, then the normalized maximal finite-support divisor is multiplicative.

Pairwise greatest-common-divisor existence and the classification of finite-support units remain
explicit hypotheses; the statements module discharges both over the real exponents.
-/

open scoped DirectSum HahnSeries NatOrdinal

universe v

namespace Berarducci

public noncomputable section

open HahnSeries.Nonpositive

variable {K : Type v} [Field K] [CharZero K]

/-- The normalized maximal finite-support divisor is multiplicative whenever finite-support
divisors of products admit compatible finite-support factorisations. -/
theorem gradedNormalizedMaximalFiniteSupportDivisor_mul_of_factorization
    (hgcd : ∀ p q : FiniteSupportRing (K := K),
      ∃ d : FiniteSupportRing (K := K),
        ∀ e : FiniteSupportRing (K := K), e ∣ p ∧ e ∣ q ↔ e ∣ d)
    (hunits : ∀ u : FiniteSupportRing (K := K),
      IsUnit u ↔ ∃ k : K, k ≠ 0 ∧
        u = finiteSupportScalarHom (G := ℝ) k)
    (hfactor : ∀ (p : FiniteSupportRing (K := K))
        (B C : DegreeGraded K),
      finiteSupportGradedEmbedding K p ∣ B * C →
        ∃ p₁ p₂ : FiniteSupportRing (K := K),
          p = p₁ * p₂ ∧
            finiteSupportGradedEmbedding K p₁ ∣ B ∧
            finiteSupportGradedEmbedding K p₂ ∣ C)
    (B C : DegreeGraded K) :
    gradedNormalizedMaximalFiniteSupportDivisor (B * C) =
      gradedNormalizedMaximalFiniteSupportDivisor B *
        gradedNormalizedMaximalFiniteSupportDivisor C := by
  let pB := gradedNormalizedMaximalFiniteSupportDivisor B
  let pC := gradedNormalizedMaximalFiniteSupportDivisor C
  have hmaxB := (isNormalizedGradedMaximalFiniteSupportDivisor_iff B _).mp
    (gradedNormalizedMaximalFiniteSupportDivisor_is_of_exists_gcd hgcd B)
  have hmaxC := (isNormalizedGradedMaximalFiniteSupportDivisor_iff C _).mp
    (gradedNormalizedMaximalFiniteSupportDivisor_is_of_exists_gcd hgcd C)
  have hmaxBC := (isNormalizedGradedMaximalFiniteSupportDivisor_iff (B * C) _).mp
    (gradedNormalizedMaximalFiniteSupportDivisor_is_of_exists_gcd hgcd (B * C))
  apply gradedNormalizedMaximalFiniteSupportDivisor_eq_of_is hgcd hunits
  rw [isNormalizedGradedMaximalFiniteSupportDivisor_iff]
  constructor
  · intro q
    constructor
    · intro hq
      obtain ⟨q₁, q₂, hqFactor, hq₁, hq₂⟩ := hfactor q B C hq
      rw [hqFactor]
      exact mul_dvd_mul ((hmaxB.1 q₁).mp hq₁) ((hmaxC.1 q₂).mp hq₂)
    · intro hq
      apply (hmaxBC.1 q).mpr
      exact hq.trans
        (gradedNormalizedMaximalFiniteSupportDivisor_mul_dvd_of_exists_gcd hgcd B C)
  · by_cases hBC : B * C = 0
    · apply Or.inl
      refine ⟨hBC, ?_⟩
      change pB * pC = 0
      rcases eq_zero_or_eq_zero_of_mul_eq_zero hBC with hB | hC
      · have hpB : pB = 0 := by
          rcases hmaxB.2 with h | h
          · exact h.2
          · exact (h.1 hB).elim
        rw [hpB, zero_mul]
      · have hpC : pC = 0 := by
          rcases hmaxC.2 with h | h
          · exact h.2
          · exact (h.1 hC).elim
        rw [hpC, mul_zero]
    · apply Or.inr
      refine ⟨hBC, ?_⟩
      apply IsMonicFiniteSupport.mul
      · apply gradedNormalizedMaximalFiniteSupportDivisor_isMonic_of_ne_zero hgcd
        intro hB
        apply hBC
        rw [hB, zero_mul]
      · apply gradedNormalizedMaximalFiniteSupportDivisor_isMonic_of_ne_zero hgcd
        intro hC
        apply hBC
        rw [hC, mul_zero]

end

end Berarducci
