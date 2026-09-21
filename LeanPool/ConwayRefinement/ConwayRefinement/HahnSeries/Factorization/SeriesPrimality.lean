/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Factorization.NormalizedSeriesMaximalFinite

import Mathlib.Algebra.GCDMonoid.Basic

/-!
# Primality of finite-support elements in the Hahn-series ring

This module proves the field-generic reduction underlying LM24, Corollary 6.3.9. The stronger
theorem retains both factors inside the finite-support subring. Primality of their images in the
Hahn-series ring is derived from that witness theorem.
-/

open scoped HahnSeries

universe v

namespace Berarducci

public noncomputable section

open HahnSeries.Nonpositive

variable {K : Type v} [Field K] [CharZero K]

/-- A finite-support divisor of a product of Hahn series factors into finite-support divisors of
the two factors, assuming multiplicativity of normalized maximal finite-support divisors. -/
theorem finiteSupportSeries_exists_factor_dvd_of_maximalMultiplicative
    (hgcd : ∀ p q : FiniteSupportRing (K := K),
      ∃ d : FiniteSupportRing (K := K),
        ∀ e : FiniteSupportRing (K := K), e ∣ p ∧ e ∣ q ↔ e ∣ d)
    (hmaxMul : ∀ b c : Series K,
      seriesNormalizedMaximalFiniteSupportDivisor (b * c) =
        seriesNormalizedMaximalFiniteSupportDivisor b *
          seriesNormalizedMaximalFiniteSupportDivisor c)
    (p : FiniteSupportRing (K := K)) (b c : Series K)
    (hp : (p : Series K) ∣ b * c) :
    ∃ p₁ p₂ : FiniteSupportRing (K := K),
      p = p₁ * p₂ ∧ (p₁ : Series K) ∣ b ∧ (p₂ : Series K) ∣ c := by
  classical
  have hmaxBC := (isNormalizedSeriesMaximalFiniteSupportDivisor_iff
    (b * c) (seriesNormalizedMaximalFiniteSupportDivisor (b * c))).mp
      (seriesNormalizedMaximalFiniteSupportDivisor_is_of_exists_gcd hgcd (b * c))
  have hpMax : p ∣ seriesNormalizedMaximalFiniteSupportDivisor (b * c) :=
    (hmaxBC.1 p).mp hp
  rw [hmaxMul b c] at hpMax
  letI : GCDMonoid (FiniteSupportRing (K := K)) :=
    gcdMonoidOfExistsGCD hgcd
  obtain ⟨p₁, p₂, hp₁, hp₂, hpFactor⟩ :=
    exists_dvd_and_dvd_of_dvd_mul hpMax
  have hmaxB := (isNormalizedSeriesMaximalFiniteSupportDivisor_iff
    b (seriesNormalizedMaximalFiniteSupportDivisor b)).mp
      (seriesNormalizedMaximalFiniteSupportDivisor_is_of_exists_gcd hgcd b)
  have hmaxC := (isNormalizedSeriesMaximalFiniteSupportDivisor_iff
    c (seriesNormalizedMaximalFiniteSupportDivisor c)).mp
      (seriesNormalizedMaximalFiniteSupportDivisor_is_of_exists_gcd hgcd c)
  exact ⟨p₁, p₂, hpFactor,
    (hmaxB.1 p₁).mpr hp₁, (hmaxC.1 p₂).mpr hp₂⟩

/-- Every finite-support element is primal in the Hahn-series ring under the same explicit
prerequisites. -/
theorem finiteSupportSeries_isPrimal_of_maximalMultiplicative
    (hgcd : ∀ p q : FiniteSupportRing (K := K),
      ∃ d : FiniteSupportRing (K := K),
        ∀ e : FiniteSupportRing (K := K), e ∣ p ∧ e ∣ q ↔ e ∣ d)
    (hmaxMul : ∀ b c : Series K,
      seriesNormalizedMaximalFiniteSupportDivisor (b * c) =
        seriesNormalizedMaximalFiniteSupportDivisor b *
          seriesNormalizedMaximalFiniteSupportDivisor c)
    (p : FiniteSupportRing (K := K)) :
    IsPrimal (p : Series K) := by
  intro b c hp
  obtain ⟨p₁, p₂, hpFactor, hp₁, hp₂⟩ :=
    finiteSupportSeries_exists_factor_dvd_of_maximalMultiplicative hgcd hmaxMul p b c hp
  refine ⟨(p₁ : Series K), (p₂ : Series K), hp₁, hp₂, ?_⟩
  exact congrArg
    (finiteSupportSubring (G := ℝ) (K := K)).subtype hpFactor

end

end Berarducci
