/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
import LeanPool.OddPrimeValuationDistribution.ValuationBlocks
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Bivariate generating function for odd-prime valuation distributions

For `p = 2 * half + 1`, the coefficient of `T ^ k * X ^ r` counts
`0 ≤ n < p ^ k` with `ν_p (centralBinom n) = r`.  The theorem below is the
denominator-cleared, subtraction-free form of

`(1 - X * T) / (1 - (half + 1) * (1 + X) * T + p * X * T ^ 2)`.
-/

namespace OddPrimeValuationDistribution

/-- Bivariate generating series for complete odd-base valuation blocks. -/
noncomputable def oddPrimeValuationGeneratingSeries (half : ℕ) :
    PowerSeries (Polynomial ℕ) :=
  PowerSeries.mk (oddPrimeValuationPolynomial half)

/-- Headline rational generating-function identity for every odd prime.  The
outer `PowerSeries.X` records block length and the inner `Polynomial.X`
records exact valuation. -/
theorem oddPrimeValuationGeneratingSeries_identity
    (half : ℕ) (hhalf : 0 < half) [Fact (oddBase half).Prime] :
    oddPrimeValuationGeneratingSeries half +
          PowerSeries.C ((oddBase half : Polynomial ℕ) * Polynomial.X) *
            ((PowerSeries.X : PowerSeries (Polynomial ℕ)) ^ 2 *
              oddPrimeValuationGeneratingSeries half) +
          PowerSeries.C Polynomial.X * PowerSeries.X =
      1 + PowerSeries.C
          (((half + 1 : ℕ) : Polynomial ℕ) * (1 + Polynomial.X)) *
        (PowerSeries.X * oddPrimeValuationGeneratingSeries half) := by
  apply PowerSeries.ext
  intro coefficient
  rcases coefficient with _ | _ | length
  · simp only [map_add, PowerSeries.coeff_C_mul]
    simp [oddPrimeValuationGeneratingSeries,
      oddPrimeValuationPolynomial_eq_carryPolynomial half hhalf,
      PowerSeries.coeff_X_pow_mul']
  · simp only [map_add, PowerSeries.coeff_C_mul]
    simp [oddPrimeValuationGeneratingSeries,
      oddPrimeValuationPolynomial_eq_carryPolynomial half hhalf,
      PowerSeries.coeff_X_pow_mul']
    ring
  · simp only [map_add, PowerSeries.coeff_C_mul]
    simpa [oddPrimeValuationGeneratingSeries, add_assoc,
      PowerSeries.coeff_X, PowerSeries.coeff_X_pow_mul'] using
        oddPrimeValuationPolynomial_recurrence half hhalf length

end OddPrimeValuationDistribution
