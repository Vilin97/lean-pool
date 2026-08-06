/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
import LeanPool.OddPrimeValuationDistribution.GeneratingFunction
import Mathlib.Tactic.Ring

/-!
# Closed low-valuation counts for every odd prime

The full distribution specializes to compact formulas at valuations zero and
one.  These are arithmetic counts on the complete block below `p ^ k`, not
asymptotic estimates.
-/

namespace OddPrimeValuationDistribution

open Polynomial

/-- The zero-carry coefficient in odd base `2 * half + 1`. -/
theorem coeff_zero_oddCarryPolynomial (half length : ℕ) :
    (oddCarryPolynomial half length).coeff 0 = (half + 1) ^ length := by
  induction length with
  | zero => simp
  | succ length ih =>
      change
        (oddCarryPolynomialFrom half 0 length).coeff 0 =
          (half + 1) ^ length at ih
      change
        (oddCarryPolynomialFrom half 0 (length + 1)).coeff 0 =
          (half + 1) ^ (length + 1)
      rw [oddCarryPolynomialFrom_zeroCarry_succ]
      have hshift :
          ((half : Polynomial ℕ) * X *
              oddCarryPolynomialFrom half 1 length).coeff 0 = 0 := by
        simp
      rw [Polynomial.coeff_add, hshift, add_zero]
      simp only [Polynomial.coeff_natCast_mul]
      rw [ih, pow_succ]
      norm_num
      ring

/-- Zero additional carries from incoming carry one, for positive word
length. -/
lemma coeff_zero_oddCarryPolynomialFrom_one_succ (half length : ℕ) :
    (oddCarryPolynomialFrom half 1 (length + 1)).coeff 0 =
      half * (half + 1) ^ length := by
  rw [oddCarryPolynomialFrom_oneCarry_succ]
  have hshift :
      (((half + 1 : ℕ) : Polynomial ℕ) * X *
          oddCarryPolynomialFrom half 1 length).coeff 0 = 0 := by
    simp
  rw [Polynomial.coeff_add, hshift, add_zero]
  simp only [Polynomial.coeff_natCast_mul]
  have h := coeff_zero_oddCarryPolynomial half length
  change
    (oddCarryPolynomialFrom half 0 length).coeff 0 =
      (half + 1) ^ length at h
  rw [h]
  norm_num

/-- Exact one-carry coefficient for every odd base, parameterized by block
length `length + 2`. -/
theorem coeff_one_oddCarryPolynomial_add_two (half length : ℕ) :
    (oddCarryPolynomial half (length + 2)).coeff 1 =
      half * (half + 1) ^ (length + 1) +
        (length + 1) * half ^ 2 * (half + 1) ^ length := by
  induction length with
  | zero =>
      change (oddCarryPolynomialFrom half 0 (1 + 1)).coeff 1 = _
      rw [oddCarryPolynomialFrom_zeroCarry_succ]
      have hzero := oddCarryPolynomial_one half
      change oddCarryPolynomialFrom half 0 1 = _ at hzero
      have hone :
          oddCarryPolynomialFrom half 1 1 =
            (half : Polynomial ℕ) +
              ((half + 1 : ℕ) : Polynomial ℕ) * X := by
        change oddCarryPolynomialFrom half 1 (0 + 1) = _
        rw [oddCarryPolynomialFrom_oneCarry_succ]
        simp [oddCarryPolynomialFrom_zero]
      have hshift (polynomial : Polynomial ℕ) :
          ((half : Polynomial ℕ) * X * polynomial).coeff 1 =
            half * polynomial.coeff 0 := by
        rw [mul_assoc]
        simp
      rw [Polynomial.coeff_add, Polynomial.coeff_natCast_mul,
        hshift, hzero, hone]
      simp [Polynomial.coeff_natCast_ite, Polynomial.coeff_one]
      ring
  | succ length ih =>
      rw [show length + 1 + 2 = (length + 2) + 1 by omega]
      change
        (oddCarryPolynomialFrom half 0 ((length + 2) + 1)).coeff 1 = _
      rw [oddCarryPolynomialFrom_zeroCarry_succ]
      rw [Polynomial.coeff_add, Polynomial.coeff_natCast_mul]
      have hshift (polynomial : Polynomial ℕ) :
          ((half : Polynomial ℕ) * X * polynomial).coeff 1 =
            half * polynomial.coeff 0 := by
        rw [mul_assoc]
        simp
      rw [hshift]
      change
        (half + 1) * (oddCarryPolynomial half (length + 2)).coeff 1 +
            half * (oddCarryPolynomialFrom half 1 (length + 2)).coeff 0 =
          half * (half + 1) ^ (length + 1 + 1) +
            (length + 1 + 1) * half ^ 2 *
              (half + 1) ^ (length + 1)
      rw [ih]
      rw [show length + 2 = (length + 1) + 1 by omega,
        coeff_zero_oddCarryPolynomialFrom_one_succ]
      simp only [pow_succ]
      ring

/-- Exact count of valuation-zero integers in a complete odd-prime block. -/
theorem card_oddPrimeBlock_valuation_zero
    (half : ℕ) (hhalf : 0 < half) [Fact (oddBase half).Prime]
    (length : ℕ) :
    Fintype.card (OddPrimeBlockWithValuation half length 0) =
      (half + 1) ^ length := by
  rw [← coeff_oddPrimeValuationPolynomial]
  rw [oddPrimeValuationPolynomial_eq_carryPolynomial half hhalf]
  exact coeff_zero_oddCarryPolynomial half length

/-- Exact count of valuation-one integers in every complete odd-prime block
of length at least two. -/
theorem card_oddPrimeBlock_valuation_one
    (half : ℕ) (hhalf : 0 < half) [Fact (oddBase half).Prime]
    (length : ℕ) :
    Fintype.card
        (OddPrimeBlockWithValuation half (length + 2) 1) =
      half * (half + 1) ^ (length + 1) +
        (length + 1) * half ^ 2 * (half + 1) ^ length := by
  rw [← coeff_oddPrimeValuationPolynomial]
  rw [oddPrimeValuationPolynomial_eq_carryPolynomial half hhalf]
  exact coeff_one_oddCarryPolynomial_add_two half length

/-- Coefficient recurrence for the exact valuation counts. -/
theorem coeff_oddPrimeValuationPolynomial_recurrence
    (half : ℕ) (hhalf : 0 < half) [Fact (oddBase half).Prime]
    (length value : ℕ) :
    (oddPrimeValuationPolynomial half (length + 2)).coeff (value + 1) +
        oddBase half *
          (oddPrimeValuationPolynomial half length).coeff value =
      (half + 1) *
          (oddPrimeValuationPolynomial half (length + 1)).coeff
            (value + 1) +
        (half + 1) *
          (oddPrimeValuationPolynomial half (length + 1)).coeff value := by
  have h := congrArg
    (fun polynomial : Polynomial ℕ => polynomial.coeff (value + 1))
    (oddPrimeValuationPolynomial_recurrence half hhalf length)
  simpa [mul_add, add_mul, mul_assoc] using h

/-- Ternary specialization: among the integers below `3 ^ (length + 2)`, the
number whose central binomial coefficient has `3`-adic valuation zero or one
is exactly `(length + 7) * 2 ^ length`. -/
theorem card_ternaryBlock_valuation_lt_two (length : ℕ) :
    Fintype.card (OddPrimeBlockWithValuation 1 (length + 2) 0) +
        Fintype.card (OddPrimeBlockWithValuation 1 (length + 2) 1) =
      (length + 7) * 2 ^ length := by
  let : Fact (oddBase 1).Prime := ⟨by decide⟩
  rw [card_oddPrimeBlock_valuation_zero 1 (by decide) (length + 2)]
  rw [card_oddPrimeBlock_valuation_one 1 (by decide) length]
  norm_num
  rw [pow_add]
  ring

end OddPrimeValuationDistribution
