/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.NumberTheory.DivisorBound

/-!
# An explicit divisor-counting bound

The asymptotic divisor bound used by the original assembly hides a threshold in a
little-oh argument.  This file keeps the same elementary factorization proof but
uses a concrete polynomial-versus-exponential estimate.  Its specialization at
`k = 32` is the numerical input for explicit strong approximation.
-/

namespace BGS.NumberTheory

open scoped BigOperators

/-- A completely explicit replacement for the polynomial-versus-exponential
constant in `DivisorBound.lean`. -/
theorem pow_succ_le_self_pow_mul_two_pow
    (k : ℕ) (hk : 0 < k) (a : ℕ) :
    (a + 1) ^ k ≤ k ^ k * 2 ^ a := by
  let q := a / k
  have haq : a + 1 ≤ k * (q + 1) := by
    exact Nat.succ_le_of_lt (by
      simpa [q, Nat.mul_comm] using Nat.lt_mul_div_succ a hk)
  have hq : q + 1 ≤ 2 ^ q := Nat.succ_le_of_lt q.lt_two_pow_self
  calc
    (a + 1) ^ k ≤ (k * (q + 1)) ^ k := Nat.pow_le_pow_left haq _
    _ = k ^ k * (q + 1) ^ k := by rw [mul_pow]
    _ ≤ k ^ k * (2 ^ q) ^ k :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hq _)
    _ = k ^ k * 2 ^ (q * k) := by rw [pow_mul]
    _ ≤ k ^ k * 2 ^ a := Nat.mul_le_mul_left _ <|
      Nat.pow_le_pow_right (by norm_num) (Nat.div_mul_le_self a k)

/-- Explicit factorization bound for the divisor-counting function. -/
theorem card_divisors_pow_le_explicit_constant_mul
    (k : ℕ) (hk : 0 < k) (n : ℕ) (hn : n ≠ 0) :
    n.divisors.card ^ k ≤ (k ^ k) ^ (2 ^ k) * n := by
  let D := k ^ k
  have hD : 0 < D := pow_pos hk _
  have hfactor : ∀ p ∈ n.primeFactors,
      (n.factorization p + 1) ^ k ≤
        (if p < 2 ^ k then D else 1) * p ^ n.factorization p := by
    intro p hp
    have hpPrime := Nat.prime_of_mem_primeFactors hp
    have hpTwo : 2 ≤ p := hpPrime.two_le
    have haPos : 0 < n.factorization p :=
      hpPrime.factorization_pos_of_dvd hn (Nat.dvd_of_mem_primeFactors hp)
    by_cases hpSmall : p < 2 ^ k
    · rw [if_pos hpSmall]
      exact (pow_succ_le_self_pow_mul_two_pow k hk (n.factorization p)).trans <|
        Nat.mul_le_mul_left D (Nat.pow_le_pow_left hpTwo _)
    · rw [if_neg hpSmall, one_mul]
      have hsucc : n.factorization p + 1 ≤ 2 ^ n.factorization p :=
        Nat.succ_le_of_lt (n.factorization p).lt_two_pow_self
      calc
        (n.factorization p + 1) ^ k ≤ (2 ^ n.factorization p) ^ k :=
          Nat.pow_le_pow_left hsucc k
        _ = (2 ^ k) ^ n.factorization p := by
          rw [← pow_mul, ← pow_mul, Nat.mul_comm]
        _ ≤ p ^ n.factorization p :=
          Nat.pow_le_pow_left (le_of_not_gt hpSmall) _
  have hsmallCard :
      (n.primeFactors.filter fun p => p < 2 ^ k).card ≤ 2 ^ k := by
    calc
      (n.primeFactors.filter fun p => p < 2 ^ k).card ≤
          (Finset.range (2 ^ k)).card :=
        Finset.card_le_card (by
          intro p hp
          exact Finset.mem_range.mpr (Finset.mem_filter.mp hp).2)
      _ = 2 ^ k := Finset.card_range _
  rw [Nat.card_divisors hn, ← Finset.prod_pow]
  calc
    (∏ p ∈ n.primeFactors, (n.factorization p + 1) ^ k) ≤
        ∏ p ∈ n.primeFactors,
          ((if p < 2 ^ k then D else 1) * p ^ n.factorization p) :=
      Finset.prod_le_prod (fun _ _ => Nat.zero_le _) hfactor
    _ = D ^ (n.primeFactors.filter fun p => p < 2 ^ k).card * n := by
      rw [Finset.prod_mul_distrib, ← Nat.prod_primeFactors_pow_factorization hn]
      simp [Finset.prod_ite]
    _ ≤ D ^ (2 ^ k) * n := by
      exact Nat.mul_le_mul_right n (Nat.pow_le_pow_right hD hsmallCard)
    _ = (k ^ k) ^ (2 ^ k) * n := by rfl

/-- Sealed data for the closed factorization constant.  The subtype equation
lets downstream proofs rewrite the value without asking the kernel to
repeatedly normalize its enormous exponentiation. -/
@[irreducible] def explicitDivisorConstantData :
    {n : ℕ // n = (32 ^ 32) ^ (2 ^ 32)} :=
  ⟨(32 ^ 32) ^ (2 ^ 32), rfl⟩

/-- The closed factorization constant used by the explicit Markoff proof. -/
def explicitDivisorConstant : ℕ := explicitDivisorConstantData.1

theorem explicitDivisorConstant_eq :
    explicitDivisorConstant = (32 ^ 32) ^ (2 ^ 32) :=
  explicitDivisorConstantData.2

theorem explicitDivisorConstant_pos : 0 < explicitDivisorConstant := by
  rw [explicitDivisorConstant_eq]
  exact pow_pos (pow_pos (by norm_num) _) _

theorem explicitDivisorConstant_le_pow_thirtyTwo :
    explicitDivisorConstant ≤ explicitDivisorConstant ^ 32 := by
  have hOne : 1 ≤ explicitDivisorConstant := explicitDivisorConstant_pos
  simpa only [pow_one] using
    (pow_le_pow_right₀ hOne (show (1 : ℕ) ≤ 32 by norm_num))

/-- Above the concrete constant, the divisor count is bounded by the
sixteenth root. -/
theorem card_divisors_le_rpow_one_div_sixteen
    (n : ℕ) (hn : explicitDivisorConstant ≤ n) :
    (n.divisors.card : ℝ) ≤ (n : ℝ) ^ (1 / 16 : ℝ) := by
  have hnPos : 0 < n := explicitDivisorConstant_pos.trans_le hn
  have hNatural := card_divisors_pow_le_explicit_constant_mul
    32 (by norm_num) n hnPos.ne'
  have hNatural' : n.divisors.card ^ 32 ≤ n ^ 2 := by
    calc
      n.divisors.card ^ 32 ≤ explicitDivisorConstant * n := by
        rw [explicitDivisorConstant_eq]
        exact hNatural
      _ ≤ n * n := Nat.mul_le_mul_right n hn
      _ = n ^ 2 := by ring
  have hCast : (n.divisors.card : ℝ) ^ 32 ≤ (n : ℝ) ^ 2 := by
    exact_mod_cast hNatural'
  have hnNonnegative : (0 : ℝ) ≤ n := by positivity
  have hPowers : (n.divisors.card : ℝ) ^ 32 ≤
      ((n : ℝ) ^ (1 / 16 : ℝ)) ^ 32 := by
    calc
      (n.divisors.card : ℝ) ^ 32 ≤ (n : ℝ) ^ 2 := hCast
      _ = (n : ℝ) ^ ((1 / 16 : ℝ) * 32) := by norm_num
      _ = ((n : ℝ) ^ (1 / 16 : ℝ)) ^ 32 :=
        Real.rpow_mul_natCast hnNonnegative (1 / 16 : ℝ) 32
  exact le_of_pow_le_pow_left₀ (by norm_num : (32 : ℕ) ≠ 0)
    (Real.rpow_nonneg hnNonnegative _) hPowers

end BGS.NumberTheory
