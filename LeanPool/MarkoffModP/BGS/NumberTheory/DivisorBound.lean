/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# Subpolynomial growth of the divisor-counting function

This module develops the analytic-number-theory input used by the BGS
middle- and end-game union bounds.  The public target is an eventual real
power bound for `Nat.divisors.card`.
-/

@[expose] public section

namespace BGS.NumberTheory

open Filter
open scoped BigOperators Topology

/-- A fixed power of `a + 1` is bounded by a constant times `2 ^ a`.
The constant is allowed to depend on the power. -/
private lemma exists_pow_succ_le_constant_mul_two_pow (k : ℕ) :
    ∃ D : ℕ, 0 < D ∧ ∀ a : ℕ, (a + 1) ^ k ≤ D * 2 ^ a := by
  have h :=
    (isLittleO_pow_const_const_pow_of_one_lt (R := ℝ) k
      (by norm_num : (1 : ℝ) < 2)).bound zero_lt_one
  rw [eventually_atTop] at h
  obtain ⟨N, hN⟩ := h
  refine ⟨2 * (N + 1) ^ k, by positivity, fun a ↦ ?_⟩
  by_cases ha : N ≤ a + 1
  · have hreal := hN (a + 1) ha
    simp only [Real.norm_eq_abs, one_mul, abs_pow] at hreal
    simp only [ge_iff_le] at hreal
    have hnat : (a + 1) ^ k ≤ 2 ^ (a + 1) := by exact_mod_cast hreal
    calc
      (a + 1) ^ k ≤ 2 ^ (a + 1) := hnat
      _ = 2 * 2 ^ a := by simp [pow_succ, Nat.mul_comm]
      _ ≤ (2 * (N + 1) ^ k) * 2 ^ a := by
        gcongr
        simpa using Nat.mul_le_mul_left 2 (Nat.one_le_pow' k N)
  · have haN : a + 1 ≤ N + 1 := by omega
    calc
      (a + 1) ^ k ≤ (N + 1) ^ k := Nat.pow_le_pow_left haN k
      _ ≤ (2 * (N + 1) ^ k) * 2 ^ a := by
        have hpow : 1 ≤ 2 ^ a := by simpa using Nat.one_le_pow' a 1
        nlinarith [Nat.zero_le ((N + 1) ^ k)]

/-- Raising the divisor count to a fixed natural power costs only a constant
times `n`.  This is the arithmetic core of the subpolynomial estimate. -/
private lemma exists_card_divisors_pow_le_constant_mul (k : ℕ) :
    ∃ C : ℕ, 0 < C ∧ ∀ n : ℕ, n ≠ 0 → n.divisors.card ^ k ≤ C * n := by
  obtain ⟨D, hD, hDpow⟩ := exists_pow_succ_le_constant_mul_two_pow k
  refine ⟨D ^ (2 ^ k), pow_pos hD _, fun n hn ↦ ?_⟩
  have hfactor : ∀ p ∈ n.primeFactors,
      (n.factorization p + 1) ^ k ≤
        (if p < 2 ^ k then D else 1) * p ^ n.factorization p := by
    intro p hp
    have hpPrime := Nat.prime_of_mem_primeFactors hp
    have hpTwo : 2 ≤ p := hpPrime.two_le
    have haPos : 0 < n.factorization p :=
      hpPrime.factorization_pos_of_dvd hn (Nat.dvd_of_mem_primeFactors hp)
    by_cases hpSmall : p < 2 ^ k
    · rw [ite_eq_left hpSmall]
      exact (hDpow (n.factorization p)).trans <|
        Nat.mul_le_mul_left D (Nat.pow_le_pow_left hpTwo _)
    · rw [ite_eq_right hpSmall, one_mul]
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
      (n.primeFactors.filter fun p ↦ p < 2 ^ k).card ≤ 2 ^ k := by
    calc
      (n.primeFactors.filter fun p ↦ p < 2 ^ k).card ≤ (Finset.range (2 ^ k)).card :=
        Finset.card_le_card (by
          intro p hp
          exact Finset.mem_range.mpr (Finset.mem_filter.mp hp).2)
      _ = 2 ^ k := Finset.card_range _
  rw [Nat.card_divisors hn, ← Finset.prod_pow]
  calc
    (∏ p ∈ n.primeFactors, (n.factorization p + 1) ^ k) ≤
        ∏ p ∈ n.primeFactors,
          ((if p < 2 ^ k then D else 1) * p ^ n.factorization p) :=
      Finset.prod_le_prod hfactor
    _ = D ^ (n.primeFactors.filter fun p ↦ p < 2 ^ k).card * n := by
      rw [Finset.prod_mul_distrib, ← Nat.prod_primeFactors_pow_factorization hn]
      simp [Finset.prod_ite]
    _ ≤ D ^ (2 ^ k) * n := by
      exact Nat.mul_le_mul_right n (Nat.pow_le_pow_right hD hsmallCard)

/-- The divisor-counting function is eventually bounded by every positive
real power.  The cast and `Real.rpow` formulation is designed for direct use
in the real-valued union bounds for divisors of `p - 1` and `p + 1`. -/
theorem eventually_card_divisors_le_rpow {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, (n.divisors.card : ℝ) ≤ (n : ℝ) ^ ε := by
  obtain ⟨k, hk⟩ := exists_nat_gt (1 / ε)
  have hkRealPos : (0 : ℝ) < k := (one_div_pos.mpr hε).trans hk
  have hkPos : 0 < k := by exact_mod_cast hkRealPos
  have hExponent : 0 < ε * (k : ℝ) - 1 := by
    have := (div_lt_iff₀ hε).mp hk
    nlinarith
  obtain ⟨C, hC, hbound⟩ := exists_card_divisors_pow_le_constant_mul k
  have hEventuallyConstant :
      ∀ᶠ n : ℕ in atTop, (C : ℝ) ≤ (n : ℝ) ^ (ε * (k : ℝ) - 1) :=
    ((tendsto_rpow_atTop hExponent).comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (C : ℝ))
  filter_upwards [hEventuallyConstant, eventually_gt_atTop 0] with n hConstant hn
  have hNatural := hbound n (Nat.ne_of_gt hn)
  have hCast : (n.divisors.card : ℝ) ^ k ≤ (C : ℝ) * n := by
    exact_mod_cast hNatural
  have hnRealPos : (0 : ℝ) < n := by exact_mod_cast hn
  have hPowers : (n.divisors.card : ℝ) ^ k ≤ ((n : ℝ) ^ ε) ^ k := by
    calc
      (n.divisors.card : ℝ) ^ k ≤ (C : ℝ) * n := hCast
      _ ≤ (n : ℝ) ^ (ε * (k : ℝ) - 1) * n :=
        mul_le_mul_of_nonneg_right hConstant (Nat.cast_nonneg n)
      _ = (n : ℝ) ^ (ε * (k : ℝ) - 1 + 1) := by
        simpa using (Real.rpow_add hnRealPos (ε * (k : ℝ) - 1) 1).symm
      _ = (n : ℝ) ^ (ε * (k : ℝ)) := by ring_nf
      _ = ((n : ℝ) ^ ε) ^ k := Real.rpow_mul_natCast hnRealPos.le ε k
  exact le_of_pow_le_pow_left₀ hkPos.ne' (Real.rpow_nonneg hnRealPos.le ε) hPowers

/-- Threshold form of `eventually_card_divisors_le_rpow`, convenient when a
downstream argument already carries explicit lower bounds for `p - 1` and
`p + 1`. -/
theorem exists_threshold_card_divisors_le_rpow {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → (n.divisors.card : ℝ) ≤ (n : ℝ) ^ ε :=
  eventually_atTop.mp (eventually_card_divisors_le_rpow hε)

end BGS.NumberTheory
