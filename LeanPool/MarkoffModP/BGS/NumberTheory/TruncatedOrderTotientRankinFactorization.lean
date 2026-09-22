/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.NumberTheory.TruncatedOrderTotientRankin
import Mathlib.NumberTheory.ArithmeticFunction.Zeta
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic

/-!
# Rankin factorization of weighted totient sums

Express the multiplicative weighted totient sum as a product over prime powers and bound its
local Rankin factors.
-/

namespace BGS.NumberTheory

open ArithmeticFunction
open scoped ArithmeticFunction.zeta

/-- Completely multiplicative rational weight determined by its prime values. -/
def factorizationWeight (primeWeight : ℕ → ℚ) (n : ℕ) : ℚ :=
  if n = 0 then 0 else
    n.factorization.prod fun prime exponent =>
      (primeWeight prime) ^ exponent

@[simp]
theorem factorizationWeight_zero (primeWeight : ℕ → ℚ) :
    factorizationWeight primeWeight 0 = 0 := by
  simp [factorizationWeight]

@[simp]
theorem factorizationWeight_one (primeWeight : ℕ → ℚ) :
    factorizationWeight primeWeight 1 = 1 := by
  simp [factorizationWeight]

theorem factorizationWeight_mul
    (primeWeight : ℕ → ℚ) {m n : ℕ}
    (hm : m ≠ 0) (hn : n ≠ 0) :
    factorizationWeight primeWeight (m * n) =
      factorizationWeight primeWeight m *
        factorizationWeight primeWeight n := by
  simp only [factorizationWeight, mul_eq_zero, hm, hn, or_false, ↓reduceIte]
  rw [Nat.factorization_mul hm hn]
  exact Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ => pow_add _)

/-- The weighted totient ratio as an arithmetic function. -/
def weightedTotientRatio
    (primeWeight : ℕ → ℚ) : ArithmeticFunction ℚ :=
  ⟨fun n =>
      if n = 0 then 0 else
        (n.totient : ℚ) / n * factorizationWeight primeWeight n,
    by simp⟩

@[simp]
theorem weightedTotientRatio_apply_ne_zero
    (primeWeight : ℕ → ℚ) {n : ℕ} (hn : n ≠ 0) :
    weightedTotientRatio primeWeight n =
      (n.totient : ℚ) / n * factorizationWeight primeWeight n := by
  simp [weightedTotientRatio, hn]

theorem weightedTotientRatio_isMultiplicative
    (primeWeight : ℕ → ℚ) :
    (weightedTotientRatio primeWeight).IsMultiplicative := by
  refine ⟨by simp [weightedTotientRatio], ?_⟩
  intro m n hcoprime
  by_cases hm : m = 0
  · subst m
    simp
  by_cases hn : n = 0
  · subst n
    simp
  simp only [weightedTotientRatio_apply_ne_zero _ hm,
    weightedTotientRatio_apply_ne_zero _ hn,
    weightedTotientRatio_apply_ne_zero _ (mul_ne_zero hm hn),
    Nat.totient_mul hcoprime,
    factorizationWeight_mul primeWeight hm hn,
    Nat.cast_mul]
  field_simp

/-- Exact local Euler factor for one prime power. -/
def rankinPrimePowerFactor
    (prime exponent : ℕ) (weight : ℚ) : ℚ :=
  1 + ((prime - 1 : ℕ) : ℚ) / prime *
    ∑ index ∈ Finset.range exponent, weight ^ (index + 1)

/-- Prime-independent upper local factor.  Dropping `1 - 1 / prime` is
important for profile certificates: a lower bound on the prime controls the
weight, while this coarser factor is monotone-free. -/
def coarseRankinPrimePowerFactor
    (exponent : ℕ) (weight : ℚ) : ℚ :=
  1 + ∑ index ∈ Finset.range exponent, weight ^ (index + 1)

theorem rankinPrimePowerFactor_nonneg
    {prime exponent : ℕ} (hprime : prime.Prime)
    {weight : ℚ} (hweight : 0 ≤ weight) :
    0 ≤ rankinPrimePowerFactor prime exponent weight := by
  simp only [rankinPrimePowerFactor]
  positivity

theorem rankinPrimePowerFactor_le_coarse
    {prime exponent : ℕ} (hprime : prime.Prime)
    {weight : ℚ} (hweight : 0 ≤ weight) :
    rankinPrimePowerFactor prime exponent weight ≤
      coarseRankinPrimePowerFactor exponent weight := by
  have hsumNonneg :
      (0 : ℚ) ≤
        ∑ index ∈ Finset.range exponent, weight ^ (index + 1) := by
    positivity
  have hratio : (((prime - 1 : ℕ) : ℚ) / prime) ≤ 1 := by
    apply (div_le_one (by exact_mod_cast hprime.pos)).2
    exact_mod_cast Nat.sub_le prime 1
  simp only [rankinPrimePowerFactor, coarseRankinPrimePowerFactor]
  gcongr
  simpa using mul_le_mul_of_nonneg_right hratio hsumNonneg

private theorem weightedTotientRatio_primePowerSum
    (prime exponent : ℕ) (hprime : prime.Prime)
  (primeWeight : ℕ → ℚ) :
    ∑ order ∈ (prime ^ exponent).divisors,
        weightedTotientRatio primeWeight order =
      rankinPrimePowerFactor prime exponent (primeWeight prime) := by
  rw [Nat.sum_divisors_prime_pow hprime]
  rw [Finset.sum_range_succ']
  simp only [rankinPrimePowerFactor]
  rw [show weightedTotientRatio primeWeight (prime ^ 0) = 1 by
    simp [weightedTotientRatio, factorizationWeight]]
  rw [add_comm _ 1]
  rw [add_left_cancel_iff]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro index hindex
  simp only [weightedTotientRatio_apply_ne_zero _
      (pow_ne_zero _ hprime.ne_zero), factorizationWeight,
      pow_ne_zero _ hprime.ne_zero, ite_false, hprime.factorization_pow]
  rw [Finsupp.prod_single_index]
  rw [Nat.totient_prime_pow_succ hprime]
  push_cast
  field_simp [hprime.ne_zero]
  ring
  all_goals simp

theorem weightedTotientDivisorSum_eq_factorizationEulerProduct
    (N : ℕ) (hN : N ≠ 0) (primeWeight : ℕ → ℚ) :
    weightedTotientDivisorSum N (factorizationWeight primeWeight) =
      N.factorization.prod fun prime exponent =>
        rankinPrimePowerFactor prime exponent (primeWeight prime) := by
  have hmult := weightedTotientRatio_isMultiplicative primeWeight
  have hzetaMult :
      ((ζ : ArithmeticFunction ℕ) : ArithmeticFunction ℚ).IsMultiplicative :=
    ArithmeticFunction.isMultiplicative_zeta.natCast
  calc
    weightedTotientDivisorSum N (factorizationWeight primeWeight) =
        ∑ order ∈ N.divisors,
          weightedTotientRatio primeWeight order := by
      apply Finset.sum_congr rfl
      intro order horder
      have horderNe : order ≠ 0 :=
        ne_zero_of_dvd_ne_zero hN (Nat.mem_divisors.mp horder).1
      simp [weightedTotientRatio_apply_ne_zero _ horderNe]
    _ = (((ζ : ArithmeticFunction ℕ) : ArithmeticFunction ℚ) *
          weightedTotientRatio primeWeight) N := by
      rw [ArithmeticFunction.coe_zeta_mul_apply]
    _ = N.factorization.prod fun prime exponent =>
          ((((ζ : ArithmeticFunction ℕ) : ArithmeticFunction ℚ) *
            weightedTotientRatio primeWeight) (prime ^ exponent)) := by
      exact (hzetaMult.mul hmult).multiplicative_factorization _ hN
    _ = N.factorization.prod fun prime exponent =>
          rankinPrimePowerFactor prime exponent (primeWeight prime) := by
      apply Finsupp.prod_congr
      intro prime hprime
      rw [ArithmeticFunction.coe_zeta_mul_apply]
      exact weightedTotientRatio_primePowerSum prime _
        (Nat.prime_of_mem_primeFactors hprime) primeWeight

/-- Nonnegative prime weights give a nonnegative multiplicative weight on
every positive integer. -/
theorem factorizationWeight_nonneg
    (primeWeight : ℕ → ℚ)
    (hprimeWeightNonneg : ∀ prime, 0 ≤ primeWeight prime)
    (n : ℕ) :
    0 ≤ factorizationWeight primeWeight n := by
  by_cases hn : n = 0
  · simp [hn]
  simp only [factorizationWeight, hn, ↓reduceIte, Finsupp.prod]
  apply Finset.prod_nonneg
  intro prime hprime
  exact pow_nonneg (hprimeWeightNonneg prime) _

/-- The exact Euler product is nonnegative when all supplied prime weights
are nonnegative. -/
theorem factorizationEulerProduct_nonneg
    (N : ℕ) (hN : N ≠ 0) (primeWeight : ℕ → ℚ)
    (hprimeWeightNonneg : ∀ prime, 0 ≤ primeWeight prime) :
    0 ≤ N.factorization.prod fun prime exponent =>
      rankinPrimePowerFactor prime exponent (primeWeight prime) := by
  rw [← weightedTotientDivisorSum_eq_factorizationEulerProduct
    N hN primeWeight]
  apply Finset.sum_nonneg
  intro order horder
  exact mul_nonneg
    (div_nonneg (by positivity) (by positivity))
    (factorizationWeight_nonneg primeWeight hprimeWeightNonneg order)

/-- The exact Euler product is bounded by the product of the
prime-independent coarse local factors. -/
theorem factorizationEulerProduct_le_coarse
    (N : ℕ) (primeWeight : ℕ → ℚ)
    (hprimeWeightNonneg : ∀ prime, 0 ≤ primeWeight prime) :
    (N.factorization.prod fun prime exponent =>
      rankinPrimePowerFactor prime exponent (primeWeight prime)) ≤
    (N.factorization.prod fun prime exponent =>
      coarseRankinPrimePowerFactor exponent (primeWeight prime)) := by
  simp only [Finsupp.prod]
  apply Finset.prod_le_prod₀
  · intro prime hprime
    exact rankinPrimePowerFactor_nonneg
      (Nat.prime_of_mem_primeFactors hprime)
      (hprimeWeightNonneg prime)
  · intro prime hprime
    exact rankinPrimePowerFactor_le_coarse
      (Nat.prime_of_mem_primeFactors hprime)
      (hprimeWeightNonneg prime)

/-- A primewise twelfth-power lower bound multiplies to the exact Rankin
weight hypothesis for every positive integer. -/
theorem factorizationWeight_twelfthPower
    (primeWeight : ℕ → ℚ)
    (hprimeWeightPower :
      ∀ prime : ℕ, prime.Prime →
        1 ≤ (prime : ℚ) * (primeWeight prime) ^ 12)
    {n : ℕ} (hn : n ≠ 0) :
    1 ≤ (n : ℚ) * (factorizationWeight primeWeight n) ^ 12 := by
  have hnCast :
      (n : ℚ) = n.factorization.prod fun prime exponent =>
        (prime : ℚ) ^ exponent := by
    calc
      (n : ℚ) =
          ((n.factorization.prod fun prime exponent =>
            prime ^ exponent : ℕ) : ℚ) := by
        exact congrArg (fun value : ℕ => (value : ℚ))
          (Nat.prod_factorization_pow_eq_self hn).symm
      _ = n.factorization.prod fun prime exponent =>
          (prime : ℚ) ^ exponent := by
        push_cast
        rfl
  rw [hnCast]
  simp only [factorizationWeight, hn, ↓reduceIte, Finsupp.prod]
  rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
  apply Finset.one_le_prod₀
  intro prime hprime
  rw [show (prime : ℚ) ^ n.factorization prime *
      (primeWeight prime ^ n.factorization prime) ^ 12 =
      ((prime : ℚ) * primeWeight prime ^ 12) ^
        n.factorization prime by
    rw [mul_pow]
    congr 1
    rw [← pow_mul, ← pow_mul, Nat.mul_comm]]
  exact one_le_pow₀
    (hprimeWeightPower prime (Nat.prime_of_mem_primeFactors hprime))

/-- Primewise rational weights specialize the abstract Rankin inequality to
an exact Euler product over the factorization of `N`. -/
theorem truncatedOrderTotientSum_cast_le_factorizationRankin
    (N bound : ℕ) (primeWeight : ℕ → ℚ) (cap : ℚ)
    (hprimeWeightNonneg : ∀ prime, 0 ≤ primeWeight prime)
    (hprimeWeightPower :
      ∀ prime : ℕ, prime.Prime →
        1 ≤ (prime : ℚ) * (primeWeight prime) ^ 12)
    (hcapNonneg : 0 ≤ cap)
    (hboundCap : (bound : ℚ) ≤ cap ^ 12)
    (hN : N ≠ 0) :
    (truncatedOrderTotientSum N bound : ℚ) ≤
      (bound : ℚ) * cap *
        (N.factorization.prod fun prime exponent =>
          rankinPrimePowerFactor prime exponent (primeWeight prime)) := by
  rw [← weightedTotientDivisorSum_eq_factorizationEulerProduct
    N hN primeWeight]
  apply truncatedOrderTotientSum_cast_le_weightedRankin
  · intro order horder
    exact factorizationWeight_nonneg primeWeight hprimeWeightNonneg order
  · intro order horder
    have horderNe : order ≠ 0 :=
      ne_zero_of_dvd_ne_zero hN (Nat.mem_divisors.mp horder).1
    exact factorizationWeight_twelfthPower primeWeight
      hprimeWeightPower horderNe
  · exact hcapNonneg
  · exact hboundCap

end BGS.NumberTheory
