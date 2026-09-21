/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.NumberTheory.ExplicitDivisorBound
import Mathlib.Tactic.IntervalCases

/-!
# An elementary tenth-moment divisor bound

For the paper's preliminary all-divisors route, the generic factorization
constant in `ExplicitDivisorBound.lean` is much too large.  Here each prime
factor is charged a small power-of-two penalty.  The penalties over primes below
`1024` sum exactly to `447`; primes at least `1024` need no penalty.
-/

namespace BGS.NumberTheory

open scoped BigOperators

/-- If the tenth-power ratio is controlled at one exponent, it remains
controlled at every later exponent. -/
private theorem pow_ten_succ_ratio_le
    (base A a : ℕ) (ha : A ≤ a)
    (hbase : (A + 2) ^ 10 ≤ base * (A + 1) ^ 10) :
    (a + 2) ^ 10 ≤ base * (a + 1) ^ 10 := by
  have hlinear : (A + 1) * (a + 2) ≤ (A + 2) * (a + 1) := by
    nlinarith
  have hpow := Nat.pow_le_pow_left hlinear 10
  have hscaled :
      (A + 1) ^ 10 * (a + 2) ^ 10 ≤
        (A + 1) ^ 10 * (base * (a + 1) ^ 10) := by
    calc
      (A + 1) ^ 10 * (a + 2) ^ 10 =
          ((A + 1) * (a + 2)) ^ 10 := by rw [mul_pow]
      _ ≤ ((A + 2) * (a + 1)) ^ 10 := hpow
      _ = (A + 2) ^ 10 * (a + 1) ^ 10 := by rw [mul_pow]
      _ ≤ (base * (A + 1) ^ 10) * (a + 1) ^ 10 :=
        Nat.mul_le_mul_right _ hbase
      _ = (A + 1) ^ 10 * (base * (a + 1) ^ 10) := by ring
  exact Nat.le_of_mul_le_mul_left hscaled (by positivity)

/-- Induction from a finite threshold for a fixed prime-size band. -/
private theorem pow_ten_le_band_of_threshold
    (base c A : ℕ)
    (hbase : (A + 1) ^ 10 ≤ 2 ^ c * base ^ A)
    (hratio : (A + 2) ^ 10 ≤ base * (A + 1) ^ 10)
    (a : ℕ) (ha : A ≤ a) :
    (a + 1) ^ 10 ≤ 2 ^ c * base ^ a := by
  induction a, ha using Nat.le_induction with
  | base => exact hbase
  | succ a ha ih =>
      calc
        (a + 1 + 1) ^ 10 ≤ base * (a + 1) ^ 10 :=
          pow_ten_succ_ratio_le base A a ha hratio
        _ ≤ base * (2 ^ c * base ^ a) :=
          Nat.mul_le_mul_left _ ih
        _ = 2 ^ c * base ^ (a + 1) := by ring

private theorem pow_ten_le_base_two (a : ℕ) :
    (a + 1) ^ 10 ≤ 2 ^ 26 * 2 ^ a := by
  by_cases ha : 13 ≤ a
  · simpa using pow_ten_le_band_of_threshold 2 26 13
      (by norm_num) (by norm_num) a ha
  · have ha' : a ≤ 12 := by omega
    interval_cases a <;> norm_num

private theorem pow_ten_le_base_three (a : ℕ) :
    (a + 1) ^ 10 ≤ 2 ^ 20 * 3 ^ a := by
  by_cases ha : 8 ≤ a
  · simpa using pow_ten_le_band_of_threshold 3 20 8
      (by norm_num) (by norm_num) a ha
  · have ha' : a ≤ 7 := by omega
    interval_cases a <;> norm_num

private theorem pow_ten_le_base_five (a : ℕ) :
    (a + 1) ^ 10 ≤ 2 ^ 15 * 5 ^ a := by
  by_cases ha : 5 ≤ a
  · simpa using pow_ten_le_band_of_threshold 5 15 5
      (by norm_num) (by norm_num) a ha
  · have ha' : a ≤ 4 := by omega
    interval_cases a <;> norm_num

private theorem pow_ten_le_base_seven (a : ℕ) :
    (a + 1) ^ 10 ≤ 2 ^ 12 * 7 ^ a := by
  by_cases ha : 4 ≤ a
  · simpa using pow_ten_le_band_of_threshold 7 12 4
      (by norm_num) (by norm_num) a ha
  · have ha' : a ≤ 3 := by omega
    interval_cases a <;> norm_num

private theorem pow_ten_le_base_eleven (a : ℕ) :
    (a + 1) ^ 10 ≤ 2 ^ 10 * 11 ^ a := by
  by_cases ha : 3 ≤ a
  · simpa using pow_ten_le_band_of_threshold 11 10 3
      (by norm_num) (by norm_num) a ha
  · have ha' : a ≤ 2 := by omega
    interval_cases a <;> norm_num

private theorem pow_ten_le_base_thirteen (a : ℕ) :
    (a + 1) ^ 10 ≤ 2 ^ 9 * 13 ^ a := by
  by_cases ha : 3 ≤ a
  · simpa using pow_ten_le_band_of_threshold 13 9 3
      (by norm_num) (by norm_num) a ha
  · have ha' : a ≤ 2 := by omega
    interval_cases a <;> norm_num

private theorem pow_ten_le_base_seventeen (a : ℕ) :
    (a + 1) ^ 10 ≤ 2 ^ 8 * 17 ^ a := by
  by_cases ha : 3 ≤ a
  · simpa using pow_ten_le_band_of_threshold 17 8 3
      (by norm_num) (by norm_num) a ha
  · have ha' : a ≤ 2 := by omega
    interval_cases a <;> norm_num

private theorem pow_ten_le_base_twentyThree (a : ℕ) :
    (a + 1) ^ 10 ≤ 2 ^ 7 * 23 ^ a := by
  by_cases ha : 2 ≤ a
  · simpa using pow_ten_le_band_of_threshold 23 7 2
      (by norm_num) (by norm_num) a ha
  · have ha' : a ≤ 1 := by omega
    interval_cases a <;> norm_num

private theorem pow_ten_le_base_thirtyOne (a : ℕ) :
    (a + 1) ^ 10 ≤ 2 ^ 6 * 31 ^ a := by
  by_cases ha : 2 ≤ a
  · simpa using pow_ten_le_band_of_threshold 31 6 2
      (by norm_num) (by norm_num) a ha
  · have ha' : a ≤ 1 := by omega
    interval_cases a <;> norm_num

private theorem pow_ten_le_base_fortyThree (a : ℕ) :
    (a + 1) ^ 10 ≤ 2 ^ 5 * 43 ^ a := by
  by_cases ha : 2 ≤ a
  · simpa using pow_ten_le_band_of_threshold 43 5 2
      (by norm_num) (by norm_num) a ha
  · have ha' : a ≤ 1 := by omega
    interval_cases a <;> norm_num

private theorem pow_ten_le_base_sixtySeven (a : ℕ) :
    (a + 1) ^ 10 ≤ 2 ^ 4 * 67 ^ a := by
  by_cases ha : 1 ≤ a
  · simpa using pow_ten_le_band_of_threshold 67 4 1
      (by norm_num) (by norm_num) a ha
  · have ha' : a ≤ 0 := by omega
    interval_cases a <;> norm_num

private theorem pow_ten_le_base_oneHundredThirtyOne (a : ℕ) :
    (a + 1) ^ 10 ≤ 2 ^ 3 * 131 ^ a := by
  by_cases ha : 1 ≤ a
  · simpa using pow_ten_le_band_of_threshold 131 3 1
      (by norm_num) (by norm_num) a ha
  · have ha' : a ≤ 0 := by omega
    interval_cases a <;> norm_num

private theorem pow_ten_le_base_twoHundredFiftySeven (a : ℕ) :
    (a + 1) ^ 10 ≤ 2 ^ 2 * 257 ^ a := by
  by_cases ha : 1 ≤ a
  · simpa using pow_ten_le_band_of_threshold 257 2 1
      (by norm_num) (by norm_num) a ha
  · have ha' : a ≤ 0 := by omega
    interval_cases a <;> norm_num

private theorem pow_ten_le_base_fiveHundredTwentyOne (a : ℕ) :
    (a + 1) ^ 10 ≤ 2 * 521 ^ a := by
  by_cases ha : 1 ≤ a
  · simpa using pow_ten_le_band_of_threshold 521 1 1
      (by norm_num) (by norm_num) a ha
  · have ha' : a ≤ 0 := by omega
    interval_cases a <;> norm_num

private theorem pow_ten_le_base_oneThousandTwentyFour (a : ℕ) :
    (a + 1) ^ 10 ≤ 1024 ^ a := by
  simpa using pow_ten_le_band_of_threshold 1024 0 0
    (by norm_num) (by norm_num) a (Nat.zero_le a)
/-- Power-of-two penalty assigned to a prime factor.  The thresholds are the
first primes at which the optimal integer penalty decreases. -/
def preliminaryPrimePenalty (p : ℕ) : ℕ :=
  if p < 3 then 26
  else if p < 5 then 20
  else if p < 7 then 15
  else if p < 11 then 12
  else if p < 13 then 10
  else if p < 17 then 9
  else if p < 23 then 8
  else if p < 31 then 7
  else if p < 43 then 6
  else if p < 67 then 5
  else if p < 131 then 4
  else if p < 257 then 3
  else if p < 521 then 2
  else if p < 1024 then 1
  else 0

private theorem preliminaryPrimePenalty_eq_zero_of_le
    {p : ℕ} (hp : 1024 ≤ p) :
    preliminaryPrimePenalty p = 0 := by
  simp [preliminaryPrimePenalty,
    show ¬p < 3 by omega,
    show ¬p < 5 by omega,
    show ¬p < 7 by omega,
    show ¬p < 11 by omega,
    show ¬p < 13 by omega,
    show ¬p < 17 by omega,
    show ¬p < 23 by omega,
    show ¬p < 31 by omega,
    show ¬p < 43 by omega,
    show ¬p < 67 by omega,
    show ¬p < 131 by omega,
    show ¬p < 257 by omega,
    show ¬p < 521 by omega,
    show ¬p < 1024 by omega]

/-- Factorwise tenth-moment estimate, using the penalty band containing the
prime. -/
private theorem factorization_succ_pow_ten_le
    {p a : ℕ} (hpPrime : p.Prime) :
    (a + 1) ^ 10 ≤
      2 ^ preliminaryPrimePenalty p * p ^ a := by
  have hpTwo : 2 ≤ p := hpPrime.two_le
  by_cases hp3 : p < 3
  · simp only [preliminaryPrimePenalty, if_pos hp3]
    exact (pow_ten_le_base_two a).trans <|
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hpTwo a)
  · by_cases hp5 : p < 5
    · have hpLower : 3 ≤ p := by omega
      simp only [preliminaryPrimePenalty, if_neg hp3, if_pos hp5]
      exact (pow_ten_le_base_three a).trans <|
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hpLower a)
    · by_cases hp7 : p < 7
      · have hpLower : 5 ≤ p := by omega
        simp only [preliminaryPrimePenalty, if_neg hp3, if_neg hp5, if_pos hp7]
        exact (pow_ten_le_base_five a).trans <|
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hpLower a)
      · by_cases hp11 : p < 11
        · have hpLower : 7 ≤ p := by omega
          simp only [preliminaryPrimePenalty, if_neg hp3, if_neg hp5,
            if_neg hp7, if_pos hp11]
          exact (pow_ten_le_base_seven a).trans <|
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hpLower a)
        · by_cases hp13 : p < 13
          · have hpLower : 11 ≤ p := by omega
            simp only [preliminaryPrimePenalty, if_neg hp3, if_neg hp5,
              if_neg hp7, if_neg hp11, if_pos hp13]
            exact (pow_ten_le_base_eleven a).trans <|
              Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hpLower a)
          · by_cases hp17 : p < 17
            · have hpLower : 13 ≤ p := by omega
              simp only [preliminaryPrimePenalty, if_neg hp3, if_neg hp5,
                if_neg hp7, if_neg hp11, if_neg hp13, if_pos hp17]
              exact (pow_ten_le_base_thirteen a).trans <|
                Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hpLower a)
            · by_cases hp23 : p < 23
              · have hpLower : 17 ≤ p := by omega
                simp only [preliminaryPrimePenalty, if_neg hp3, if_neg hp5,
                  if_neg hp7, if_neg hp11, if_neg hp13, if_neg hp17,
                  if_pos hp23]
                exact (pow_ten_le_base_seventeen a).trans <|
                  Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hpLower a)
              · by_cases hp31 : p < 31
                · have hpLower : 23 ≤ p := by omega
                  simp only [preliminaryPrimePenalty, if_neg hp3, if_neg hp5,
                    if_neg hp7, if_neg hp11, if_neg hp13, if_neg hp17,
                    if_neg hp23, if_pos hp31]
                  exact (pow_ten_le_base_twentyThree a).trans <|
                    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hpLower a)
                · by_cases hp43 : p < 43
                  · have hpLower : 31 ≤ p := by omega
                    simp only [preliminaryPrimePenalty, if_neg hp3, if_neg hp5,
                      if_neg hp7, if_neg hp11, if_neg hp13, if_neg hp17,
                      if_neg hp23, if_neg hp31, if_pos hp43]
                    exact (pow_ten_le_base_thirtyOne a).trans <|
                      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hpLower a)
                  · by_cases hp67 : p < 67
                    · have hpLower : 43 ≤ p := by omega
                      simp only [preliminaryPrimePenalty, if_neg hp3, if_neg hp5,
                        if_neg hp7, if_neg hp11, if_neg hp13, if_neg hp17,
                        if_neg hp23, if_neg hp31, if_neg hp43, if_pos hp67]
                      exact (pow_ten_le_base_fortyThree a).trans <|
                        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hpLower a)
                    · by_cases hp131 : p < 131
                      · have hpLower : 67 ≤ p := by omega
                        simp only [preliminaryPrimePenalty, if_neg hp3,
                          if_neg hp5, if_neg hp7, if_neg hp11, if_neg hp13,
                          if_neg hp17, if_neg hp23, if_neg hp31, if_neg hp43,
                          if_neg hp67, if_pos hp131]
                        exact (pow_ten_le_base_sixtySeven a).trans <|
                          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hpLower a)
                      · by_cases hp257 : p < 257
                        · have hpLower : 131 ≤ p := by omega
                          simp only [preliminaryPrimePenalty, if_neg hp3,
                            if_neg hp5, if_neg hp7, if_neg hp11, if_neg hp13,
                            if_neg hp17, if_neg hp23, if_neg hp31, if_neg hp43,
                            if_neg hp67, if_neg hp131, if_pos hp257]
                          exact (pow_ten_le_base_oneHundredThirtyOne a).trans <|
                            Nat.mul_le_mul_left _
                              (Nat.pow_le_pow_left hpLower a)
                        · by_cases hp521 : p < 521
                          · have hpLower : 257 ≤ p := by omega
                            simp only [preliminaryPrimePenalty, if_neg hp3,
                              if_neg hp5, if_neg hp7, if_neg hp11, if_neg hp13,
                              if_neg hp17, if_neg hp23, if_neg hp31, if_neg hp43,
                              if_neg hp67, if_neg hp131, if_neg hp257,
                              if_pos hp521]
                            exact (pow_ten_le_base_twoHundredFiftySeven a).trans <|
                              Nat.mul_le_mul_left _
                                (Nat.pow_le_pow_left hpLower a)
                          · by_cases hp1024 : p < 1024
                            · have hpLower : 521 ≤ p := by omega
                              simp only [preliminaryPrimePenalty, if_neg hp3,
                                if_neg hp5, if_neg hp7, if_neg hp11, if_neg hp13,
                                if_neg hp17, if_neg hp23, if_neg hp31, if_neg hp43,
                                if_neg hp67, if_neg hp131, if_neg hp257,
                                if_neg hp521, if_pos hp1024]
                              exact (pow_ten_le_base_fiveHundredTwentyOne a).trans <|
                                Nat.mul_le_mul_left _
                                  (Nat.pow_le_pow_left hpLower a)
                            · have hpLower : 1024 ≤ p := by omega
                              simp only [preliminaryPrimePenalty, if_neg hp3,
                                if_neg hp5, if_neg hp7, if_neg hp11, if_neg hp13,
                                if_neg hp17, if_neg hp23, if_neg hp31, if_neg hp43,
                                if_neg hp67, if_neg hp131, if_neg hp257,
                                if_neg hp521, if_neg hp1024, pow_zero, one_mul]
                              exact
                                (pow_ten_le_base_oneThousandTwentyFour a).trans <|
                                  Nat.pow_le_pow_left hpLower a

-- Separate closed computations keep each kernel check within the default limit.
private def preliminaryPrimePenaltyBlock (k : ℕ) : ℕ :=
  ∑ p ∈ Finset.range 64, if Nat.Prime (k * 64 + p) then preliminaryPrimePenalty (k * 64 + p) else 0
private theorem preliminaryPrimePenaltyBlock_value_0 : preliminaryPrimePenaltyBlock 0 = 165 := by
  decide +kernel

private theorem preliminaryPrimePenaltyBlock_value_1 : preliminaryPrimePenaltyBlock 1 = 52 := by
  decide +kernel

private theorem preliminaryPrimePenaltyBlock_value_2 : preliminaryPrimePenaltyBlock 2 = 36 := by
  decide +kernel

private theorem preliminaryPrimePenaltyBlock_value_3 : preliminaryPrimePenaltyBlock 3 = 33 := by
  decide +kernel

private theorem preliminaryPrimePenaltyBlock_value_4 : preliminaryPrimePenaltyBlock 4 = 24 := by
  decide +kernel

private theorem preliminaryPrimePenaltyBlock_value_5 : preliminaryPrimePenaltyBlock 5 = 20 := by
  decide +kernel

private theorem preliminaryPrimePenaltyBlock_value_6 : preliminaryPrimePenaltyBlock 6 = 20 := by
  decide +kernel

private theorem preliminaryPrimePenaltyBlock_value_7 : preliminaryPrimePenaltyBlock 7 = 22 := by
  decide +kernel

private theorem preliminaryPrimePenaltyBlock_value_8 : preliminaryPrimePenaltyBlock 8 = 8 := by
  decide +kernel

private theorem preliminaryPrimePenaltyBlock_value_9 : preliminaryPrimePenaltyBlock 9 = 10 := by
  decide +kernel

private theorem preliminaryPrimePenaltyBlock_value_10 : preliminaryPrimePenaltyBlock 10 = 11 := by
  decide +kernel

private theorem preliminaryPrimePenaltyBlock_value_11 : preliminaryPrimePenaltyBlock 11 = 9 := by
  decide +kernel

private theorem preliminaryPrimePenaltyBlock_value_12 : preliminaryPrimePenaltyBlock 12 = 10 := by
  decide +kernel

private theorem preliminaryPrimePenaltyBlock_value_13 : preliminaryPrimePenaltyBlock 13 = 9 := by
  decide +kernel

private theorem preliminaryPrimePenaltyBlock_value_14 : preliminaryPrimePenaltyBlock 14 = 8 := by
  decide +kernel

private theorem preliminaryPrimePenaltyBlock_value_15 : preliminaryPrimePenaltyBlock 15 = 10 := by
  decide +kernel

private theorem sum_preliminaryPrimePenalty_blocks (k : ℕ) :
    (∑ p ∈ Finset.range (k * 64), if Nat.Prime p then preliminaryPrimePenalty p else 0) =
      ∑ i ∈ Finset.range k, preliminaryPrimePenaltyBlock i := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih]
    rw [Finset.sum_range_succ (f := preliminaryPrimePenaltyBlock)]
    rfl

private theorem sum_preliminaryPrimePenalty_le (n : ℕ) :
    ∑ p ∈ n.primeFactors, preliminaryPrimePenalty p ≤ 447 := by
  let smallFactors :=
    n.primeFactors.filter fun p ↦ p < 1024
  let allSmallPrimes :=
    (Finset.range 1024).filter Nat.Prime
  have hsumEq :
      (∑ p ∈ smallFactors, preliminaryPrimePenalty p) =
        ∑ p ∈ n.primeFactors, preliminaryPrimePenalty p := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro p hpFactors hpNotSmall
    have hpLarge : 1024 ≤ p := by
      by_contra hpNotLarge
      have hpSmall : p < 1024 := by omega
      exact hpNotSmall (Finset.mem_filter.mpr ⟨hpFactors, hpSmall⟩)
    exact preliminaryPrimePenalty_eq_zero_of_le hpLarge
  have hsubset : smallFactors ⊆ allSmallPrimes := by
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr hp'.2,
        Nat.prime_of_mem_primeFactors hp'.1⟩
  have hle :
      (∑ p ∈ smallFactors, preliminaryPrimePenalty p) ≤
        ∑ p ∈ allSmallPrimes, preliminaryPrimePenalty p :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun _ _ _ ↦ Nat.zero_le _)
  have htotal :
      (∑ p ∈ allSmallPrimes, preliminaryPrimePenalty p) ≤ 447 := by
    apply le_of_eq
    rw [Finset.sum_filter]
    change (∑ p ∈ Finset.range (16 * 64), if Nat.Prime p then preliminaryPrimePenalty p else 0) = _
    rw [sum_preliminaryPrimePenalty_blocks]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    rw [preliminaryPrimePenaltyBlock_value_0, preliminaryPrimePenaltyBlock_value_1,
      preliminaryPrimePenaltyBlock_value_2,
      preliminaryPrimePenaltyBlock_value_3,
      preliminaryPrimePenaltyBlock_value_4,
      preliminaryPrimePenaltyBlock_value_5,
      preliminaryPrimePenaltyBlock_value_6,
      preliminaryPrimePenaltyBlock_value_7,
      preliminaryPrimePenaltyBlock_value_8,
      preliminaryPrimePenaltyBlock_value_9,
      preliminaryPrimePenaltyBlock_value_10,
      preliminaryPrimePenaltyBlock_value_11,
      preliminaryPrimePenaltyBlock_value_12,
      preliminaryPrimePenaltyBlock_value_13,
      preliminaryPrimePenaltyBlock_value_14,
      preliminaryPrimePenaltyBlock_value_15]
  rw [← hsumEq]
  exact hle.trans htotal

/-- The divisor function satisfies the uniform elementary estimate
`τ(n)^10 ≤ 2^447 n`. -/
theorem card_divisors_pow_ten_le_preliminary_constant_mul
    (n : ℕ) (hn : n ≠ 0) :
    n.divisors.card ^ 10 ≤ 2 ^ 447 * n := by
  rw [Nat.card_divisors hn, ← Finset.prod_pow]
  calc
    (∏ p ∈ n.primeFactors, (n.factorization p + 1) ^ 10) ≤
        ∏ p ∈ n.primeFactors,
          (2 ^ preliminaryPrimePenalty p * p ^ n.factorization p) :=
      Finset.prod_le_prod
        (fun p hp ↦ factorization_succ_pow_ten_le
          (Nat.prime_of_mem_primeFactors hp))
    _ = 2 ^ (∑ p ∈ n.primeFactors, preliminaryPrimePenalty p) * n := by
      rw [Finset.prod_mul_distrib,
        Finset.prod_pow_eq_pow_sum,
        ← Nat.prod_primeFactors_pow_factorization hn]
    _ ≤ 2 ^ 447 * n :=
      Nat.mul_le_mul_right n <|
        Nat.pow_le_pow_right (by norm_num)
          (sum_preliminaryPrimePenalty_le n)

end BGS.NumberTheory
