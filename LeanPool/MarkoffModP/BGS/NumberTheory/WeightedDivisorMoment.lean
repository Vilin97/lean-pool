/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.NumberTheory.PreliminaryDivisorBound
import Mathlib.Tactic.IntervalCases

/-!
# A weighted twentieth-moment divisor bound

Squaring the elementary tenth-moment estimate would give
`τ(n)^20 ≤ 2^894 n^2`.  That loses the fractional part of every
prime-factor penalty before the square is taken.  Charging the doubled
weight directly preserves those fractional parts and gives the stronger
uniform estimate

`τ(n)^20 ≤ 2^796 n^2`.

The proof uses the same finite-band induction as the tenth-moment bound.
It does not enumerate integers, factorizations, or neighboring divisor
profiles.
-/

namespace BGS.NumberTheory

open scoped BigOperators

/-- Tenth-power ratio monotonicity used before squaring the weighted estimate. -/
private theorem weighted_pow_ten_succ_ratio_le
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

/-- Once the twentieth-power ratio is controlled, it remains controlled
at every later exponent. -/
private theorem pow_twenty_succ_ratio_le
    (base A a : ℕ) (ha : A ≤ a)
    (hbase : (A + 2) ^ 20 ≤ base ^ 2 * (A + 1) ^ 20) :
    (a + 2) ^ 20 ≤ base ^ 2 * (a + 1) ^ 20 := by
  have hbaseTenSq : ((A + 2) ^ 10) ^ 2 ≤
      (base * (A + 1) ^ 10) ^ 2 := by
    calc
      ((A + 2) ^ 10) ^ 2 = (A + 2) ^ 20 := by
        rw [← pow_mul]
      _ ≤ base ^ 2 * (A + 1) ^ 20 := hbase
      _ = base ^ 2 * ((A + 1) ^ 10) ^ 2 := by
        rw [← pow_mul]
      _ = (base * (A + 1) ^ 10) ^ 2 := by rw [mul_pow]
  have hbaseTen : (A + 2) ^ 10 ≤ base * (A + 1) ^ 10 :=
    (Nat.pow_le_pow_iff_left (by norm_num : 2 ≠ 0)).mp hbaseTenSq
  have hten := weighted_pow_ten_succ_ratio_le base A a ha hbaseTen
  have hsq := Nat.pow_le_pow_left hten 2
  calc
    (a + 2) ^ 20 = ((a + 2) ^ 10) ^ 2 := by
      rw [← pow_mul]
    _ ≤ (base * (a + 1) ^ 10) ^ 2 := hsq
    _ = base ^ 2 * ((a + 1) ^ 10) ^ 2 := by rw [mul_pow]
    _ = base ^ 2 * (a + 1) ^ 20 := by
      rw [← pow_mul]

/-- Induction from a finite threshold for a fixed prime-size band. -/
private theorem pow_twenty_le_band_of_threshold
    (base c A : ℕ)
    (hbase : (A + 1) ^ 20 ≤ 2 ^ c * base ^ (2 * A))
    (hratio : (A + 2) ^ 20 ≤ base ^ 2 * (A + 1) ^ 20)
    (a : ℕ) (ha : A ≤ a) :
    (a + 1) ^ 20 ≤ 2 ^ c * base ^ (2 * a) := by
  induction a, ha using Nat.le_induction with
  | base => exact hbase
  | succ a ha ih =>
      calc
        (a + 1 + 1) ^ 20 ≤ base ^ 2 * (a + 1) ^ 20 :=
          pow_twenty_succ_ratio_le base A a ha hratio
        _ ≤ base ^ 2 * (2 ^ c * base ^ (2 * a)) :=
          Nat.mul_le_mul_left _ ih
        _ = 2 ^ c * base ^ (2 * (a + 1)) := by
          rw [show 2 * (a + 1) = 2 * a + 2 by omega, pow_add]
          ring

private theorem pow_twenty_le_base_two (a : ℕ) :
    (a + 1) ^ 20 ≤ 2 ^ 51 * 2 ^ (2 * a) := by
  by_cases ha : 13 ≤ a
  · simpa using pow_twenty_le_band_of_threshold 2 51 13
      (by norm_num) (by norm_num) a ha
  · have ha' : a ≤ 12 := by omega
    interval_cases a <;> norm_num

private theorem pow_twenty_le_base_three (a : ℕ) :
    (a + 1) ^ 20 ≤ 2 ^ 39 * 3 ^ (2 * a) := by
  by_cases ha : 8 ≤ a
  · simpa using pow_twenty_le_band_of_threshold 3 39 8
      (by norm_num) (by norm_num) a ha
  · have ha' : a ≤ 7 := by omega
    interval_cases a <;> norm_num

private theorem pow_twenty_le_base_five (a : ℕ) :
    (a + 1) ^ 20 ≤ 2 ^ 29 * 5 ^ (2 * a) := by
  by_cases ha : 5 ≤ a
  · simpa using pow_twenty_le_band_of_threshold 5 29 5
      (by norm_num) (by norm_num) a ha
  · have ha' : a ≤ 4 := by omega
    interval_cases a <;> norm_num

private theorem pow_twenty_le_base_seven (a : ℕ) :
    (a + 1) ^ 20 ≤ 2 ^ 24 * 7 ^ (2 * a) := by
  by_cases ha : 4 ≤ a
  · simpa using pow_twenty_le_band_of_threshold 7 24 4
      (by norm_num) (by norm_num) a ha
  · have ha' : a ≤ 3 := by omega
    interval_cases a <;> norm_num

private theorem pow_twenty_le_base_eleven (a : ℕ) :
    (a + 1) ^ 20 ≤ 2 ^ 20 * 11 ^ (2 * a) := by
  by_cases ha : 3 ≤ a
  · simpa using pow_twenty_le_band_of_threshold 11 20 3
      (by norm_num) (by norm_num) a ha
  · have ha' : a ≤ 2 := by omega
    interval_cases a <;> norm_num

private theorem pow_twenty_le_base_thirteen (a : ℕ) :
    (a + 1) ^ 20 ≤ 2 ^ 18 * 13 ^ (2 * a) := by
  by_cases ha : 3 ≤ a
  · simpa using pow_twenty_le_band_of_threshold 13 18 3
      (by norm_num) (by norm_num) a ha
  · have ha' : a ≤ 2 := by omega
    interval_cases a <;> norm_num

private theorem pow_twenty_le_base_seventeen (a : ℕ) :
    (a + 1) ^ 20 ≤ 2 ^ 16 * 17 ^ (2 * a) := by
  by_cases ha : 3 ≤ a
  · simpa using pow_twenty_le_band_of_threshold 17 16 3
      (by norm_num) (by norm_num) a ha
  · have ha' : a ≤ 2 := by omega
    interval_cases a <;> norm_num

private theorem pow_twenty_le_base_nineteen (a : ℕ) :
    (a + 1) ^ 20 ≤ 2 ^ 15 * 19 ^ (2 * a) := by
  by_cases ha : 2 ≤ a
  · simpa using pow_twenty_le_band_of_threshold 19 15 2
      (by norm_num) (by norm_num) a ha
  · have ha' : a ≤ 1 := by omega
    interval_cases a <;> norm_num

private theorem pow_twenty_le_base_twentyThree (a : ℕ) :
    (a + 1) ^ 20 ≤ 2 ^ 14 * 23 ^ (2 * a) := by
  by_cases ha : 2 ≤ a
  · simpa using pow_twenty_le_band_of_threshold 23 14 2
      (by norm_num) (by norm_num) a ha
  · have ha' : a ≤ 1 := by omega
    interval_cases a <;> norm_num

private theorem pow_twenty_le_base_twentyNine (a : ℕ) :
    (a + 1) ^ 20 ≤ 2 ^ 13 * 29 ^ (2 * a) := by
  by_cases ha : 2 ≤ a
  · simpa using pow_twenty_le_band_of_threshold 29 13 2
      (by norm_num) (by norm_num) a ha
  · have ha' : a ≤ 1 := by omega
    interval_cases a <;> norm_num

private theorem pow_twenty_le_base_thirtyOne (a : ℕ) :
    (a + 1) ^ 20 ≤ 2 ^ 12 * 31 ^ (2 * a) := by
  by_cases ha : 2 ≤ a
  · simpa using pow_twenty_le_band_of_threshold 31 12 2
      (by norm_num) (by norm_num) a ha
  · have ha' : a ≤ 1 := by omega
    interval_cases a <;> norm_num

private theorem pow_twenty_le_base_thirtySeven (a : ℕ) :
    (a + 1) ^ 20 ≤ 2 ^ 11 * 37 ^ (2 * a) := by
  by_cases ha : 2 ≤ a
  · simpa using pow_twenty_le_band_of_threshold 37 11 2
      (by norm_num) (by norm_num) a ha
  · have ha' : a ≤ 1 := by omega
    interval_cases a <;> norm_num

private theorem pow_twenty_le_base_fortyThree (a : ℕ) :
    (a + 1) ^ 20 ≤ 2 ^ 10 * 43 ^ (2 * a) := by
  by_cases ha : 2 ≤ a
  · simpa using pow_twenty_le_band_of_threshold 43 10 2
      (by norm_num) (by norm_num) a ha
  · have ha' : a ≤ 1 := by omega
    interval_cases a <;> norm_num

private theorem pow_twenty_le_base_fiftyThree (a : ℕ) :
    (a + 1) ^ 20 ≤ 2 ^ 9 * 53 ^ (2 * a) := by
  by_cases ha : 2 ≤ a
  · simpa using pow_twenty_le_band_of_threshold 53 9 2
      (by norm_num) (by norm_num) a ha
  · have ha' : a ≤ 1 := by omega
    interval_cases a <;> norm_num

private theorem pow_twenty_le_base_sixtySeven (a : ℕ) :
    (a + 1) ^ 20 ≤ 2 ^ 8 * 67 ^ (2 * a) := by
  by_cases ha : 1 ≤ a
  · simpa using pow_twenty_le_band_of_threshold 67 8 1
      (by norm_num) (by norm_num) a ha
  · have ha' : a ≤ 0 := by omega
    interval_cases a <;> norm_num

private theorem pow_twenty_le_base_ninetySeven (a : ℕ) :
    (a + 1) ^ 20 ≤ 2 ^ 7 * 97 ^ (2 * a) := by
  by_cases ha : 1 ≤ a
  · simpa using pow_twenty_le_band_of_threshold 97 7 1
      (by norm_num) (by norm_num) a ha
  · have ha' : a ≤ 0 := by omega
    interval_cases a <;> norm_num

private theorem pow_twenty_le_base_oneHundredThirtyOne (a : ℕ) :
    (a + 1) ^ 20 ≤ 2 ^ 6 * 131 ^ (2 * a) := by
  by_cases ha : 1 ≤ a
  · simpa using pow_twenty_le_band_of_threshold 131 6 1
      (by norm_num) (by norm_num) a ha
  · have ha' : a ≤ 0 := by omega
    interval_cases a <;> norm_num

private theorem pow_twenty_le_base_oneHundredNinetyOne (a : ℕ) :
    (a + 1) ^ 20 ≤ 2 ^ 5 * 191 ^ (2 * a) := by
  by_cases ha : 1 ≤ a
  · simpa using pow_twenty_le_band_of_threshold 191 5 1
      (by norm_num) (by norm_num) a ha
  · have ha' : a ≤ 0 := by omega
    interval_cases a <;> norm_num

private theorem pow_twenty_le_base_twoHundredFiftySeven (a : ℕ) :
    (a + 1) ^ 20 ≤ 2 ^ 4 * 257 ^ (2 * a) := by
  by_cases ha : 1 ≤ a
  · simpa using pow_twenty_le_band_of_threshold 257 4 1
      (by norm_num) (by norm_num) a ha
  · have ha' : a ≤ 0 := by omega
    interval_cases a <;> norm_num

private theorem pow_twenty_le_base_threeHundredSixtySeven (a : ℕ) :
    (a + 1) ^ 20 ≤ 2 ^ 3 * 367 ^ (2 * a) := by
  by_cases ha : 1 ≤ a
  · simpa using pow_twenty_le_band_of_threshold 367 3 1
      (by norm_num) (by norm_num) a ha
  · have ha' : a ≤ 0 := by omega
    interval_cases a <;> norm_num

private theorem pow_twenty_le_base_fiveHundredTwentyOne (a : ℕ) :
    (a + 1) ^ 20 ≤ 2 ^ 2 * 521 ^ (2 * a) := by
  by_cases ha : 1 ≤ a
  · simpa using pow_twenty_le_band_of_threshold 521 2 1
      (by norm_num) (by norm_num) a ha
  · have ha' : a ≤ 0 := by omega
    interval_cases a <;> norm_num

private theorem pow_twenty_le_base_sevenHundredTwentySeven (a : ℕ) :
    (a + 1) ^ 20 ≤ 2 * 727 ^ (2 * a) := by
  by_cases ha : 1 ≤ a
  · simpa using pow_twenty_le_band_of_threshold 727 1 1
      (by norm_num) (by norm_num) a ha
  · have ha' : a ≤ 0 := by omega
    interval_cases a <;> norm_num

private theorem pow_twenty_le_base_oneThousandTwentyFour (a : ℕ) :
    (a + 1) ^ 20 ≤ 1024 ^ (2 * a) := by
  simpa using pow_twenty_le_band_of_threshold 1024 0 0
    (by norm_num) (by norm_num) a (Nat.zero_le a)

/-- The exact integer penalty bands for the weight pair `(20, 2)`. -/
def weightedPrimePenaltyTwenty (p : ℕ) : ℕ :=
  if p < 3 then 51
  else if p < 5 then 39
  else if p < 7 then 29
  else if p < 11 then 24
  else if p < 13 then 20
  else if p < 17 then 18
  else if p < 19 then 16
  else if p < 23 then 15
  else if p < 29 then 14
  else if p < 31 then 13
  else if p < 37 then 12
  else if p < 43 then 11
  else if p < 53 then 10
  else if p < 67 then 9
  else if p < 97 then 8
  else if p < 131 then 7
  else if p < 191 then 6
  else if p < 257 then 5
  else if p < 367 then 4
  else if p < 521 then 3
  else if p < 727 then 2
  else if p < 1024 then 1
  else 0

private theorem weightedPrimePenaltyTwenty_eq_zero_of_le
    {p : ℕ} (hp : 1024 ≤ p) :
    weightedPrimePenaltyTwenty p = 0 := by
  simp [weightedPrimePenaltyTwenty,
    show ¬p < 3 by omega, show ¬p < 5 by omega,
    show ¬p < 7 by omega, show ¬p < 11 by omega,
    show ¬p < 13 by omega, show ¬p < 17 by omega,
    show ¬p < 19 by omega, show ¬p < 23 by omega,
    show ¬p < 29 by omega, show ¬p < 31 by omega,
    show ¬p < 37 by omega, show ¬p < 43 by omega,
    show ¬p < 53 by omega, show ¬p < 67 by omega,
    show ¬p < 97 by omega, show ¬p < 131 by omega,
    show ¬p < 191 by omega, show ¬p < 257 by omega,
    show ¬p < 367 by omega, show ¬p < 521 by omega,
    show ¬p < 727 by omega, show ¬p < 1024 by omega]

private theorem pow_twenty_le_of_base_le
    {base p c a : ℕ}
    (h : (a + 1) ^ 20 ≤ 2 ^ c * base ^ (2 * a))
    (hbase : base ≤ p) :
    (a + 1) ^ 20 ≤ 2 ^ c * p ^ (2 * a) :=
  h.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hbase _))

/-- Factorwise twentieth-moment estimate for the doubled number weight. -/
private theorem factorization_succ_pow_twenty_le
    {p a : ℕ} (hpPrime : p.Prime) :
    (a + 1) ^ 20 ≤
      2 ^ weightedPrimePenaltyTwenty p * p ^ (2 * a) := by
  have hpTwo : 2 ≤ p := hpPrime.two_le
  by_cases hp3 : p < 3
  · simp only [weightedPrimePenaltyTwenty, if_pos hp3]
    exact pow_twenty_le_of_base_le (pow_twenty_le_base_two a) hpTwo
  · by_cases hp5 : p < 5
    · have hpLower : 3 ≤ p := by omega
      simp only [weightedPrimePenaltyTwenty, if_neg hp3, if_pos hp5]
      exact pow_twenty_le_of_base_le (pow_twenty_le_base_three a) hpLower
    · by_cases hp7 : p < 7
      · have hpLower : 5 ≤ p := by omega
        simp only [weightedPrimePenaltyTwenty, if_neg hp3, if_neg hp5, if_pos hp7]
        exact pow_twenty_le_of_base_le (pow_twenty_le_base_five a) hpLower
      · by_cases hp11 : p < 11
        · have hpLower : 7 ≤ p := by omega
          simp only [weightedPrimePenaltyTwenty, if_neg hp3, if_neg hp5,
            if_neg hp7, if_pos hp11]
          exact pow_twenty_le_of_base_le (pow_twenty_le_base_seven a) hpLower
        · by_cases hp13 : p < 13
          · have hpLower : 11 ≤ p := by omega
            simp only [weightedPrimePenaltyTwenty, if_neg hp3, if_neg hp5,
              if_neg hp7, if_neg hp11, if_pos hp13]
            exact pow_twenty_le_of_base_le (pow_twenty_le_base_eleven a) hpLower
          · by_cases hp17 : p < 17
            · have hpLower : 13 ≤ p := by omega
              simp only [weightedPrimePenaltyTwenty, if_neg hp3, if_neg hp5,
                if_neg hp7, if_neg hp11, if_neg hp13, if_pos hp17]
              exact pow_twenty_le_of_base_le (pow_twenty_le_base_thirteen a) hpLower
            · by_cases hp19 : p < 19
              · have hpLower : 17 ≤ p := by omega
                simp only [weightedPrimePenaltyTwenty, if_neg hp3, if_neg hp5,
                  if_neg hp7, if_neg hp11, if_neg hp13, if_neg hp17, if_pos hp19]
                exact pow_twenty_le_of_base_le
                  (pow_twenty_le_base_seventeen a) hpLower
              · by_cases hp23 : p < 23
                · have hpLower : 19 ≤ p := by omega
                  simp only [weightedPrimePenaltyTwenty, if_neg hp3, if_neg hp5,
                    if_neg hp7, if_neg hp11, if_neg hp13, if_neg hp17,
                    if_neg hp19, if_pos hp23]
                  exact pow_twenty_le_of_base_le
                    (pow_twenty_le_base_nineteen a) hpLower
                · by_cases hp29 : p < 29
                  · have hpLower : 23 ≤ p := by omega
                    simp only [weightedPrimePenaltyTwenty, if_neg hp3, if_neg hp5,
                      if_neg hp7, if_neg hp11, if_neg hp13, if_neg hp17,
                      if_neg hp19, if_neg hp23, if_pos hp29]
                    exact pow_twenty_le_of_base_le
                      (pow_twenty_le_base_twentyThree a) hpLower
                  · by_cases hp31 : p < 31
                    · have hpLower : 29 ≤ p := by omega
                      simp only [weightedPrimePenaltyTwenty, if_neg hp3, if_neg hp5,
                        if_neg hp7, if_neg hp11, if_neg hp13, if_neg hp17,
                        if_neg hp19, if_neg hp23, if_neg hp29, if_pos hp31]
                      exact pow_twenty_le_of_base_le
                        (pow_twenty_le_base_twentyNine a) hpLower
                    · by_cases hp37 : p < 37
                      · have hpLower : 31 ≤ p := by omega
                        simp only [weightedPrimePenaltyTwenty, if_neg hp3,
                          if_neg hp5, if_neg hp7, if_neg hp11, if_neg hp13,
                          if_neg hp17, if_neg hp19, if_neg hp23, if_neg hp29,
                          if_neg hp31, if_pos hp37]
                        exact pow_twenty_le_of_base_le
                          (pow_twenty_le_base_thirtyOne a) hpLower
                      · by_cases hp43 : p < 43
                        · have hpLower : 37 ≤ p := by omega
                          simp only [weightedPrimePenaltyTwenty, if_neg hp3,
                            if_neg hp5, if_neg hp7, if_neg hp11, if_neg hp13,
                            if_neg hp17, if_neg hp19, if_neg hp23, if_neg hp29,
                            if_neg hp31, if_neg hp37, if_pos hp43]
                          exact pow_twenty_le_of_base_le
                            (pow_twenty_le_base_thirtySeven a) hpLower
                        · by_cases hp53 : p < 53
                          · have hpLower : 43 ≤ p := by omega
                            simp only [weightedPrimePenaltyTwenty, if_neg hp3,
                              if_neg hp5, if_neg hp7, if_neg hp11, if_neg hp13,
                              if_neg hp17, if_neg hp19, if_neg hp23, if_neg hp29,
                              if_neg hp31, if_neg hp37, if_neg hp43, if_pos hp53]
                            exact pow_twenty_le_of_base_le
                              (pow_twenty_le_base_fortyThree a) hpLower
                          · by_cases hp67 : p < 67
                            · have hpLower : 53 ≤ p := by omega
                              simp only [weightedPrimePenaltyTwenty, if_neg hp3,
                                if_neg hp5, if_neg hp7, if_neg hp11, if_neg hp13,
                                if_neg hp17, if_neg hp19, if_neg hp23, if_neg hp29,
                                if_neg hp31, if_neg hp37, if_neg hp43, if_neg hp53,
                                if_pos hp67]
                              exact pow_twenty_le_of_base_le
                                (pow_twenty_le_base_fiftyThree a) hpLower
                            · by_cases hp97 : p < 97
                              · have hpLower : 67 ≤ p := by omega
                                simp only [weightedPrimePenaltyTwenty, if_neg hp3,
                                  if_neg hp5, if_neg hp7, if_neg hp11,
                                  if_neg hp13, if_neg hp17, if_neg hp19,
                                  if_neg hp23, if_neg hp29, if_neg hp31,
                                  if_neg hp37, if_neg hp43, if_neg hp53,
                                  if_neg hp67, if_pos hp97]
                                exact pow_twenty_le_of_base_le
                                  (pow_twenty_le_base_sixtySeven a) hpLower
                              · by_cases hp131 : p < 131
                                · have hpLower : 97 ≤ p := by omega
                                  simp only [weightedPrimePenaltyTwenty,
                                    if_neg hp3, if_neg hp5, if_neg hp7,
                                    if_neg hp11, if_neg hp13, if_neg hp17,
                                    if_neg hp19, if_neg hp23, if_neg hp29,
                                    if_neg hp31, if_neg hp37, if_neg hp43,
                                    if_neg hp53, if_neg hp67, if_neg hp97,
                                    if_pos hp131]
                                  exact pow_twenty_le_of_base_le
                                    (pow_twenty_le_base_ninetySeven a) hpLower
                                · by_cases hp191 : p < 191
                                  · have hpLower : 131 ≤ p := by omega
                                    simp only [weightedPrimePenaltyTwenty,
                                      if_neg hp3, if_neg hp5, if_neg hp7,
                                      if_neg hp11, if_neg hp13, if_neg hp17,
                                      if_neg hp19, if_neg hp23, if_neg hp29,
                                      if_neg hp31, if_neg hp37, if_neg hp43,
                                      if_neg hp53, if_neg hp67, if_neg hp97,
                                      if_neg hp131, if_pos hp191]
                                    exact pow_twenty_le_of_base_le
                                      (pow_twenty_le_base_oneHundredThirtyOne a)
                                      hpLower
                                  · by_cases hp257 : p < 257
                                    · have hpLower : 191 ≤ p := by omega
                                      simp only [weightedPrimePenaltyTwenty,
                                        if_neg hp3, if_neg hp5, if_neg hp7,
                                        if_neg hp11, if_neg hp13, if_neg hp17,
                                        if_neg hp19, if_neg hp23, if_neg hp29,
                                        if_neg hp31, if_neg hp37, if_neg hp43,
                                        if_neg hp53, if_neg hp67, if_neg hp97,
                                        if_neg hp131, if_neg hp191, if_pos hp257]
                                      exact pow_twenty_le_of_base_le
                                        (pow_twenty_le_base_oneHundredNinetyOne a)
                                        hpLower
                                    · by_cases hp367 : p < 367
                                      · have hpLower : 257 ≤ p := by omega
                                        simp only [weightedPrimePenaltyTwenty,
                                          if_neg hp3, if_neg hp5, if_neg hp7,
                                          if_neg hp11, if_neg hp13, if_neg hp17,
                                          if_neg hp19, if_neg hp23, if_neg hp29,
                                          if_neg hp31, if_neg hp37, if_neg hp43,
                                          if_neg hp53, if_neg hp67, if_neg hp97,
                                          if_neg hp131, if_neg hp191,
                                          if_neg hp257, if_pos hp367]
                                        exact pow_twenty_le_of_base_le
                                          (pow_twenty_le_base_twoHundredFiftySeven a)
                                          hpLower
                                      · by_cases hp521 : p < 521
                                        · have hpLower : 367 ≤ p := by omega
                                          simp only [weightedPrimePenaltyTwenty,
                                            if_neg hp3, if_neg hp5, if_neg hp7,
                                            if_neg hp11, if_neg hp13, if_neg hp17,
                                            if_neg hp19, if_neg hp23, if_neg hp29,
                                            if_neg hp31, if_neg hp37, if_neg hp43,
                                            if_neg hp53, if_neg hp67, if_neg hp97,
                                            if_neg hp131, if_neg hp191,
                                            if_neg hp257, if_neg hp367,
                                            if_pos hp521]
                                          exact pow_twenty_le_of_base_le
                                            (pow_twenty_le_base_threeHundredSixtySeven a)
                                            hpLower
                                        · by_cases hp727 : p < 727
                                          · have hpLower : 521 ≤ p := by omega
                                            simp only [weightedPrimePenaltyTwenty,
                                              if_neg hp3, if_neg hp5, if_neg hp7,
                                              if_neg hp11, if_neg hp13,
                                              if_neg hp17, if_neg hp19,
                                              if_neg hp23, if_neg hp29,
                                              if_neg hp31, if_neg hp37,
                                              if_neg hp43, if_neg hp53,
                                              if_neg hp67, if_neg hp97,
                                              if_neg hp131, if_neg hp191,
                                              if_neg hp257, if_neg hp367,
                                              if_neg hp521, if_pos hp727]
                                            exact pow_twenty_le_of_base_le
                                              (pow_twenty_le_base_fiveHundredTwentyOne a)
                                              hpLower
                                          · by_cases hp1024 : p < 1024
                                            · have hpLower : 727 ≤ p := by omega
                                              simp only [weightedPrimePenaltyTwenty,
                                                if_neg hp3, if_neg hp5,
                                                if_neg hp7, if_neg hp11,
                                                if_neg hp13, if_neg hp17,
                                                if_neg hp19, if_neg hp23,
                                                if_neg hp29, if_neg hp31,
                                                if_neg hp37, if_neg hp43,
                                                if_neg hp53, if_neg hp67,
                                                if_neg hp97, if_neg hp131,
                                                if_neg hp191, if_neg hp257,
                                                if_neg hp367, if_neg hp521,
                                                if_neg hp727, if_pos hp1024]
                                              exact pow_twenty_le_of_base_le
                                                (pow_twenty_le_base_sevenHundredTwentySeven a)
                                                hpLower
                                            · have hpLower : 1024 ≤ p := by omega
                                              simp only [weightedPrimePenaltyTwenty,
                                                if_neg hp3, if_neg hp5,
                                                if_neg hp7, if_neg hp11,
                                                if_neg hp13, if_neg hp17,
                                                if_neg hp19, if_neg hp23,
                                                if_neg hp29, if_neg hp31,
                                                if_neg hp37, if_neg hp43,
                                                if_neg hp53, if_neg hp67,
                                                if_neg hp97, if_neg hp131,
                                                if_neg hp191, if_neg hp257,
                                                if_neg hp367, if_neg hp521,
                                                if_neg hp727, if_neg hp1024,
                                                pow_zero, one_mul]
                                              simpa only [pow_zero, one_mul] using
                                                (pow_twenty_le_of_base_le (c := 0)
                                                  (by simpa only [pow_zero, one_mul] using
                                                    pow_twenty_le_base_oneThousandTwentyFour a)
                                                  hpLower)

-- Separate closed computations keep each kernel check within the default limit.
private def weightedPrimePenaltyTwentyBlock (k : ℕ) : ℕ :=
  ∑ p ∈ Finset.range 64, if Nat.Prime (k * 64 + p) then weightedPrimePenaltyTwenty (k * 64 + p) else 0
private theorem weightedPrimePenaltyTwentyBlock_value_0 : weightedPrimePenaltyTwentyBlock 0 = 320 := by
  decide +kernel

private theorem weightedPrimePenaltyTwentyBlock_value_1 : weightedPrimePenaltyTwentyBlock 1 = 97 := by
  decide +kernel

private theorem weightedPrimePenaltyTwentyBlock_value_2 : weightedPrimePenaltyTwentyBlock 2 = 71 := by
  decide +kernel

private theorem weightedPrimePenaltyTwentyBlock_value_3 : weightedPrimePenaltyTwentyBlock 3 = 55 := by
  decide +kernel

private theorem weightedPrimePenaltyTwentyBlock_value_4 : weightedPrimePenaltyTwentyBlock 4 = 48 := by
  decide +kernel

private theorem weightedPrimePenaltyTwentyBlock_value_5 : weightedPrimePenaltyTwentyBlock 5 = 36 := by
  decide +kernel

private theorem weightedPrimePenaltyTwentyBlock_value_6 : weightedPrimePenaltyTwentyBlock 6 = 30 := by
  decide +kernel

private theorem weightedPrimePenaltyTwentyBlock_value_7 : weightedPrimePenaltyTwentyBlock 7 = 33 := by
  decide +kernel

private theorem weightedPrimePenaltyTwentyBlock_value_8 : weightedPrimePenaltyTwentyBlock 8 = 16 := by
  decide +kernel

private theorem weightedPrimePenaltyTwentyBlock_value_9 : weightedPrimePenaltyTwentyBlock 9 = 20 := by
  decide +kernel

private theorem weightedPrimePenaltyTwentyBlock_value_10 : weightedPrimePenaltyTwentyBlock 10 = 22 := by
  decide +kernel

private theorem weightedPrimePenaltyTwentyBlock_value_11 : weightedPrimePenaltyTwentyBlock 11 = 11 := by
  decide +kernel

private theorem weightedPrimePenaltyTwentyBlock_value_12 : weightedPrimePenaltyTwentyBlock 12 = 10 := by
  decide +kernel

private theorem weightedPrimePenaltyTwentyBlock_value_13 : weightedPrimePenaltyTwentyBlock 13 = 9 := by
  decide +kernel

private theorem weightedPrimePenaltyTwentyBlock_value_14 : weightedPrimePenaltyTwentyBlock 14 = 8 := by
  decide +kernel

private theorem weightedPrimePenaltyTwentyBlock_value_15 : weightedPrimePenaltyTwentyBlock 15 = 10 := by
  decide +kernel

private theorem sum_weightedPrimePenaltyTwenty_blocks (k : ℕ) :
    (∑ p ∈ Finset.range (k * 64), if Nat.Prime p then weightedPrimePenaltyTwenty p else 0) =
      ∑ i ∈ Finset.range k, weightedPrimePenaltyTwentyBlock i := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih]
    rw [Finset.sum_range_succ (f := weightedPrimePenaltyTwentyBlock)]
    rfl

private theorem sum_weightedPrimePenaltyTwenty_le (n : ℕ) :
    ∑ p ∈ n.primeFactors, weightedPrimePenaltyTwenty p ≤ 796 := by
  let smallFactors :=
    n.primeFactors.filter fun p ↦ p < 1024
  let allSmallPrimes :=
    (Finset.range 1024).filter Nat.Prime
  have hsumEq :
      (∑ p ∈ smallFactors, weightedPrimePenaltyTwenty p) =
        ∑ p ∈ n.primeFactors, weightedPrimePenaltyTwenty p := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro p hpFactors hpNotSmall
    have hpLarge : 1024 ≤ p := by
      by_contra hpNotLarge
      have hpSmall : p < 1024 := by omega
      exact hpNotSmall (Finset.mem_filter.mpr ⟨hpFactors, hpSmall⟩)
    exact weightedPrimePenaltyTwenty_eq_zero_of_le hpLarge
  have hsubset : smallFactors ⊆ allSmallPrimes := by
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr hp'.2,
        Nat.prime_of_mem_primeFactors hp'.1⟩
  have hle :
      (∑ p ∈ smallFactors, weightedPrimePenaltyTwenty p) ≤
        ∑ p ∈ allSmallPrimes, weightedPrimePenaltyTwenty p :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun _ _ _ ↦ Nat.zero_le _)
  have htotal :
      (∑ p ∈ allSmallPrimes, weightedPrimePenaltyTwenty p) ≤ 796 := by
    apply le_of_eq
    rw [Finset.sum_filter]
    change (∑ p ∈ Finset.range (16 * 64), if Nat.Prime p then weightedPrimePenaltyTwenty p else 0) = _
    rw [sum_weightedPrimePenaltyTwenty_blocks]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    rw [weightedPrimePenaltyTwentyBlock_value_0, weightedPrimePenaltyTwentyBlock_value_1,
      weightedPrimePenaltyTwentyBlock_value_2,
      weightedPrimePenaltyTwentyBlock_value_3,
      weightedPrimePenaltyTwentyBlock_value_4,
      weightedPrimePenaltyTwentyBlock_value_5,
      weightedPrimePenaltyTwentyBlock_value_6,
      weightedPrimePenaltyTwentyBlock_value_7,
      weightedPrimePenaltyTwentyBlock_value_8,
      weightedPrimePenaltyTwentyBlock_value_9,
      weightedPrimePenaltyTwentyBlock_value_10,
      weightedPrimePenaltyTwentyBlock_value_11,
      weightedPrimePenaltyTwentyBlock_value_12,
      weightedPrimePenaltyTwentyBlock_value_13,
      weightedPrimePenaltyTwentyBlock_value_14,
      weightedPrimePenaltyTwentyBlock_value_15]
  rw [← hsumEq]
  exact hle.trans htotal

/-- Weighted elementary divisor estimate:
`τ(n)^20 ≤ 2^796 n^2`. -/
theorem card_divisors_pow_twenty_le_weighted_constant_mul_sq
    (n : ℕ) (hn : n ≠ 0) :
    n.divisors.card ^ 20 ≤ 2 ^ 796 * n ^ 2 := by
  rw [Nat.card_divisors hn, ← Finset.prod_pow]
  calc
    (∏ p ∈ n.primeFactors, (n.factorization p + 1) ^ 20) ≤
        ∏ p ∈ n.primeFactors,
          (2 ^ weightedPrimePenaltyTwenty p *
            p ^ (2 * n.factorization p)) :=
      Finset.prod_le_prod
        (fun p hp ↦ factorization_succ_pow_twenty_le
          (Nat.prime_of_mem_primeFactors hp))
    _ = 2 ^ (∑ p ∈ n.primeFactors, weightedPrimePenaltyTwenty p) * n ^ 2 := by
      rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
      congr 1
      calc
        (∏ p ∈ n.primeFactors, p ^ (2 * n.factorization p)) =
            ∏ p ∈ n.primeFactors, (p ^ n.factorization p) ^ 2 := by
          apply Finset.prod_congr rfl
          intro p hp
          rw [show 2 * n.factorization p = n.factorization p * 2 by omega, pow_mul]
        _ = (∏ p ∈ n.primeFactors, p ^ n.factorization p) ^ 2 := by
          exact Finset.prod_pow n.primeFactors 2
            (fun p => p ^ n.factorization p)
        _ = n ^ 2 := by rw [← Nat.prod_primeFactors_pow_factorization hn]
    _ ≤ 2 ^ 796 * n ^ 2 :=
      Nat.mul_le_mul_right (n ^ 2) <|
        Nat.pow_le_pow_right (by norm_num)
          (sum_weightedPrimePenaltyTwenty_le n)

end BGS.NumberTheory
