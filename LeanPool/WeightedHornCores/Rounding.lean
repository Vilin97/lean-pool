/-
Copyright (c) 2026 Weighted Horn Cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weighted Horn Cores contributors
-/
module

public import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Rounding the doubling period

Bernoulli's inequality bounds the exponential cost of replacing the real period `m`
by its natural ceiling.
-/

@[expose] public section

namespace WeightedHornCores

/-- Rounding the period up to a positive integer preserves the stated real coefficient. -/
theorem rounded_coefficient_le {m : ℝ} (hm : 0 < m) :
    ((⌈m⌉₊ : ℕ) : ℝ) / Real.log 2 * (2 : ℝ) ^ (m / (⌈m⌉₊ : ℕ)) ≤
      2 * (1 + m / Real.log 2) := by
  let p : ℝ := ⌈m⌉₊
  have hmp : m ≤ p := Nat.le_ceil m
  have hp : 0 < p := hm.trans_le hmp
  have hceil : p < m + 1 := Nat.ceil_lt_add_one hm.le
  have hpow : (2 : ℝ) ^ (m / p) ≤ 1 + m / p := by
    simpa only [one_add_one_eq_two, mul_one] using
      rpow_one_add_le_one_add_mul_self (s := 1) (by norm_num) (div_nonneg hm.le hp.le)
        ((div_le_one hp).2 hmp)
  have hlog := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
  have hlogPos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  change p / Real.log 2 * (2 : ℝ) ^ (m / p) ≤ _
  rw [div_mul_eq_mul_div₀, div_le_iff₀ hlogPos, mul_assoc, add_mul, one_mul,
    div_mul_cancel₀ m hlogPos.ne']
  calc
    p * (2 : ℝ) ^ (m / p) ≤ p * (1 + m / p) := mul_le_mul_of_nonneg_left hpow hp.le
    _ = p + m := by rw [mul_add, mul_one, mul_comm p (m / p), div_mul_cancel₀ m hp.ne']
    _ ≤ 2 * (Real.log 2 + m) := by linarith only [hceil, hlog]

end WeightedHornCores
