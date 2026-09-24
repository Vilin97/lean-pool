/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Logarithm estimates for the local lemma

Section 10.2 of `bs_lambda.txt` applies the asymmetric Lovász local lemma.  This file
collects the facts about `Real.log` that the verification needs; none of them mentions the
construction.

## Two general estimates

* `le_mul_pow_mul_pow_of_lt_log` turns a local-lemma condition `p ≤ c p y₁^a y₂^b` into the
  logarithmic inequality `a (-log y₁) + b (-log y₂) < log c`;
* `neg_log_one_sub_le` is the elementary bound `-log (1-y) ≤ y / (1-y)` used to replace those
  logarithms by exact rationals.

## Two certified rational bounds

The local lemma is applied with `x₁ = (29/16) p₁` and `x₂ = (17/2) p₂`, so the two `log c`
above are `log (29/16)` and `log (17/2)`; `log_29_div_16_gt` and `log_17_div_2_gt` bound them
below.  Both split off a power of two, so that Mathlib's `Real.log_two_gt_d9` does most of the
work, and bound the remaining factor:

* `log (29/16) = log 2 + log (29/32)`, and `log (29/32) = log (1 - 3/32)` is bounded below by
  the cubic Taylor estimate `Real.abs_log_sub_add_sum_range_le` (`log_29_div_32_gt`);
* `log (17/2) = 3 log 2 + log (17/16)`, and `log (17/16) = -log (16/17) > 1/17` by
  `Real.log_lt_sub_one_of_pos` (`log_17_div_16_gt`).

Adapted for Lean Pool from `Timeroot/BS_Lam` at commit
`7bd39a8d41ee7910d3296d0477ad18f8fff9d870`; ported to Lean Pool with proof and dependency cleanup.
-/

@[expose] public section

namespace BSLambda.Numerics

/-! ### Two general estimates -/

/-- For `y < 1` one has `-log (1-y) ≤ y / (1-y)`; a repackaging of
`Real.one_sub_inv_le_log_of_pos`, and the elementary estimate used in Section 10.2 of
`bs_lambda.txt`. -/
theorem neg_log_one_sub_le {y : ℝ} (hy : y < 1) : -Real.log (1 - y) ≤ y / (1 - y) := by
  have hpos : (0 : ℝ) < 1 - y := sub_pos.mpr hy
  have h : (1 - y)⁻¹ - 1 = y / (1 - y) := by rw [← one_div, div_sub_one hpos.ne', sub_sub_cancel]
  linarith [Real.one_sub_inv_le_log_of_pos hpos]

/-- The analytic core of an asymmetric local-lemma condition: if `log c` exceeds the weighted
sum of the logarithmic losses `-log yᵢ`, then `p ≤ c p y₁^m y₂^n`. -/
theorem le_mul_pow_mul_pow_of_lt_log {p c y₁ y₂ : ℝ} {m n : ℕ} (hp : 0 < p) (hc : 0 < c)
    (hy₁ : 0 < y₁) (hy₂ : 0 < y₂)
    (h : (m : ℝ) * -Real.log y₁ + (n : ℝ) * -Real.log y₂ < Real.log c) :
    p ≤ c * p * y₁ ^ m * y₂ ^ n := by
  refine ((Real.log_lt_log_iff hp (by positivity)).mp ?_).le
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_mul hc.ne' hp.ne', Real.log_pow, Real.log_pow]
  linarith

/-! ### Two certified rational bounds -/

/-- Cubic Taylor lower bound for `log (29/32) = log (1 - 3/32)`.  The exact bound the Taylor
estimate gives is `-(3225/32768) - 81/950272 = -0.09850442…`; the true value is
`-0.09806…`. -/
theorem log_29_div_32_gt : (-0.0986 : ℝ) < Real.log (29 / 32) := by
  have h := Real.abs_log_sub_add_sum_range_le (show |(3 / 32 : ℝ)| < 1 by norm_num) 3
  norm_num [Finset.sum_range_succ] at h
  linarith [(abs_le.mp h).1]

/-- Lower bound `1/17 < log (17/16)`, from `log t < t - 1` at `t = 16/17`. -/
theorem log_17_div_16_gt : (1 / 17 : ℝ) < Real.log (17 / 16) := by
  have hinv : Real.log (17 / 16 : ℝ) = -Real.log (16 / 17) := by norm_num [← Real.log_inv]
  linarith [Real.log_lt_sub_one_of_pos (show (0 : ℝ) < 16 / 17 by norm_num) (by norm_num)]

/-- Certified rational lower bound `0.594 < log (29/16)`, the first of the two logarithm
estimates required by the local-lemma verification in Section 10.2 of `bs_lambda.txt`.  The
true value is `0.5947071077…`. -/
theorem log_29_div_16_gt : (0.594 : ℝ) < Real.log (29 / 16) := by
  rw [show (29 / 16 : ℝ) = 2 * (29 / 32) by norm_num, Real.log_mul two_ne_zero (by norm_num)]
  linarith [Real.log_two_gt_d9, log_29_div_32_gt]

/-- Certified rational lower bound `2.138 < log (17/2)`, the second of the two logarithm
estimates required by the local-lemma verification in Section 10.2 of `bs_lambda.txt`.  The
true value is `2.1400661635…`. -/
theorem log_17_div_2_gt : (2.138 : ℝ) < Real.log (17 / 2) := by
  rw [show (17 / 2 : ℝ) = 2 ^ (3 : ℕ) * (17 / 16) by norm_num,
    Real.log_mul (by positivity) (by norm_num), Real.log_pow, Nat.cast_ofNat]
  linarith [Real.log_two_gt_d9, log_17_div_16_gt]

end BSLambda.Numerics
