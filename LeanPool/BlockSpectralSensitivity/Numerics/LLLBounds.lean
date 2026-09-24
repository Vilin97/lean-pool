/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import LeanPool.BlockSpectralSensitivity.Numerics.Binomial
public import LeanPool.BlockSpectralSensitivity.Numerics.Logs

/-!
# The two asymmetric local-lemma inequalities

This file verifies the two numerical hypotheses of the asymmetric Lovász local lemma stated
in Section 10.2 of `bs_lambda.txt`, for the dependency counts of Section 10.1.

The bad events come in two types, with probabilities `p₁ = r⁻⁶` and `p₂ = K / r²⁰` at
`r = 144`, `K = 1300311466573824` (the Lean constant `BSLambda.LLL.radiusTwoConst`).  With
the choices `x₁ = (29/16) p₁` and `x₂ = (17/2) p₂`
the two conditions to check are

* `p₁ ≤ x₁ (1-x₁)^{D₁₁} (1-x₂)^{D₁₂}` (`lll_cond_one`),
* `p₂ ≤ x₂ (1-x₁)^{D₂₁} (1-x₂)^{D₂₂}` (`lll_cond_two`).

## Method

`BSLambda.Numerics.le_mul_pow_mul_pow_of_lt_log` reduces `p ≤ c p y₁^a y₂^b` to the
logarithmic inequality `a (-log y₁) + b (-log y₂) < log c`, and the elementary estimate
`BSLambda.Numerics.neg_log_one_sub_le` replaces the two logarithms by the *exact rationals*
`x₁ / (1 - x₁) = 29 / (16 · 144⁶ - 29)` and `x₂ / (1 - x₂) = 17 K / (2 · 144²⁰ - 17 K)`
(`add_mul_neg_log_one_sub_le`).  The resulting rational loss sums are bounded by `0.594` and
`2.138` in `loss_one_lt` and `loss_two_lt` — exactly the two thresholds for which
`BSLambda.Numerics.log_29_div_16_gt` and `BSLambda.Numerics.log_17_div_2_gt` supply certified
lower bounds on `log (29/16)` and `log (17/2)`.

Adapted for Lean Pool from `Timeroot/BS_Lam` at commit
`7bd39a8d41ee7910d3296d0477ad18f8fff9d870`; ported to Lean Pool with proof and dependency cleanup.
-/

@[expose] public section

namespace BSLambda.Numerics

/-! ### The dependency counts and the local-lemma parameters (Sections 10.1 and 10.2) -/

/-- The number of type-1 dependency neighbours of a type-1 event, `D₁₁ = 10 N₁`
(Section 10.1 of `bs_lambda.txt`). -/
def D11 : ℕ := 2146200875100

/-- The number of type-2 dependency neighbours of a type-1 event,
`D₁₂ = ∑_{s=2}^{5} C(5,s) C(14006,9-s)` (`D12_eq_sum`, Section 10.1 of `bs_lambda.txt`). -/
def D12 : ℕ := 209572451535510643927671555

/-- The number of type-1 dependency neighbours of a type-2 event, `D₂₁ = 36 N₁`
(Section 10.1 of `bs_lambda.txt`). -/
def D21 : ℕ := 7726323150360

/-- The number of type-2 dependency neighbours of a type-2 event,
`D₂₂ = (∑_{s=2}^{9} C(9,s) C(14002,9-s)) - 1` (`D22_eq_sum`, Section 10.1 of
`bs_lambda.txt`); the subtraction removes the event itself. -/
def D22 : ℕ := 753455972623601870517771054

/-- The type-1 event probability `p₁ = r⁻⁶` at `r = 144` (Section 10 of `bs_lambda.txt`). -/
noncomputable def p1 : ℝ := 1 / 144 ^ 6

/-- The type-2 event probability bound `p₂ = K / r²⁰` at `r = 144` and
`K = 1300311466573824` (`BSLambda.LLL.radiusTwoConst`; Sections 9 and 10 of
`bs_lambda.txt`). -/
noncomputable def p2 : ℝ := 1300311466573824 / 144 ^ 20

/-- The local-lemma parameter `x₁ = (29/16) p₁` (Section 10.2 of `bs_lambda.txt`). -/
noncomputable def x1 : ℝ := 29 / (16 * 144 ^ 6)

/-- The local-lemma parameter `x₂ = (17/2) p₂` (Section 10.2 of `bs_lambda.txt`). -/
noncomputable def x2 : ℝ := 17 * 1300311466573824 / (2 * 144 ^ 20)

/-- `D₂₁ = 36 N₁`, with `N₁ = 214620087510` the radius-one flag count of Section 8.2
(`typeAFlagSum_eq` and `typeBFlagSum_eq`). -/
theorem D21_eq_thirtysix_mul : D21 = 36 * 214620087510 := by norm_num [D21]

/-- `D₁₂` is the Section 10.1 sum it abbreviates; the evaluation is `depSumOneTwo_eq`. -/
theorem D12_eq_sum :
    D12 = ∑ s ∈ Finset.Icc 2 5, Nat.choose 5 s * Nat.choose 14006 (9 - s) := depSumOneTwo_eq.symm

/-- `D₂₂` is the Section 10.1 sum it abbreviates; the evaluation is `depSumTwoTwo_eq`. -/
theorem D22_eq_sum :
    D22 = (∑ s ∈ Finset.Icc 2 9, Nat.choose 9 s * Nat.choose 14002 (9 - s)) - 1 :=
  depSumTwoTwo_eq.symm

/-! ### Positivity of the local-lemma parameters (Section 10.2) -/

/-- The local-lemma parameter `x₁` is positive (Section 10.2 of `bs_lambda.txt`). -/
theorem x1_pos : 0 < x1 := by norm_num [x1]

/-- The local-lemma parameter `x₂` is positive (Section 10.2 of `bs_lambda.txt`). -/
theorem x2_pos : 0 < x2 := by norm_num [x2]

/-- The local-lemma parameter `x₁` lies below `1` (Section 10.2 of `bs_lambda.txt`). -/
theorem x1_lt_one : x1 < 1 := by norm_num [x1]

/-- The local-lemma parameter `x₂` lies below `1` (Section 10.2 of `bs_lambda.txt`). -/
theorem x2_lt_one : x2 < 1 := by norm_num [x2]

/-! ### The two rational loss sums (Section 10.2) -/

/-- The type-1 loss sum is below `0.594` (Section 10.2 of `bs_lambda.txt`).  This is a
statement about explicit rationals. The true value is `0.5938861514605…`. -/
theorem loss_one_lt : (D11 : ℝ) * (x1 / (1 - x1)) + (D12 : ℝ) * (x2 / (1 - x2)) < 0.594 := by
  norm_num [D11, D12, x1, x2]

/-- The type-2 loss sum is below `2.138` (Section 10.2 of `bs_lambda.txt`).  This is a
statement about explicit rationals. The true value is `2.1372344982481…`. -/
theorem loss_two_lt : (D21 : ℝ) * (x1 / (1 - x1)) + (D22 : ℝ) * (x2 / (1 - x2)) < 2.138 := by
  norm_num [D21, D22, x1, x2]

/-- The logarithmic losses at `x₁` and `x₂`, weighted by two dependency counts, are bounded
by the corresponding sum of exact rationals (Section 10.2 of `bs_lambda.txt`). -/
theorem add_mul_neg_log_one_sub_le (m n : ℕ) :
    (m : ℝ) * -Real.log (1 - x1) + (n : ℝ) * -Real.log (1 - x2) ≤
      (m : ℝ) * (x1 / (1 - x1)) + (n : ℝ) * (x2 / (1 - x2)) := by
  gcongr
  · exact neg_log_one_sub_le x1_lt_one
  · exact neg_log_one_sub_le x2_lt_one

/-! ### The two local-lemma conditions (Section 10.2) -/

/-- The type-1 asymmetric local-lemma condition
`p₁ ≤ x₁ (1-x₁)^{D₁₁} (1-x₂)^{D₁₂}` (Section 10.2 of `bs_lambda.txt`). -/
theorem lll_cond_one : p1 ≤ x1 * (1 - x1) ^ D11 * (1 - x2) ^ D12 := by
  nth_rewrite 1 [show x1 = 29 / 16 * p1 by norm_num [x1, p1]]
  exact le_mul_pow_mul_pow_of_lt_log (by norm_num [p1]) (by norm_num) (sub_pos.mpr x1_lt_one)
    (sub_pos.mpr x2_lt_one)
    ((add_mul_neg_log_one_sub_le D11 D12).trans_lt (loss_one_lt.trans log_29_div_16_gt))

/-- The type-2 asymmetric local-lemma condition
`p₂ ≤ x₂ (1-x₁)^{D₂₁} (1-x₂)^{D₂₂}` (Section 10.2 of `bs_lambda.txt`). -/
theorem lll_cond_two : p2 ≤ x2 * (1 - x1) ^ D21 * (1 - x2) ^ D22 := by
  nth_rewrite 1 [show x2 = 17 / 2 * p2 by norm_num [x2, p2]]
  exact le_mul_pow_mul_pow_of_lt_log (by norm_num [p2]) (by norm_num) (sub_pos.mpr x1_lt_one)
    (sub_pos.mpr x2_lt_one)
    ((add_mul_neg_log_one_sub_le D21 D22).trans_lt (loss_two_lt.trans log_17_div_2_gt))

end BSLambda.Numerics
