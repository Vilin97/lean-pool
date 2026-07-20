/-
Copyright (c) 2026 Ho Boon Suan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ho Boon Suan
-/

/-
# Log bounds for Phi endpoint proofs

Each log bound is proved using the atanh series:
- `Real.sum_range_le_log_div` for lower bounds on `log((1+t)/(1-t))`
- `Real.log_div_le_sum_range_add` for upper bounds on `log((1+t)/(1-t))`

The decomposition is `log(z) = e * log(2) + log(y)` where `z = 2^e * y`
with `1 ≤ y ≤ 2`, and `t = (y-1)/(y+1)`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Log bounds for Phi endpoint proofs

Numerical logarithm bounds proved via the atanh series and exact rational
estimates.
-/

namespace KaltonRoberts

open Real Finset

private lemma log_lower_from_atanh (x z c : ℝ) (n : ℕ)
    (hx₀ : 0 ≤ x) (hx₁ : x < 1)
    (hz : (1 + x) / (1 - x) = z)
    (hc : c ≤ 2 * (∑ i ∈ Finset.range n, x ^ (2 * i + 1) / (2 * i + 1))) :
    c ≤ Real.log z := by
  have h := Real.sum_range_le_log_div hx₀ hx₁ n
  rw [hz] at h
  nlinarith

private lemma log_upper_from_atanh (x z c : ℝ) (n : ℕ)
    (hx₀ : 0 ≤ x) (hx₁ : x < 1)
    (hz : (1 + x) / (1 - x) = z)
    (hc : 2 * ((∑ i ∈ Finset.range n, x ^ (2 * i + 1) / (2 * i + 1)) +
        x ^ (2 * n + 1) / (1 - x ^ 2)) ≤ c) :
    Real.log z ≤ c := by
  have h := Real.log_div_le_sum_range_add hx₀ hx₁ n
  rw [hz] at h
  nlinarith

/-! ## E₂ log bounds: Phi 4 (4/7) (3009/10000) -/

theorem log_lower_18937_70000 : (-817111/625000 : ℝ) ≤ Real.log (18937/70000) := by
  -- Applying the sum_range_le_log_div lemma with x = 1437/36437 and n = 8.
  have h_log_div :
      ∑ i ∈ Finset.range 8,
          (1437 / 36437 : ℝ) ^ (2 * i + 1) / (2 * i + 1) ≤
        (1 / 2) * Real.log ((1 + 1437 / 36437) / (1 - 1437 / 36437)) := by
    convert Real.sum_range_le_log_div
      (by norm_num : (0 : ℝ) ≤ 1437 / 36437) (by norm_num) 8
      using 1;
  norm_num [ Real.log_div ] at *;
  rw [ show ( 70000 : ℝ ) = 17500 * 4 by norm_num, Real.log_mul ] <;> norm_num at *;
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
  norm_num
  linarith [Real.log_two_lt_d9]

theorem log_lower_3009_10000 : (-12009773/10000000 : ℝ) ≤ Real.log (3009/10000) := by
  -- We'll use the fact that $Real.log (a / b) = Real.log a - Real.log b$ to simplify the
  -- expression.
  suffices h_suff : -12009773 / 10000000 ≤ Real.log 3009 - Real.log 10000 by
    rwa [ Real.log_div ( by norm_num ) ( by norm_num ) ];
  rw [ show ( 10000 : ℝ ) = 3009 * ( 10000 / 3009 ) by ring, Real.log_mul ] <;> norm_num at *;
  rw [ Real.log_le_iff_le_exp ] <;> norm_num at *;
  rw [ Real.exp_eq_exp_ℝ ];
  rw [ NormedSpace.exp_eq_tsum_div ];
  exact le_trans ( by norm_num ) ( Summable.sum_le_tsum ( Finset.range 20 ) ( fun _ _ => by
    positivity ) ( by exact Real.summable_pow_div_factorial _ ) )

theorem log_upper_4_7 : Real.log (4/7) ≤ (-5596157/10000000 : ℝ) := by
  have h : (5596157 / 10000000 : ℝ) ≤ Real.log (7 / 4) := by
    refine log_lower_from_atanh (x := 3 / 11) (z := 7 / 4)
      (c := 5596157 / 10000000) (n := 6) (by norm_num) (by norm_num)
      (by norm_num) ?_
    norm_num [Finset.sum_range_succ]
  have hlog : Real.log (4 / 7 : ℝ) = -Real.log (7 / 4 : ℝ) := by
    rw [show (4 / 7 : ℝ) = (7 / 4 : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [hlog]
  linarith

theorem log_lower_6991_10000 : (-715923/2000000 : ℝ) ≤ Real.log (6991/10000) := by
  rw [ Real.le_log_iff_exp_le ] <;> norm_num;
  -- We'll use the exponential property to simplify the expression. Note that $e^{715923 / 2000000}
  -- \approx 1.429$.
  have h_exp : Real.exp (715923 / 2000000) > 10000 / 6991 := by
    rw [ Real.exp_eq_exp_ℝ ];
    rw [ NormedSpace.exp_eq_tsum_div ];
    exact lt_of_lt_of_le ( by norm_num ) ( Summable.sum_le_tsum ( Finset.range 10 ) ( fun _ _ => by
      positivity ) ( by exact Real.summable_pow_div_factorial _ ) );
  rw [Real.exp_neg]
  nlinarith [
    Real.exp_pos (715923 / 2000000),
    mul_inv_cancel₀ (ne_of_gt (Real.exp_pos (715923 / 2000000)))]

theorem log_lower_9027_10000 : (-1023651/10000000 : ℝ) ≤ Real.log (9027/10000) := by
  have h : Real.log (10000 / 9027 : ℝ) ≤ 1023651 / 10000000 := by
    refine log_upper_from_atanh (x := 973 / 19027) (z := 10000 / 9027)
      (c := 1023651 / 10000000) (n := 3) (by norm_num) (by norm_num)
      (by norm_num) ?_
    norm_num [Finset.sum_range_succ]
  have hlog : Real.log (9027 / 10000 : ℝ) = -Real.log (10000 / 9027 : ℝ) := by
    rw [show (9027 / 10000 : ℝ) = (10000 / 9027 : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [hlog]
  linarith

theorem log_upper_21063_10000 : Real.log (21063/10000) ≤ (7449329/10000000 : ℝ) := by
  refine log_upper_from_atanh (x := 11063 / 31063) (z := 21063 / 10000)
    (c := 7449329 / 10000000) (n := 9) (by norm_num) (by norm_num)
    (by norm_num) ?_
  norm_num [Finset.sum_range_succ]

theorem log_upper_6991_2500 : Real.log (6991/2500) ≤ (10283329/10000000 : ℝ) := by
  rw [ Real.log_le_iff_le_exp ];
  · -- By calculating the first few terms of the Taylor series expansion for $e^{1.0283329}$, we can
    -- show that it is greater than $6991 / 2500$.
    have h_taylor : Real.exp (10283329 / 10000000) > 6991 / 2500 := by
      have h_series : Real.exp (10283329 / 10000000) = ∑' n : ℕ, (10283329 / 10000000 : ℝ)^n /
        Nat.factorial n := by
        simp +decide [ Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div ]
      rw [ h_series ];
      exact lt_of_lt_of_le ( by norm_num [ Finset.sum_range_succ, Nat.factorial ] ) (
        Summable.sum_le_tsum ( Finset.range 20 ) ( fun _ _ => by positivity ) (
          Real.summable_pow_div_factorial (10283329 / 10000000 : ℝ) ) );
    linarith;
  · norm_num

theorem log_lower_4 : (13862943/10000000 : ℝ) ≤ Real.log 4 := by
  rw [ show ( 4 : ℝ ) = 2 ^ 2 by norm_num, Real.log_pow ]; norm_num at *; have :=
    Real.log_two_gt_d9; norm_num at *; linarith;

/-! ## E₃ log bounds: Phi 4 (2/7) (47/625) -/

theorem log_lower_47_625 : (-25876041/10000000 : ℝ) ≤ Real.log (47/625) := by
  rw [ Real.le_log_iff_exp_le ] <;> norm_num;
  rw [ Real.exp_neg ];
  rw [ inv_le_comm₀, Real.exp_eq_exp_ℝ ] <;> norm_num [ NormedSpace.exp_eq_tsum_div ] at *;
  · exact le_trans ( by norm_num ) ( Summable.sum_le_tsum ( Finset.range 20 ) ( fun _ _ => by
    positivity ) ( by exact Real.summable_pow_div_factorial _ ) );
  · positivity

theorem log_lower_921_4375 : (-7791009/5000000 : ℝ) ≤ Real.log (921/4375) := by
  rw [ ← Real.log_exp ( -7791009 / 5000000 ) ];
  -- We'll use the exponential property to simplify the expression. Note that $e^{7791009 / 5000000}
  -- \geq 4375 / 921$.
  have h_exp : Real.exp (7791009 / 5000000) ≥ 4375 / 921 := by
    rw [ Real.exp_eq_exp_ℝ ];
    rw [ NormedSpace.exp_eq_tsum_div ];
    exact le_trans (by norm_num)
      (Summable.sum_le_tsum (Finset.range 20) (fun _ _ => by positivity) (by
        exact Real.summable_pow_div_factorial _))
  exact Real.log_le_log (by positivity) (by
    rw [show (Real.exp (-7791009 / 5000000) : ℝ) =
        (Real.exp (7791009 / 5000000))⁻¹ by
      rw [← Real.exp_neg]
      ring_nf]
    rw [inv_eq_one_div, div_le_div_iff₀] <;> linarith)

theorem log_upper_2_7 : Real.log (2/7) ≤ (-12527629/10000000 : ℝ) := by
  have h : (12527629 / 10000000 : ℝ) ≤ Real.log (7 / 2) := by
    refine log_lower_from_atanh (x := 5 / 9) (z := 7 / 2)
      (c := 12527629 / 10000000) (n := 12) (by norm_num) (by norm_num)
      (by norm_num) ?_
    norm_num [Finset.sum_range_succ]
  have hlog : Real.log (2 / 7 : ℝ) = -Real.log (7 / 2 : ℝ) := by
    rw [show (2 / 7 : ℝ) = (7 / 2 : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [hlog]
  linarith

theorem log_lower_94_125 : (-285019/1000000 : ℝ) ≤ Real.log (94/125) := by
  -- We'll use the exponential function to show that $94/125 > \exp(-0.285019)$.
  have h_exp : 94 / 125 > Real.exp (-0.285019) := by
    norm_num [ Real.exp_neg ] at *;
    rw [ inv_lt_comm₀, Real.exp_eq_exp_ℝ ] <;> norm_num [ NormedSpace.exp_eq_tsum_div ] at *;
    · exact lt_of_lt_of_le ( by norm_num [ Finset.sum_range_succ, Nat.factorial ] ) (
      Summable.sum_le_tsum ( Finset.range 10 ) ( fun _ _ => by positivity ) (
        Real.summable_pow_div_factorial (285019 / 1000000 : ℝ) ) );
    · positivity;
  exact le_trans ( by norm_num ) ( Real.log_le_log ( by positivity ) h_exp.le )

theorem log_lower_578_625 : (-390889/5000000 : ℝ) ≤ Real.log (578/625) := by
  have h : Real.log (625 / 578 : ℝ) ≤ 390889 / 5000000 := by
    refine log_upper_from_atanh (x := 47 / 1203) (z := 625 / 578)
      (c := 390889 / 5000000) (n := 3) (by norm_num) (by norm_num)
      (by norm_num) ?_
    norm_num [Finset.sum_range_succ]
  have hlog : Real.log (578 / 625 : ℝ) = -Real.log (625 / 578 : ℝ) := by
    rw [show (578 / 625 : ℝ) = (625 / 578 : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [hlog]
  linarith

theorem log_upper_658_625 : Real.log (658/625) ≤ (514533/10000000 : ℝ) := by
  refine log_upper_from_atanh (x := 33 / 1283) (z := 658 / 625)
    (c := 514533 / 10000000) (n := 2) (by norm_num) (by norm_num)
    (by norm_num) ?_
  norm_num [Finset.sum_range_succ]

theorem log_upper_2312_625 : Real.log (2312/625) ≤ (6540583/5000000 : ℝ) := by
  rw [ Real.log_le_iff_le_exp ] <;> norm_num;
  norm_num [ Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div ] at *;
  exact le_trans ( by norm_num ) ( Summable.sum_le_tsum ( Finset.range 20 ) ( fun _ _ => by
    positivity ) ( by exact Real.summable_pow_div_factorial _ ) )

/-! ## E₄ log bounds: Phi 5 (5/11) (329/1250) -/

theorem log_lower_2631_13750 : (-16536749/10000000 : ℝ) ≤ Real.log (2631/13750) := by
  have h : Real.log (13750 / 2631 : ℝ) ≤ 16536749 / 10000000 := by
    refine log_upper_from_atanh (x := 11119 / 16381) (z := 13750 / 2631)
      (c := 16536749 / 10000000) (n := 23) (by norm_num) (by norm_num)
      (by norm_num) ?_
    norm_num [Finset.sum_range_succ]
  have hlog : Real.log (2631 / 13750 : ℝ) = -Real.log (13750 / 2631 : ℝ) := by
    rw [show (2631 / 13750 : ℝ) = (13750 / 2631 : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [hlog]
  linarith

theorem log_lower_329_1250 : (-13348411/10000000 : ℝ) ≤ Real.log (329/1250) := by
  rw [ Real.le_log_iff_exp_le ] <;> norm_num;
  rw [ Real.exp_neg ];
  field_simp;
  rw [ ← div_le_iff₀ ] <;> norm_num [ Real.exp_eq_exp_ℝ ];
  rw [ NormedSpace.exp_eq_tsum_div ]; exact le_trans ( by norm_num ) ( Summable.sum_le_tsum (
    Finset.range 12 ) ( fun _ _ => by positivity ) ( by exact Real.summable_pow_div_factorial _ ) )

theorem log_upper_5_11 : Real.log (5/11) ≤ (-7884573/10000000 : ℝ) := by
  have h : (7884573 / 10000000 : ℝ) ≤ Real.log (11 / 5) := by
    refine log_lower_from_atanh (x := 3 / 8) (z := 11 / 5)
      (c := 7884573 / 10000000) (n := 8) (by norm_num) (by norm_num)
      (by norm_num) ?_
    norm_num [Finset.sum_range_succ]
  have hlog : Real.log (5 / 11 : ℝ) = -Real.log (11 / 5 : ℝ) := by
    rw [show (5 / 11 : ℝ) = (11 / 5 : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [hlog]
  linarith

theorem log_lower_921_1250 : (-763597/2500000 : ℝ) ≤ Real.log (921/1250) := by
  rw [← Real.log_exp (-763597 / 2500000 : ℝ), Real.le_log_iff_exp_le] <;>
    norm_num [Real.exp_neg] at *
  rw [ inv_eq_one_div, div_le_iff₀ ] <;> norm_num [ Real.exp_pos ];
  -- We'll use the exponential property to simplify the expression. Note that $e^{763597 / 2500000}
  -- = \left(e^{1 / 2500000}\right)^{763597}$.
  suffices h_exp : (Real.exp (1 / 2500000)) ^ 763597 ≥ 1250 / 921 by
    rw [ ← Real.exp_nat_mul ] at *; norm_num at *; linarith;
  -- We'll use the exponential property to simplify the expression. Note that
  -- $(e^{1/2500000})^{763597} = e^{763597/2500000}$.
  suffices h_exp : Real.exp (763597 / 2500000) ≥ 1250 / 921 by
    exact h_exp.trans_eq ( by rw [ ← Real.exp_nat_mul ]; ring_nf );
  rw [ Real.exp_eq_exp_ℝ ];
  rw [ NormedSpace.exp_eq_tsum_div ];
  exact le_trans ( by norm_num ) ( Summable.sum_le_tsum ( Finset.range 10 ) ( fun _ _ => by
    positivity ) ( by exact Real.summable_pow_div_factorial _ ) )

theorem log_lower_987_625 : (4569183/10000000 : ℝ) ≤ Real.log (987/625) := by
  refine log_lower_from_atanh (x := 181 / 806) (z := 987 / 625)
    (c := 4569183 / 10000000) (n := 5) (by norm_num) (by norm_num)
    (by norm_num) ?_
  norm_num [Finset.sum_range_succ]

theorem log_upper_3619_1250 : Real.log (3619/1250) ≤ (5315271/5000000 : ℝ) := by
  -- We'll use the exponential function to reverse the logarithm and compare the values.
  have h_exp : (3619 / 1250 : ℝ) ≤ Real.exp (5315271 / 5000000) := by
    rw [ Real.exp_eq_exp_ℝ ];
    rw [ NormedSpace.exp_eq_tsum_div ];
    exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
      (Summable.sum_le_tsum (Finset.range 20) (fun _ _ => by positivity) (by
        exact Real.summable_pow_div_factorial _))
  rwa [ Real.log_le_iff_le_exp ( by norm_num ) ]

theorem log_upper_921_250 : Real.log (921/250) ≤ (1629999/1250000 : ℝ) := by
  rw [ Real.log_le_iff_le_exp ] <;> norm_num;
  rw [ Real.exp_eq_exp_ℝ ];
  rw [ NormedSpace.exp_eq_tsum_div ];
  exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
    (Summable.sum_le_tsum (Finset.range 20) (fun _ _ => by positivity) (by
      exact Real.summable_pow_div_factorial _))

theorem log_lower_5 : (16094379/10000000 : ℝ) ≤ Real.log 5 := by
  refine log_lower_from_atanh (x := 2 / 3) (z := 5)
    (c := 16094379 / 10000000) (n := 19) (by norm_num) (by norm_num)
    (by norm_num) ?_
  norm_num [Finset.sum_range_succ]

end KaltonRoberts
