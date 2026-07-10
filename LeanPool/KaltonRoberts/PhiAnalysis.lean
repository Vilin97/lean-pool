/-
Copyright (c) 2026 Ho Boon Suan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ho Boon Suan
-/

/-
# Phi function analysis: convexity, endpoint bounds, interval negativity

This file provides the analytic tools needed to prove `Phi_neg_Eᵢ` for each
row of the expander table. All theorems are fully proved.
-/
import LeanPool.KaltonRoberts.Defs
import LeanPool.KaltonRoberts.PhiDeriv
import LeanPool.KaltonRoberts.LogBounds

/-!
# Phi function analysis

Convexity, endpoint bounds, and interval-negativity proofs for the Phi
functions used in the expander table.
-/

namespace KaltonRoberts

open Real Finset

/-! ## Convexity bridge -/

/-- If `f` is convex on `[a, b]` and negative at both endpoints,
then `f` is negative on the entire interval. -/
theorem convexOn_Icc_neg_of_endpoints {a b : ℝ} {f : ℝ → ℝ}
    (hab : a ≤ b)
    (hconv : ConvexOn ℝ (Set.Icc a b) f)
    (hfa : f a < 0) (hfb : f b < 0)
    (x : ℝ) (hxa : a ≤ x) (hxb : x ≤ b) : f x < 0 := by
  have hle := hconv.le_max_of_mem_Icc
    (Set.left_mem_Icc.mpr hab) (Set.right_mem_Icc.mpr hab) ⟨hxa, hxb⟩
  exact lt_of_le_of_lt hle (max_lt hfa hfb)

/-! ## Real Phi'' lower bounds -/

theorem Phi''_lower_real_E₁ :
    ∀ x : ℝ, 1/100 ≤ x → x ≤ 1003/10000 →
      3 < (4 - 2) / x + (4 - 1) / (1 - x) - 1 / (1/3 - x) := by
  intro x hx₁ hx₂
  rw [div_add_div, div_sub_div, lt_div_iff₀] <;>
  nlinarith [sq_nonneg (x - 1003 / 10000)]

theorem Phi''_lower_real_E₂ :
    ∀ x : ℝ, 1/100 ≤ x → x ≤ 3009/10000 →
      3 < (4 - 2) / x + (4 - 1) / (1 - x) - 1 / (4/7 - x) := by
  intro x hx₁ hx₂
  rw [div_add_div, div_sub_div, lt_div_iff₀] <;>
  nlinarith [mul_self_nonneg (x - 1 / 100), mul_self_nonneg (x - 3009 / 10000)]

theorem Phi''_lower_real_E₃ :
    ∀ x : ℝ, 1/100 ≤ x → x ≤ 47/625 →
      3 < (4 - 2) / x + (4 - 1) / (1 - x) - 1 / (2/7 - x) := by
  intro x hx₁ hx₂
  rw [div_add_div, div_sub_div, lt_div_iff₀] <;>
  nlinarith [sq_nonneg (x - 1 / 100)]

theorem Phi''_lower_real_E₄ :
    ∀ x : ℝ, 1/100 ≤ x → x ≤ 329/1250 →
      3 < (5 - 2) / x + (5 - 1) / (1 - x) - 1 / (5/11 - x) := by
  intro x hx₁ hx₂
  rw [div_add_div, div_sub_div, lt_div_iff₀] <;> try nlinarith
  · nlinarith [sq_nonneg (x - 1 / 100), mul_le_mul_of_nonneg_left hx₂ (sub_nonneg_of_le hx₁)]
  · exact mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)

/-! ## ConvexOn for Phi on each row interval

These follow from the generic `convexOn_Phi_of_Phi''_nonneg` in PhiDeriv.lean,
instantiated with the real Phi'' lower bounds proved above. -/

theorem convexOn_Phi_E₁ :
    ConvexOn ℝ (Set.Icc (1/100 : ℝ) (1003/10000)) (fun x => Phi 4 (1/3) x) :=
  convexOn_Phi_of_Phi''_nonneg (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
    (fun x hx₁ hx₂ =>
      le_of_lt (by
        unfold Phi''
        linarith [Phi''_lower_real_E₁ x hx₁ hx₂]))

theorem convexOn_Phi_E₂ :
    ConvexOn ℝ (Set.Icc (1/100 : ℝ) (3009/10000)) (fun x => Phi 4 (4/7) x) :=
  convexOn_Phi_of_Phi''_nonneg (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
    (fun x hx₁ hx₂ =>
      le_of_lt (by
        unfold Phi''
        linarith [Phi''_lower_real_E₂ x hx₁ hx₂]))

theorem convexOn_Phi_E₃ :
    ConvexOn ℝ (Set.Icc (1/100 : ℝ) (47/625)) (fun x => Phi 4 (2/7) x) :=
  convexOn_Phi_of_Phi''_nonneg (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
    (fun x hx₁ hx₂ =>
      le_of_lt (by
        unfold Phi''
        linarith [Phi''_lower_real_E₃ x hx₁ hx₂]))

theorem convexOn_Phi_E₄ :
    ConvexOn ℝ (Set.Icc (1/100 : ℝ) (329/1250)) (fun x => Phi 5 (5/11) x) :=
  convexOn_Phi_of_Phi''_nonneg (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
    (fun x hx₁ hx₂ =>
      le_of_lt (by
        unfold Phi''
        linarith [Phi''_lower_real_E₄ x hx₁ hx₂]))

/-! ## Endpoint Phi upper bounds

These require atanh-based log certificates from `Real.sum_range_sub_log_div_le`.
Each endpoint bound is a finite computation involving ~8 log evaluations.
-/

theorem Phi_E₁_at_delta : Phi 4 (1/3) (1/100 : ℝ) < -(1 : ℝ)/1000 := by
  norm_num [ Phi, hEntropy ] at *;
  norm_num [ Real.log_div ];
  rw [show (100 : ℝ) = 10 ^ 2 by norm_num,
    show (99 : ℝ) = 3 ^ 2 * 11 by norm_num,
    show (300 : ℝ) = 3 * 10 ^ 2 by norm_num,
    show (25 : ℝ) = 5 ^ 2 by norm_num, Real.log_mul,
    Real.log_mul, Real.log_pow, Real.log_pow, Real.log_pow] <;>
    ring_nf <;> norm_num;
  rw [ show ( 97 : ℝ ) = 2 ^ 6 * ( 97 / 64 ) by norm_num, Real.log_mul, Real.log_pow ] <;> ring_nf
    <;> norm_num;
  rw [show (10 : ℝ) = 2 * 5 by norm_num,
    show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_mul, Real.log_pow] <;>
    ring_nf <;> norm_num;
  rw [ show ( 5 : ℝ ) = 2 ^ 2 * 1.25 by norm_num, Real.log_mul, Real.log_pow ] <;> ring_nf <;>
    norm_num;
  have := Real.log_two_gt_d9;
  norm_num at *;
  rw [show (3 : ℝ) = 2 * 1.5 by norm_num, Real.log_mul] <;> norm_num;
  rw [ show ( 11 : ℝ ) = 2 ^ 3 * ( 11 / 8 ) by norm_num, Real.log_mul, Real.log_pow ] <;> ring_nf
    <;> norm_num;
  have := Real.sum_range_le_log_div
    (show 0 ≤ 1 / 9 by norm_num) (show 1 / 9 < 1 by norm_num) 6;
  norm_num at *;
  (have := Real.log_div_le_sum_range_add
    (show 0 ≤ 1 / 9 by norm_num) (show 1 / 9 < 1 by norm_num) 6;
   norm_num at *);
  have := Real.sum_range_le_log_div
    (show 0 ≤ 1 / 5 by norm_num) (show 1 / 5 < 1 by norm_num) 6;
  norm_num at *;
  (have := Real.log_div_le_sum_range_add
    (show 0 ≤ 1 / 5 by norm_num) (show 1 / 5 < 1 by norm_num) 6;
   norm_num at *);
  have := Real.sum_range_le_log_div
    (show 0 ≤ 3 / 19 by norm_num) (show 3 / 19 < 1 by norm_num) 6;
  norm_num at *;
  (have := Real.log_div_le_sum_range_add
    (show 0 ≤ 3 / 19 by norm_num) (show 3 / 19 < 1 by norm_num) 6;
   norm_num at *);
  have := Real.sum_range_le_log_div
    (show 0 ≤ 33 / 161 by norm_num) (show 33 / 161 < 1 by norm_num) 6;
  norm_num at *;
  (have := Real.log_div_le_sum_range_add
    (show 0 ≤ 33 / 161 by norm_num) (show 33 / 161 < 1 by norm_num) 6;
   norm_num at *);
  linarith

theorem Phi_E₁_at_alpha : Phi 4 (1/3) (1003/10000 : ℝ) < -(1 : ℝ)/1000 := by
  unfold Phi hEntropy;
  have := Real.sum_range_le_log_div
    (show 0 ≤ 21 / 2027 by norm_num) (show 21 / 2027 < 1 by norm_num) 8;
  have := Real.log_div_le_sum_range_add
    (show 0 ≤ 951 / 5047 by norm_num) (show 951 / 5047 < 1 by norm_num) 8;
  norm_num [Finset.sum_range_succ] at this;
  have := Real.sum_range_le_log_div
    (show 0 ≤ 2895 / 11087 by norm_num) (show 2895 / 11087 < 1 by norm_num) 8;
  norm_num [Finset.sum_range_succ] at this;
  have := Real.sum_range_le_log_div
    (show 0 ≤ 1 / 9 by norm_num) (show 1 / 9 < 1 by norm_num) 8;
  norm_num [Finset.sum_range_succ] at this;
  have := Real.log_div_le_sum_range_add
    (show 0 ≤ 1 / 5 by norm_num) (show 1 / 5 < 1 by norm_num) 8;
  norm_num [Finset.sum_range_succ] at this;
  norm_num [ Real.log_div ] at *;
  rw [ show ( 10000 : ℝ ) = 10 ^ 4 by norm_num, Real.log_pow ]; norm_num;
  rw [ show ( 10 : ℝ ) = 2 * 5 by norm_num, Real.log_mul ] <;> norm_num;
  rw [show (30000 : ℝ) = 2 ^ 4 * 3 * 5 ^ 4 by norm_num,
    Real.log_mul, Real.log_mul, Real.log_pow, Real.log_pow] <;> norm_num;
  rw [ show ( 3009 : ℝ ) = 3 * 1003 by norm_num, Real.log_mul ] <;> norm_num;
  rw [ show ( 8997 : ℝ ) = 3 * 2999 by norm_num, Real.log_mul ] <;> norm_num;
  rw [show (2500 : ℝ) = 2 ^ 2 * 5 ^ 4 by norm_num, Real.log_mul,
    Real.log_pow, Real.log_pow] <;> norm_num;
  rw [ show ( 1250 : ℝ ) = 2 * 5 ^ 4 by norm_num, Real.log_mul, Real.log_pow ] <;> norm_num;
  rw [ show ( 1024 : ℝ ) = 2 ^ 10 by norm_num, Real.log_pow ] at *; norm_num at *;
  rw [ show ( 4096 : ℝ ) = 2 ^ 12 by norm_num, Real.log_pow ] at *; norm_num at *;
  rw [ show ( 2048 : ℝ ) = 2 ^ 11 by norm_num, Real.log_pow ] at *; norm_num at *;
  rw [ show ( 4 : ℝ ) = 2 ^ 2 by norm_num, Real.log_pow ] at *; norm_num at *;
  linarith [ Real.log_two_gt_d9 ]

theorem Phi_E₂_at_delta : Phi 4 (4/7) (1/100 : ℝ) < -(1 : ℝ)/1000 := by
  unfold Phi hEntropy; norm_num [ Real.log_div ];
  rw [show (100 : ℝ) = 2 ^ 2 * 5 ^ 2 by norm_num,
    show (99 : ℝ) = 3 ^ 2 * 11 by norm_num,
    show (4 : ℝ) = 2 ^ 2 by norm_num,
    show (700 : ℝ) = 2 ^ 2 * 5 ^ 2 * 7 by norm_num,
    show (393 : ℝ) = 3 * 131 by norm_num, Real.log_mul, Real.log_mul,
    Real.log_mul, Real.log_mul, Real.log_mul] <;> norm_num;
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow];
  rw [show (25 : ℝ) = 5 ^ 2 by norm_num, Real.log_pow];
  rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.log_pow];
  ring_nf;
      norm_num;
  rw [ show ( 5 : ℝ ) = 2 ^ 2 * 1.25 by norm_num, Real.log_mul, Real.log_pow ] <;> ring_nf <;>
    norm_num;
  -- We'll use the fact that $log(131) > log(128) = 7log(2)$ to bound the term involving $log(131)$.
  have h_log_131 : Real.log 131 > 7 * Real.log 2 := by
    norm_num [ ← Real.log_rpow, Real.log_lt_log ];
  have h_log_3 : Real.log 3 < 1.1 := by
    norm_num [ Real.log_lt_iff_lt_exp ];
    -- We can raise both sides to the power of 10 to get $3^{10} < e^{11}$.
    have h_exp : (3 : ℝ) ^ 10 < Real.exp 11 := by
      have := Real.exp_one_gt_d9.le;
      norm_num at *;
      rw [show Real.exp 11 = (Real.exp 1) ^ 11 by
        rw [← Real.exp_nat_mul]; norm_num];
      exact lt_of_lt_of_le (by norm_num)
        (pow_le_pow_left₀ (by positivity) this _);
    contrapose! h_exp;
    exact le_trans (by norm_num [← Real.exp_nat_mul])
      (pow_le_pow_left₀ (by positivity) h_exp 10)
  have h_log_11 : Real.log 11 < 2.4 := by
    norm_num [ Real.log_lt_iff_lt_exp ] at *;
    -- We can raise both sides to the power of 5 to get $11^5 < e^{12}$.
    have h_exp : (11 : ℝ)^5 < Real.exp 12 := by
      have := Real.exp_one_gt_d9.le;
      norm_num at *;
      rw [show Real.exp 12 = (Real.exp 1) ^ 12 by
        rw [← Real.exp_nat_mul]; norm_num];
      exact lt_of_lt_of_le (by norm_num)
        (pow_le_pow_left₀ (by positivity) this _);
    contrapose! h_exp;
    exact le_trans (by norm_num [← Real.exp_nat_mul])
      (pow_le_pow_left₀ (by positivity) h_exp 5)
  have h_log_7 : Real.log 7 < 2 := by
    rw [ Real.log_lt_iff_lt_exp ] <;> norm_num;
    have := Real.exp_one_gt_d9.le;
    norm_num at *;
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add];
    nlinarith [Real.add_one_le_exp 1]
  have h_log_5_4 : Real.log (5 / 4) > 0.22 := by
    norm_num [ Real.log_lt_log ] at *;
    rw [ div_lt_iff₀' ] <;> norm_num [ ← Real.log_rpow, Real.lt_log_iff_exp_lt ];
    have := Real.exp_one_lt_d9.le;
    norm_num1 at *;
    rw [show Real.exp 11 = (Real.exp 1) ^ 11 by
      rw [← Real.exp_nat_mul]; norm_num];
    exact lt_of_le_of_lt (pow_le_pow_left₀ (by positivity) this _) (by norm_num);
  have := Real.log_two_gt_d9; norm_num at *; linarith

theorem Phi_E₂_at_alpha : Phi 4 (4/7) (3009/10000 : ℝ) < -(1 : ℝ)/1000 := by
  have h_expr : Phi 4 (4/7) (3009/10000) =
    (-18937/70000) * Real.log (18937/70000)
    + (-3009/5000) * Real.log (3009/10000)
    + (4/7) * Real.log (4/7)
    + (-6991/10000) * Real.log (6991/10000)
    + (-9027/10000) * Real.log (9027/10000)
    + (21063/10000) * Real.log (21063/10000)
    + (6991/2500) * Real.log (6991/2500)
    + (-4) * Real.log 4 := by
    unfold Phi hEntropy; simp only [Real.log_one, mul_zero, zero_sub]; ring_nf
  rw [h_expr]
  nlinarith [log_lower_18937_70000, log_lower_3009_10000, log_upper_4_7,
    log_lower_6991_10000, log_lower_9027_10000, log_upper_21063_10000,
    log_upper_6991_2500, log_lower_4]

theorem Phi_E₃_at_delta : Phi 4 (2/7) (1/100 : ℝ) < -(1 : ℝ)/1000 := by
  unfold Phi hEntropy;
  norm_num [ Real.log_div ]; ring_nf; norm_num;
  rw [show (99 : ℝ) = 100 * (99 / 100) by norm_num,
    show (700 : ℝ) = 100 * 7 by norm_num, Real.log_mul, Real.log_mul] <;>
    ring_nf <;> norm_num;
  rw [show (100 : ℝ) = 10 ^ 2 by norm_num, Real.log_pow];
  rw [show (50 : ℝ) = 10 * 5 by norm_num, Real.log_mul] <;> norm_num;
  rw [show (25 : ℝ) = 5 ^ 2 by norm_num, Real.log_pow];
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow];
  ring_nf;
  rw [ show ( 10 : ℝ ) = 2 * 5 by norm_num, Real.log_mul ] <;> norm_num;
  -- We'll use the fact that $\log(99/100) \approx -0.01005$ and $\log(193) \approx 5.263$ to
  -- simplify the expression.
  have h_approx : Real.log (99 / 100) < -0.01 ∧ Real.log 193 > 5.26 := by
    constructor <;> norm_num [ Real.log_lt_iff_lt_exp, Real.lt_log_iff_exp_lt ];
    · exact lt_of_le_of_lt ( by norm_num ) ( Real.add_one_lt_exp ( by norm_num ) );
    · have := Real.exp_one_lt_d9
      -- We can raise both sides to the power of 50 to get
      -- $(\exp(263 / 50))^{50} < 193^{50}$, which simplifies to
      -- $\exp 263 < 193^{50}$.
      have h_exp : Real.exp 263 < 193 ^ 50 := by
        have h_exp_bound : Real.exp 263 < (2.719 : ℝ) ^ 263 := by
          have hbase : Real.exp 1 < (2.719 : ℝ) := by linarith [this]
          have hpow : (Real.exp 1) ^ 263 < (2.719 : ℝ) ^ 263 := by
            exact pow_lt_pow_left₀ hbase (by positivity) (by norm_num : (263 : ℕ) ≠ 0)
          simp_all
        have h1 : (2.719 : ℝ) ^ 121 < 193 ^ 23 := by norm_num
        have h2 : (2.719 : ℝ) ^ 142 < 193 ^ 27 := by norm_num
        have hnum : (2.719 : ℝ) ^ 263 < 193 ^ 50 := by
          rw [show (263 : ℕ) = 121 + 142 by norm_num, show (50 : ℕ) = 23 + 27 by norm_num]
          rw [pow_add, pow_add]
          exact mul_lt_mul'' h1 h2
            (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2.719) 121)
            (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2.719) 142)
        exact lt_trans h_exp_bound hnum
      contrapose! h_exp;
      exact le_trans (pow_le_pow_left₀ (by norm_num) h_exp 50)
        (by norm_num [← Real.exp_nat_mul]);
  rw [show (5 : ℝ) = 2 ^ 2 * 1.25 by norm_num, Real.log_mul,
    Real.log_pow] <;> norm_num at *;
  rw [show (7 : ℝ) = 2 ^ 2 * 1.75 by norm_num, Real.log_mul,
    Real.log_pow] <;> norm_num at *;
  have := Real.log_two_lt_d9;
  norm_num at *;
  linarith [Real.log_le_sub_one_of_pos (show 0 < 5 / 4 by norm_num),
    Real.log_le_sub_one_of_pos (show 0 < 7 / 4 by norm_num),
    Real.log_pos (show 1 < 5 / 4 by norm_num),
    Real.log_pos (show 1 < 7 / 4 by norm_num)]

theorem Phi_E₃_at_alpha : Phi 4 (2/7) (47/625 : ℝ) < -(1 : ℝ)/1000 := by
  have h_expr : Phi 4 (2/7) (47/625) =
    (-94/625) * Real.log (47/625)
    + (-921/4375) * Real.log (921/4375)
    + (2/7) * Real.log (2/7)
    + (-94/125) * Real.log (94/125)
    + (-578/625) * Real.log (578/625)
    + (658/625) * Real.log (658/625)
    + (2312/625) * Real.log (2312/625)
    + (-4) * Real.log 4 := by
    unfold Phi hEntropy; simp only [Real.log_one, mul_zero, zero_sub]; ring_nf
  rw [h_expr]
  nlinarith [log_lower_47_625, log_lower_921_4375, log_upper_2_7,
    log_lower_94_125, log_lower_578_625, log_upper_658_625,
    log_upper_2312_625, log_lower_4]

theorem Phi_E₄_at_delta : Phi 5 (5/11) (1/100 : ℝ) < -(1 : ℝ)/1000 := by
  unfold Phi hEntropy;
  norm_num [ Real.log_div ];
  rw [show (100 : ℝ) = 10 ^ 2 by norm_num,
    show (99 : ℝ) = 3 ^ 2 * 11 by norm_num,
    show (1100 : ℝ) = 10 ^ 2 * 11 by norm_num,
    show (489 : ℝ) = 3 * 163 by norm_num, Real.log_mul, Real.log_mul,
    Real.log_mul, Real.log_pow, Real.log_pow] <;> ring_nf <;> norm_num;
  rw [show (10 : ℝ) = 2 * 5 by norm_num,
    show (20 : ℝ) = 2 ^ 2 * 5 by norm_num,
    show (50 : ℝ) = 2 * 5 ^ 2 by norm_num, Real.log_mul, Real.log_mul,
    Real.log_mul, Real.log_pow, Real.log_pow]
      <;> ring_nf <;> norm_num;
  rw [ show ( 163 : ℝ ) = 2 ^ 7 * ( 163 / 128 ) by norm_num, Real.log_mul, Real.log_pow ] <;>
    ring_nf <;> norm_num;
  -- We'll use the fact that $\log(3) \approx 1.0986$, $\log(5) \approx 1.6094$, $\log(11) \approx
  -- 2.3979$, and $\log(163/128) \approx 0.2412$.
  have h_approx :
      Real.log 3 < 1.1 ∧ Real.log 5 > 1.6 ∧ Real.log 11 < 2.4 ∧
        Real.log (163 / 128) > 0.24 := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num [ Real.log_lt_iff_lt_exp, Real.lt_log_iff_exp_lt ];
    · -- We can raise both sides to the power of 10 to remove the fraction.
      suffices h_exp : (3 : ℝ) ^ 10 < Real.exp 11 by
        contrapose! h_exp;
        convert pow_le_pow_left₀ (by positivity) h_exp 10 using 1;
        norm_num [← Real.exp_nat_mul];
      have := Real.exp_one_gt_d9.le;
      norm_num at *;
      rw [show Real.exp 11 = (Real.exp 1) ^ 11 by
        rw [← Real.exp_nat_mul]; norm_num];
      exact lt_of_lt_of_le (by norm_num)
        (pow_le_pow_left₀ (by positivity) this _);
    · -- We can raise both sides to the power of 5 to get $e^8 < 5^5$.
      have h_exp_8 : Real.exp 8 < 5 ^ 5 := by
        have := Real.exp_one_lt_d9.le;
        norm_num at *;
        rw [show Real.exp 8 = (Real.exp 1) ^ 8 by
          rw [← Real.exp_nat_mul]; norm_num];
        exact lt_of_le_of_lt (pow_le_pow_left₀ (by positivity) this _)
          (by norm_num);
      contrapose! h_exp_8;
      exact le_trans (pow_le_pow_left₀ (by norm_num) h_exp_8 5)
        (by norm_num [← Real.exp_nat_mul]);
    · -- We can raise both sides to the power of 5 to get $11^5 < e^{12}$.
      have h_exp : (11 : ℝ)^5 < Real.exp 12 := by
        have := Real.exp_one_gt_d9.le;
        norm_num at *;
        rw [show Real.exp 12 = (Real.exp 1) ^ 12 by
          rw [← Real.exp_nat_mul]; norm_num];
        exact lt_of_lt_of_le (by norm_num)
          (pow_le_pow_left₀ (by positivity) this _);
      contrapose! h_exp;
      exact le_trans ( by norm_num [ ← Real.exp_nat_mul ] ) ( pow_le_pow_left₀ ( by positivity )
        h_exp 5 );
    · rw [ ← Real.log_lt_log_iff ( by positivity ) ( by positivity ), Real.log_exp ];
      rw [ div_lt_iff₀' ] <;> norm_num [ ← Real.log_rpow, Real.lt_log_iff_exp_lt ];
      have := Real.exp_one_lt_d9.le;
      norm_num1 at *;
      rw [show Real.exp 6 = (Real.exp 1) ^ 6 by
        rw [← Real.exp_nat_mul]; norm_num];
      exact lt_of_le_of_lt (pow_le_pow_left₀ (by positivity) this _) (by norm_num);
  have := Real.log_two_gt_d9; norm_num at *; linarith

theorem Phi_E₄_at_alpha : Phi 5 (5/11) (329/1250 : ℝ) < -(1 : ℝ)/1000 := by
  have h_expr : Phi 5 (5/11) (329/1250) =
    (-2631/13750) * Real.log (2631/13750)
    + (-329/625) * Real.log (329/1250)
    + (5/11) * Real.log (5/11)
    + (-921/1250) * Real.log (921/1250)
    + (-987/625) * Real.log (987/625)
    + (3619/1250) * Real.log (3619/1250)
    + (921/250) * Real.log (921/250)
    + (-5) * Real.log 5 := by
    unfold Phi hEntropy; simp only [Real.log_one, mul_zero, zero_sub]; ring_nf
  rw [h_expr]
  nlinarith [log_lower_2631_13750, log_lower_329_1250, log_upper_5_11,
    log_lower_921_1250, log_lower_987_625, log_upper_3619_1250,
    log_upper_921_250, log_lower_5]
end KaltonRoberts
