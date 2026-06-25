/-
Copyright (c) 2026 Zhihao Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Guo, freezed-corpse-143
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Real inequalities for moment growth

Verified Wikipedia references:
* Exponential function: https://en.wikipedia.org/wiki/Exponential_function
* Gaussian function: https://en.wikipedia.org/wiki/Gaussian_function

Note: real-analysis background is available at
https://en.wikipedia.org/wiki/Real_analysis, but the formulas below are
specifically exponential/Gaussian-tail envelope inequalities.

This file contains small deterministic real-analysis helpers used by the
concentration moment layer.  It deliberately avoids probability assumptions.
-/

namespace HighDimProb

/-- Scalar exponential chord bound on `[0, sigma]`.

This is the one-dimensional convexity helper used before matrix/eigenvalue
bookkeeping: it keeps the downstream `0 <= c` assumption in the signature even
though convexity of `exp` proves the inequality for arbitrary `c`. -/
theorem exp_mul_le_chord_exp_of_nonneg_of_le
    {c x sigma : Real}
    (_hc : 0 <= c) (hx0 : 0 <= x) (hxsigma : x <= sigma) (hsigma : 0 < sigma) :
    Real.exp (c * x) <=
      1 + (x / sigma) * (Real.exp (c * sigma) - 1) := by
  let t : Real := x / sigma
  have ht0 : 0 <= t := by
    dsimp [t]
    exact div_nonneg hx0 hsigma.le
  have ht1 : t <= 1 := by
    dsimp [t]
    exact (div_le_one hsigma).mpr hxsigma
  have hsum : 1 - t + t = 1 := by ring
  have hconv :=
    convexOn_exp.2 (Set.mem_univ (0 : Real)) (Set.mem_univ (c * sigma))
      (sub_nonneg.mpr ht1) ht0 hsum
  simp only [smul_eq_mul, Real.exp_zero] at hconv
  have harg : (1 - t) * 0 + t * (c * sigma) = c * x := by
    dsimp [t]
    field_simp [hsigma.ne']
    ring
  have hrhs :
      (1 - t) * 1 + t * Real.exp (c * sigma) =
        1 + t * (Real.exp (c * sigma) - 1) := by
    ring
  rw [harg, hrhs] at hconv
  exact hconv

/-- A convenient elementary bound used to dominate powers by Gaussian tails. -/
lemma log_le_sq_of_nonneg {y : ℝ} (hy : 0 ≤ y) :
    Real.log y ≤ y ^ 2 := by
  by_cases hy0 : y = 0
  · simp [hy0]
  · have hpos : 0 < y := lt_of_le_of_ne hy (Ne.symm hy0)
    by_cases hle : y ≤ 1
    · have hlog_nonpos : Real.log y ≤ 0 := by
        rw [← Real.exp_le_exp, Real.exp_log hpos, Real.exp_zero]
        exact hle
      exact hlog_nonpos.trans (sq_nonneg y)
    · have hge : 1 ≤ y := le_of_lt (lt_of_not_ge hle)
      have hysq : y ≤ y ^ 2 := by
        have hmul : y * 1 ≤ y * y := mul_le_mul_of_nonneg_left hge hy
        simpa [pow_two] using hmul
      exact (Real.log_le_self hy).trans hysq

/-- Powers are dominated by a Gaussian exponential envelope. -/
lemma pow_le_exp_nat_mul_sq {y : ℝ} (hy : 0 ≤ y) (q : ℕ) :
    y ^ q ≤ Real.exp ((q : ℝ) * y ^ 2) := by
  by_cases hy0 : y = 0
  · subst y
    cases q with
    | zero => simp
    | succ q => simp
  · have hpos : 0 < y := lt_of_le_of_ne hy (Ne.symm hy0)
    have hlog : Real.log (y ^ q) ≤ (q : ℝ) * y ^ 2 := by
      rw [Real.log_pow]
      exact mul_le_mul_of_nonneg_left (log_le_sq_of_nonneg hy) (Nat.cast_nonneg q)
    rwa [Real.log_le_iff_le_exp (pow_pos hpos q)] at hlog

/--
Deterministic sharp-growth envelope for natural powers.

The constant `2` is the main helper; a constant-`4` compatibility wrapper is
provided below for theorem statements that use a looser envelope.
-/
theorem pow_le_two_sqrt_mul_exp_sq {x : ℝ} (hx : 0 ≤ x)
    {q : ℕ} (hq : 1 ≤ q) :
    x ^ q ≤ (2 * Real.sqrt (q : ℝ)) ^ q * Real.exp (x ^ 2 / 4) := by
  have hqposNat : 0 < q := lt_of_lt_of_le Nat.zero_lt_one hq
  have hqpos : 0 < (q : ℝ) := by exact_mod_cast hqposNat
  have hdenpos : 0 < 2 * Real.sqrt (q : ℝ) := by positivity
  have hy_nonneg : 0 ≤ x / (2 * Real.sqrt (q : ℝ)) :=
    div_nonneg hx hdenpos.le
  have hcore := pow_le_exp_nat_mul_sq hy_nonneg q
  have harg :
      (q : ℝ) * (x / (2 * Real.sqrt (q : ℝ))) ^ 2 = x ^ 2 / 4 := by
    field_simp [hdenpos.ne', hqpos.ne']
    rw [Real.sq_sqrt hqpos.le]
    ring
  calc
    x ^ q = (2 * Real.sqrt (q : ℝ) * (x / (2 * Real.sqrt (q : ℝ)))) ^ q := by
      field_simp [hdenpos.ne']
    _ = (2 * Real.sqrt (q : ℝ)) ^ q *
          (x / (2 * Real.sqrt (q : ℝ))) ^ q := by
      rw [mul_pow]
    _ ≤ (2 * Real.sqrt (q : ℝ)) ^ q *
          Real.exp ((q : ℝ) * (x / (2 * Real.sqrt (q : ℝ))) ^ 2) := by
      exact mul_le_mul_of_nonneg_left hcore (pow_nonneg hdenpos.le q)
    _ = (2 * Real.sqrt (q : ℝ)) ^ q * Real.exp (x ^ 2 / 4) := by
      rw [harg]

/-- Scaled version of `pow_le_two_sqrt_mul_exp_sq`. -/
theorem pow_le_two_mul_scale_sqrt_mul_exp_sq_div_four
    {x K : ℝ} (hx : 0 ≤ x) (hK : 0 < K) {q : ℕ} (hq : 1 ≤ q) :
    x ^ q ≤ (2 * K * Real.sqrt (q : ℝ)) ^ q *
      Real.exp ((x / K) ^ 2 / 4) := by
  have hdiv_nonneg : 0 ≤ x / K := div_nonneg hx hK.le
  have h := pow_le_two_sqrt_mul_exp_sq (x := x / K) hdiv_nonneg (q := q) hq
  have hKpow_nonneg : 0 ≤ K ^ q := pow_nonneg hK.le q
  have hmul := mul_le_mul_of_nonneg_left h hKpow_nonneg
  calc
    x ^ q = K ^ q * (x / K) ^ q := by
      rw [div_pow]
      field_simp [pow_ne_zero q hK.ne']
    _ ≤ K ^ q * ((2 * Real.sqrt (q : ℝ)) ^ q *
          Real.exp ((x / K) ^ 2 / 4)) := hmul
    _ = (2 * K * Real.sqrt (q : ℝ)) ^ q *
          Real.exp ((x / K) ^ 2 / 4) := by
      rw [mul_pow]
      ring

/-- A looser scaled envelope with the full exponential-square term. -/
theorem pow_le_two_mul_scale_sqrt_mul_exp_sq_div
    {x K : ℝ} (hx : 0 ≤ x) (hK : 0 < K) {q : ℕ} (hq : 1 ≤ q) :
    x ^ q ≤ (2 * K * Real.sqrt (q : ℝ)) ^ q *
      Real.exp ((x / K) ^ 2) := by
  have hbase_nonneg : 0 ≤ (2 * K * Real.sqrt (q : ℝ)) ^ q := by positivity
  have hsq_nonneg : 0 ≤ (x / K) ^ 2 := sq_nonneg (x / K)
  have hquarter_le : (x / K) ^ 2 / 4 ≤ (x / K) ^ 2 := by nlinarith
  exact (pow_le_two_mul_scale_sqrt_mul_exp_sq_div_four hx hK hq).trans
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp_of_le hquarter_le) hbase_nonneg)

private lemma two_le_two_pow_succ (n : ℕ) :
    (2 : ℝ) ≤ 2 ^ (n + 1) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      have hpow_nonneg : 0 ≤ (2 : ℝ) ^ (n + 1) := by positivity
      calc
        (2 : ℝ) ≤ 2 ^ (n + 1) := ih
        _ ≤ 2 ^ (n + 1) * 2 := by nlinarith
        _ = 2 ^ (Nat.succ n + 1) := by
          rw [show Nat.succ n + 1 = Nat.succ (n + 1) by omega]
          exact (pow_succ (2 : ℝ) (n + 1)).symm

private lemma two_le_two_pow (q : ℕ) (hq : 1 ≤ q) :
    (2 : ℝ) ≤ 2 ^ q := by
  cases q with
  | zero => cases hq
  | succ n =>
      simpa [Nat.succ_eq_add_one] using two_le_two_pow_succ n

/-- Absorb a leading factor `2` by doubling the base of a nonzero natural power. -/
lemma two_mul_pow_le_two_mul_pow {a : ℝ} (ha : 0 ≤ a)
    {q : ℕ} (hq : 1 ≤ q) :
    2 * a ^ q ≤ (2 * a) ^ q := by
  calc
    2 * a ^ q ≤ 2 ^ q * a ^ q := by
      exact mul_le_mul_of_nonneg_right (two_le_two_pow q hq) (pow_nonneg ha q)
    _ = (2 * a) ^ q := by
      rw [mul_pow]

/-- Constant-`4` compatibility wrapper for the deterministic envelope. -/
theorem pow_le_four_sqrt_mul_exp_sq {x : ℝ} (hx : 0 ≤ x)
    {q : ℕ} (hq : 1 ≤ q) :
    x ^ q ≤ (4 * Real.sqrt (q : ℝ)) ^ q * Real.exp (x ^ 2 / 4) := by
  have h := pow_le_two_sqrt_mul_exp_sq (x := x) hx (q := q) hq
  have hleft_nonneg : 0 ≤ (2 * Real.sqrt (q : ℝ)) ^ q := by positivity
  have hsqrt_nonneg : 0 ≤ Real.sqrt (q : ℝ) := Real.sqrt_nonneg _
  have hbase : 2 * Real.sqrt (q : ℝ) ≤ 4 * Real.sqrt (q : ℝ) := by
    nlinarith
  have hpow :
      (2 * Real.sqrt (q : ℝ)) ^ q ≤ (4 * Real.sqrt (q : ℝ)) ^ q := by
    exact pow_le_pow_left₀ (by positivity) hbase q
  exact h.trans
    (mul_le_mul_of_nonneg_right hpow (Real.exp_pos (x ^ 2 / 4)).le)

/-! ## Bounded scalar Bernstein exponential inequality

The deterministic scalar inequality behind the matrix Bernstein
functional-calculus step.  It is purely real analysis and carries no
probability or matrix content. -/

open scoped Nat

/-- Elementary factorial lower bound `2 * 3 ^ n ≤ (n + 2)!`.

This is the comparison that turns the exponential tail series into a geometric
series with ratio `|u| / 3`. -/
private lemma two_mul_three_pow_le_factorial_add_two (n : ℕ) :
    2 * 3 ^ n ≤ (n + 2)! := by
  induction n with
  | zero => decide
  | succ k ih =>
    have hfac : (k + 1 + 2)! = (k + 3) * (k + 2)! := by
      have hidx : k + 1 + 2 = (k + 2) + 1 := by ring
      rw [hidx, Nat.factorial_succ]
    calc
      2 * 3 ^ (k + 1) = 3 * (2 * 3 ^ k) := by ring
      _ ≤ 3 * (k + 2)! := Nat.mul_le_mul (le_refl 3) ih
      _ ≤ (k + 3) * (k + 2)! := Nat.mul_le_mul (by omega) (le_refl _)
      _ = (k + 1 + 2)! := hfac.symm

/-- Bounded scalar Bernstein exponential inequality.

For a real number `u` with `|u| ≤ b` and `b < 3`,
`exp u ≤ 1 + u + (u ^ 2 / 2) / (1 - b / 3)`.

The constant `(1 / 2) / (1 - b / 3)` is the canonical bounded-Bernstein
moment-generating-function coefficient. -/
theorem exp_le_one_add_add_half_sq_div_one_sub_third {u b : ℝ}
    (hub : |u| ≤ b) (hb : b < 3) :
    Real.exp u ≤ 1 + u + (u ^ 2 / 2) / (1 - b / 3) := by
  have hu3 : |u| < 3 := lt_of_le_of_lt hub hb
  set r : ℝ := |u| / 3 with hr
  have hr0 : 0 ≤ r := by rw [hr]; positivity
  have hr1 : r < 1 := by
    rw [hr, div_lt_one (by norm_num)]; exact hu3
  have hden_b : 0 < 1 - b / 3 := by linarith
  have hden_u : 0 < 1 - r := by linarith
  -- exponential series
  have hsum : Summable (fun n : ℕ => u ^ n / (n ! : ℝ)) :=
    Real.summable_pow_div_factorial u
  have hexp : Real.exp u = ∑' n : ℕ, u ^ n / (n ! : ℝ) := by
    rw [Real.exp_eq_exp_ℝ]
    exact congrFun NormedSpace.exp_eq_tsum_div u
  -- split off the first two terms
  have hsplit :
      (∑ i ∈ Finset.range 2, u ^ i / (i ! : ℝ)) +
          ∑' i : ℕ, u ^ (i + 2) / ((i + 2)! : ℝ) =
        ∑' i : ℕ, u ^ i / (i ! : ℝ) :=
    hsum.sum_add_tsum_nat_add 2
  have hprefix :
      (∑ i ∈ Finset.range 2, u ^ i / (i ! : ℝ)) = 1 + u := by
    simp [Finset.sum_range_succ, Nat.factorial]
  -- summabilities
  have htail_sum : Summable (fun i : ℕ => u ^ (i + 2) / ((i + 2)! : ℝ)) :=
    (summable_nat_add_iff 2).2 hsum
  have hg_sum : Summable (fun n : ℕ => (u ^ 2 / 2) * r ^ n) :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left _
  -- termwise geometric domination
  have hterm : ∀ i : ℕ,
      u ^ (i + 2) / ((i + 2)! : ℝ) ≤ (u ^ 2 / 2) * r ^ i := by
    intro i
    have hfac_pos : (0 : ℝ) < ((i + 2)! : ℝ) := by
      exact_mod_cast (i + 2).factorial_pos
    have h2pos : (0 : ℝ) < 2 * 3 ^ i := by positivity
    have hfac_ge : (2 : ℝ) * 3 ^ i ≤ ((i + 2)! : ℝ) := by
      exact_mod_cast two_mul_three_pow_le_factorial_add_two i
    have hpow_le : u ^ (i + 2) ≤ |u| ^ (i + 2) := by
      calc
        u ^ (i + 2) ≤ |u ^ (i + 2)| := le_abs_self _
        _ = |u| ^ (i + 2) := abs_pow u (i + 2)
    have heq : |u| ^ (i + 2) / ((2 : ℝ) * 3 ^ i) = (u ^ 2 / 2) * r ^ i := by
      rw [hr, div_pow, ← sq_abs u, pow_add]
      ring
    have step1 :
        u ^ (i + 2) / ((i + 2)! : ℝ) ≤ |u| ^ (i + 2) / ((i + 2)! : ℝ) :=
      (div_le_div_iff_of_pos_right hfac_pos).mpr hpow_le
    have step2 :
        |u| ^ (i + 2) / ((i + 2)! : ℝ) ≤ |u| ^ (i + 2) / ((2 : ℝ) * 3 ^ i) := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left
        ((inv_le_inv₀ hfac_pos h2pos).mpr hfac_ge)
        (pow_nonneg (abs_nonneg u) _)
    calc
      u ^ (i + 2) / ((i + 2)! : ℝ)
          ≤ |u| ^ (i + 2) / ((i + 2)! : ℝ) := step1
      _ ≤ |u| ^ (i + 2) / ((2 : ℝ) * 3 ^ i) := step2
      _ = (u ^ 2 / 2) * r ^ i := heq
  -- bound the tail by the geometric sum
  have htail_le :
      (∑' i : ℕ, u ^ (i + 2) / ((i + 2)! : ℝ)) ≤
        ∑' n : ℕ, (u ^ 2 / 2) * r ^ n :=
    htail_sum.tsum_le_tsum hterm hg_sum
  have hgeom : (∑' n : ℕ, (u ^ 2 / 2) * r ^ n) = (u ^ 2 / 2) * (1 - r)⁻¹ := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
  have hrb : 1 - b / 3 ≤ 1 - r := by rw [hr]; linarith
  have hfrac : (u ^ 2 / 2) * (1 - r)⁻¹ ≤ (u ^ 2 / 2) / (1 - b / 3) := by
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left
      ((inv_le_inv₀ hden_u hden_b).mpr hrb) (by positivity)
  have htail_bound :
      (∑' i : ℕ, u ^ (i + 2) / ((i + 2)! : ℝ)) ≤ (u ^ 2 / 2) / (1 - b / 3) :=
    htail_le.trans (by rw [hgeom]; exact hfrac)
  calc
    Real.exp u
        = (∑ i ∈ Finset.range 2, u ^ i / (i ! : ℝ)) +
            ∑' i : ℕ, u ^ (i + 2) / ((i + 2)! : ℝ) := by
          rw [hexp]; exact hsplit.symm
    _ = 1 + u + ∑' i : ℕ, u ^ (i + 2) / ((i + 2)! : ℝ) := by rw [hprefix]
    _ ≤ 1 + u + (u ^ 2 / 2) / (1 - b / 3) := by linarith [htail_bound]

end HighDimProb
