/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

import LeanPool.Zeta5Irrational.Growth.Assembly1
import Mathlib.Analysis.Complex.ExponentialBounds
public import LeanPool.Zeta5Irrational.Growth.Assembly4
public import LeanPool.Zeta5Irrational.Constants
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Ring.Basic

/-! # Growth of the normaliser (Proposition 5.2, in the form needed here)

`log m_K ≤ (A_eff + ε) K²` for all large `K`, with `A_eff = 1.36 < -U`.

The bound assembles the four prime ranges:

* small primes `p ≤ K/400`: `(6λ/400)K²` by
the prime number theorem;
* `K/400 < p ≤ K/20`: the tail bound, `≤ -0.05346 K²`;
* `K/20 < p ≤ K/3`: the exact table, `(5.18) K² = 0.04279 K²`;
* `K/3 < p ≤ 2h`: the outer table, `129101/96000 K² = 1.34480 K²`;

total `≈ 1.3480 K² + o(K²)`.
-/

public section

open Filter Finset

namespace Zeta5Irrational

/-- The lower-order terms are `o(K²)`. -/
lemma low_order {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop,
      6 * (37 * (n : ℝ)) * ((Real.sqrt (200 * n) + 1) * Real.log (200 * n)) + 3 * 10 ^ 9 * n ≤
        δ * Kr n ^ 2 := by
  set A : ℝ := (1776 + 3 * 10 ^ 9) / (8 * δ) + 1 with hA
  have hy : Tendsto (fun n : ℕ => (200 * (n : ℝ)) ^ ((1 : ℝ) / 4)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp
      ((tendsto_natCast_atTop_atTop).const_mul_atTop (by norm_num))
  filter_upwards [hy.eventually_ge_atTop A, eventually_ge_atTop 1] with n hs hn
  set s := (200 * (n : ℝ)) ^ ((1 : ℝ) / 4) with hsdef
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hy0 : (0 : ℝ) ≤ 200 * n := by positivity
  have hA1 : 1 ≤ A := by
    rw [hA]; have : 0 ≤ (1776 + 3 * 10 ^ 9) / (8 * δ) := by positivity
    linarith
  have hs1 : 1 ≤ s := le_trans hA1 hs
  have hs4 : s ^ 4 = 200 * n := by rw [hsdef, ← Real.rpow_natCast, ← Real.rpow_mul hy0]; norm_num
  have hsqrt : Real.sqrt (200 * n) = s ^ 2 := by
    rw [← hs4, show s ^ 4 = (s ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  have hlog : Real.log (200 * n) ≤ 4 * s := by
    rw [← hs4, Real.log_pow]
    have := Real.log_le_sub_one_of_pos (show 0 < s by linarith)
    push_cast; linarith
  have hlog0 : 0 ≤ Real.log (200 * n) := Real.log_nonneg (by linarith)
  rw [hsqrt]
  have h1 : (s ^ 2 + 1) * Real.log (200 * n) ≤ 8 * s ^ 3 := by
    have := mul_le_mul_of_nonneg_left hlog (show (0 : ℝ) ≤ s ^ 2 + 1 by positivity)
    nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hs1 2]
  have hKr : Kr n ^ 2 = 8 * s ^ 4 * n := by simp only [Kr]; rw [hs4]; ring
  rw [hKr]
  have hs3 : 1 ≤ s ^ 3 := one_le_pow₀ hs1
  have hkey : 1776 * s ^ 3 + 3 * 10 ^ 9 ≤ 8 * δ * s ^ 4 := by
    have hAs : (1776 + 3 * 10 ^ 9) / (8 * δ) ≤ s := by linarith
    have : 1776 + 3 * 10 ^ 9 ≤ 8 * δ * s := by rw [div_le_iff₀ (by positivity)] at hAs; linarith
    nlinarith [mul_le_mul_of_nonneg_right this (show (0 : ℝ) ≤ s ^ 3 by positivity)]
  have hn0 : (0 : ℝ) ≤ n := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h1 (show (0 : ℝ) ≤ 6 * (37 * n) by positivity),
    mul_le_mul_of_nonneg_left hkey hn0]

lemma theta_le_two (y : ℝ) (hy : 0 ≤ y) : Chebyshev.theta y ≤ 2 * y := by
  have h := Chebyshev.theta_le_log4_mul_x hy
  have : Real.log 4 < 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    have := Real.log_two_lt_d9; push_cast; linarith
  nlinarith

/-- **Growth of the normaliser.** -/
theorem growth_mN :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, Real.log (mN n) ≤ ((Aeff : ℝ) + ε) * Kr n ^ 2 := by
  intro ε hε
  set δ : ℝ := min (ε / 20) (1 / 10000) with hδdef
  have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
  have hδ1 : δ ≤ ε / 20 := min_le_left _ _
  have hδ2 : δ ≤ 1 / 10000 := min_le_right _ _
  have hKr : Tendsto Kr atTop atTop :=
    (tendsto_natCast_atTop_atTop).const_mul_atTop (by norm_num : (0 : ℝ) < 40)
  have hy10 : Tendsto (fun n : ℕ => ((n / 10 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (Nat.tendsto_div_const_atTop (by norm_num))
  have Eθ := hy10.eventually (theta_eventually_close hδ)
  filter_upwards [hKr.eventually (tail_psum_limit hδ), hKr.eventually (inner_psum_limit hδ),
    hKr.eventually (outer_psum_limit hδ), Eθ, low_order hδ, eventually_ge_atTop 10400] with n h2
    h3 h4 hθ hlow hn
  have hK0 : 0 < Kr n ^ 2 := by
    simp only [Kr]; have : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
    positivity
  rw [div_le_iff₀ hK0] at h2 h3 h4
  have hK : Kr n ^ 2 = 1600 * (n : ℝ) ^ 2 := by simp only [Kr]; ring
  rw [log_mN,
    sum_split4 _ (a := n / 10) (b := 2 * n) (c := 40 * n / 3) (N := 2 * (37 * n)) (by omega)
      (by omega) (by omega)]
  have r1 := small_range_le n (by omega)
  have r2 := range2_le hn
  have r3 := range3_le hn
  have r4 :=
    range4_le
      hn
        -- the `θ` terms
  have hθ1 : Chebyshev.theta ((n / 10 : ℕ) : ℝ) ≤ (1 + δ) * (n / 10 : ℝ) := by
    have h10 : ((n / 10 : ℕ) : ℝ) ≤ (n : ℝ) / 10 := by
      rw [le_div_iff₀ (by norm_num)];
      exact_mod_cast (Nat.div_mul_le_self n 10)
    have := (abs_le.mp hθ).2
    nlinarith
  have t2 := theta_le_two ((2 * n : ℕ) : ℝ) (by positivity)
  have t3 := theta_le_two ((40 * n / 3 : ℕ) : ℝ) (by positivity)
  have t4 := theta_le_two ((2 * (37 * n) : ℕ) : ℝ) (by positivity)
  have hn3 : ((40 * n / 3 : ℕ) : ℝ) ≤ 40 * n / 3 := by
    rw [le_div_iff₀ (by norm_num)];
    exact_mod_cast (Nat.div_mul_le_self (40 * n) 3)
  push_cast at t2 t4 r1 r2 r4
  have hA : (Aeff : ℝ) = 136 / 100 := by unfold Aeff; norm_num
  rw [hA]
  have hn0 : (0 : ℝ) ≤ n := by
    positivity
      -- the main terms
  have hmain : 6 * (37 * (n : ℝ)) * ((1 + δ) * (n / 10)) = 22.2 * (1 + δ) / 1600 * Kr n ^ 2 := by
    rw [hK]; ring
  have hsum :
    -6843153 / 128000000 + 322437603634266857629 / 7535670527041937280000 + 129101 / 96000 +
        22.2 / 1600 <
      (136 / 100 : ℝ) - 1 / 1000 :=
    by norm_num
  have i1 := mul_le_mul_of_nonneg_left hθ1 (show (0 : ℝ) ≤ 6 * (37 * n) by positivity)
  have i2 := mul_le_mul_of_nonneg_left hδ2 hK0.le
  have i3 := mul_le_mul_of_nonneg_left hδ1 hK0.le
  have i4 : (10 : ℝ) ^ 8 * Chebyshev.theta ((40 * n / 3 : ℕ) : ℝ) ≤ 10 ^ 8 * (2 * (40 * n / 3)) :=
    by have := t3.trans (mul_le_mul_of_nonneg_left hn3 (by norm_num)); linarith
  have hε0 : 0 ≤ ε * Kr n ^ 2 := by positivity
  linarith

end Zeta5Irrational
