/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

public import LeanPool.Zeta5Irrational.HermiteIntegrals
import LeanPool.Zeta5Irrational.Moments
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.RingNF

import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! # Four integrations by parts: `∫₀^∞ g F₄ = ∫₀^∞ g₄ F₀`

Uniform bounds `|F_m(y)| ≤ c_m (1+2πy)^{m+1} / (2π y^{m+1} e^{2πy})` and `|g_j(y)| ≤ c_j y^{5-j}/a²`
give integrability of the products and vanishing boundary terms at `0⁺` and `∞`.
-/

public section

open Filter Topology Set MeasureTheory

namespace Zeta5Irrational

/-! ### Bounds for `F_m` -/

lemma qe_sub_one_ge {y : ℝ} : 2 * Real.pi * y ≤ qe y - 1 := by
  unfold qe;
  linarith [Real.add_one_le_exp (2 * Real.pi * y)]

lemma one_div_qe_sub_one_le {y : ℝ} (hy : 0 < y) :
    1 / (qe y - 1) ≤ (1 + 2 * Real.pi * y) / (2 * Real.pi * y * qe y) := by
  have hq := qe_gt_one hy
  have h := qe_sub_one_ge (y := y)
  rw [div_le_div_iff₀ (by linarith) (by positivity)]
  nlinarith [qe_pos y]

/-- Generic estimate `N / (q-1)^(m+1) ≤ c (1+2πy)^(m+1) / (2π y^(m+1) q)` when
`N ≤ (2π)^m c q^m`. -/
lemma F_bound_aux {y : ℝ} (hy : 0 < y) (m : ℕ) {N c : ℝ} (hN : 0 ≤ N)
    (hNc : N ≤ (2 * Real.pi) ^ m * c * qe y ^ m) :
    N / (qe y - 1) ^ (m + 1) ≤
      c * (1 + 2 * Real.pi * y) ^ (m + 1) / (2 * Real.pi * y ^ (m + 1) * qe y) := by
  have hq := qe_gt_one hy
  have hq0 := qe_pos y
  have h1 :
    1 / (qe y - 1) ^ (m + 1) ≤ ((1 + 2 * Real.pi * y) / (2 * Real.pi * y * qe y)) ^ (m + 1) := by
    rw [one_div, ← inv_pow, ← one_div]
    exact pow_le_pow_left₀ (by positivity) (one_div_qe_sub_one_le hy) _
  calc
    N / (qe y - 1) ^ (m + 1) = N * (1 / (qe y - 1) ^ (m + 1)) := by ring
    _ ≤
        ((2 * Real.pi) ^ m * c * qe y ^ m) *
          ((1 + 2 * Real.pi * y) / (2 * Real.pi * y * qe y)) ^ (m + 1) :=
      (mul_le_mul hNc h1 (by positivity)
        (by
          have : 0 ≤ N := hN
          exact le_trans this hNc))
    _ = c * (1 + 2 * Real.pi * y) ^ (m + 1) / (2 * Real.pi * y ^ (m + 1) * qe y) := by
      have h2pi : (2 * Real.pi) ≠ 0 := by positivity
      have hqne : qe y ≠ 0 := hq0.ne'
      rw [div_pow, mul_pow (2 * Real.pi * y) (qe y), mul_pow (2 * Real.pi) y,
        pow_succ (2 * Real.pi), pow_succ (qe y), pow_succ y]
      field_simp
      try ring

lemma abs_F0_le {y : ℝ} (hy : 0 < y) :
    |F0 y| ≤ 1 * (1 + 2 * Real.pi * y) ^ (0 + 1) / (2 * Real.pi * y ^ (0 + 1) * qe y) := by
  have hq := qe_gt_one hy
  rw [F0, abs_of_pos (by positivity)]
  have := F_bound_aux hy 0 (N := 1) (c := 1) (by norm_num) (by simp)
  simpa using this

lemma abs_F1_le {y : ℝ} (hy : 0 < y) :
    |F1 y| ≤ 1 * (1 + 2 * Real.pi * y) ^ (1 + 1) / (2 * Real.pi * y ^ (1 + 1) * qe y) := by
  have hq := qe_gt_one hy
  have hq0 := qe_pos y
  have : F1 y = -((2 * Real.pi) * qe y / (qe y - 1) ^ 2) := by unfold F1; ring
  rw [this, abs_neg, abs_of_pos (by positivity)]
  exact F_bound_aux hy 1 (by positivity) (by ring_nf; rfl)

lemma abs_F2_le {y : ℝ} (hy : 0 < y) :
    |F2 y| ≤ 2 * (1 + 2 * Real.pi * y) ^ (2 + 1) / (2 * Real.pi * y ^ (2 + 1) * qe y) := by
  have hq := qe_gt_one hy
  have hq0 := qe_pos y
  rw [F2, abs_of_pos (by positivity)]
  refine F_bound_aux hy 2 (by positivity) ?_
  have h1 : qe y + 1 ≤ 2 * qe y := by linarith
  calc
    (2 * Real.pi) ^ 2 * qe y * (qe y + 1) ≤ (2 * Real.pi) ^ 2 * qe y * (2 * qe y) := by gcongr
    _ = (2 * Real.pi) ^ 2 * 2 * qe y ^ 2 := by ring

lemma abs_F3_le {y : ℝ} (hy : 0 < y) :
    |F3 y| ≤ 6 * (1 + 2 * Real.pi * y) ^ (3 + 1) / (2 * Real.pi * y ^ (3 + 1) * qe y) := by
  have hq := qe_gt_one hy
  have hq0 := qe_pos y
  have : F3 y = -((2 * Real.pi) ^ 3 * qe y * (qe y ^ 2 + 4 * qe y + 1) / (qe y - 1) ^ 4) := by
    unfold F3; ring
  rw [this, abs_neg, abs_of_pos (by positivity)]
  refine F_bound_aux hy 3 (by positivity) ?_
  have h1 : qe y ^ 2 + 4 * qe y + 1 ≤ 6 * qe y ^ 2 := by nlinarith
  calc
    (2 * Real.pi) ^ 3 * qe y * (qe y ^ 2 + 4 * qe y + 1) ≤
        (2 * Real.pi) ^ 3 * qe y * (6 * qe y ^ 2) :=
      by gcongr
    _ = (2 * Real.pi) ^ 3 * 6 * qe y ^ 3 := by ring

lemma abs_F4_le {y : ℝ} (hy : 0 < y) :
    |F4 y| ≤ 24 * (1 + 2 * Real.pi * y) ^ (4 + 1) / (2 * Real.pi * y ^ (4 + 1) * qe y) := by
  have hq := qe_gt_one hy
  have hq0 := qe_pos y
  rw [F4, abs_of_pos (by positivity)]
  refine F_bound_aux hy 4 (by positivity) ?_
  have h1 : qe y ^ 3 + 11 * qe y ^ 2 + 11 * qe y + 1 ≤ 24 * qe y ^ 3 := by
    nlinarith [sq_nonneg (qe y), mul_pos hq0 hq0]
  calc
    (2 * Real.pi) ^ 4 * qe y * (qe y ^ 3 + 11 * qe y ^ 2 + 11 * qe y + 1) ≤
        (2 * Real.pi) ^ 4 * qe y * (24 * qe y ^ 3) :=
      by gcongr
    _ = (2 * Real.pi) ^ 4 * 24 * qe y ^ 4 := by ring

/-! ### Bounds for `g_j` -/

lemma abs_g0_le {a : ℝ} (ha : 0 < a) {y : ℝ} (hy : 0 ≤ y) : |g0 a y| ≤ 1 / 12 * y ^ 5 / a ^ 2 := by
  unfold g0
  rw [abs_of_nonneg (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [pow_nonneg hy 5, sq_nonneg y, mul_nonneg (pow_nonneg hy 5) (sq_nonneg y)]

lemma abs_g1_le {a : ℝ} (ha : 0 < a) {y : ℝ} (_hy : 0 ≤ y) : |g1 a y| ≤ 5 / 12 * y ^ 4 / a ^ 2 := by
  unfold g1
  rw [abs_of_nonneg (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
  have h4 : 0 ≤ y ^ 4 := by positivity
  nlinarith [mul_nonneg h4 (sq_nonneg y), mul_nonneg (mul_nonneg h4 (sq_nonneg y)) (sq_nonneg y),
    mul_nonneg (mul_nonneg h4 (sq_nonneg y)) (sq_nonneg a), mul_nonneg h4 (sq_nonneg a),
    mul_nonneg (mul_nonneg h4 (sq_nonneg a)) (sq_nonneg a)]

lemma abs_g2_le {a : ℝ} (ha : 0 < a) {y : ℝ} (hy : 0 ≤ y) : |g2 a y| ≤ 10 / 6 * y ^ 3 / a ^ 2 := by
  unfold g2
  rw [abs_of_nonneg (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
  have h3 : 0 ≤ y ^ 3 := by positivity
  have hs : 0 ≤ (y ^ 2 + a ^ 2) := by positivity
  have key : 10 * a ^ 4 + 9 * a ^ 2 * y ^ 2 + 3 * y ^ 4 ≤ 10 * (y ^ 2 + a ^ 2) ^ 2 := by
    nlinarith [sq_nonneg y, sq_nonneg a, mul_nonneg (sq_nonneg y) (sq_nonneg a)]
  calc
    y ^ 3 * (10 * a ^ 4 + 9 * a ^ 2 * y ^ 2 + 3 * y ^ 4) * a ^ 2 ≤
        y ^ 3 * (10 * (y ^ 2 + a ^ 2) ^ 2) * a ^ 2 :=
      by gcongr
    _ ≤ y ^ 3 * (10 * (y ^ 2 + a ^ 2) ^ 2) * (y ^ 2 + a ^ 2) := by gcongr; nlinarith [sq_nonneg y]
    _ = 10 / 6 * y ^ 3 * (6 * (y ^ 2 + a ^ 2) ^ 3) := by ring

lemma abs_g3_le {a : ℝ} (ha : 0 < a) {y : ℝ} (_hy : 0 ≤ y) : |g3 a y| ≤ 5 * y ^ 2 / a ^ 2 := by
  unfold g3
  rw [abs_of_nonneg (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
  have hs : 0 ≤ (y ^ 2 + a ^ 2) := by positivity
  have key :
    10 * a ^ 6 + 5 * a ^ 4 * y ^ 2 + 4 * a ^ 2 * y ^ 4 + y ^ 6 ≤ 10 * (y ^ 2 + a ^ 2) ^ 3 := by
    nlinarith [sq_nonneg y, sq_nonneg a, mul_nonneg (sq_nonneg y) (sq_nonneg a),
      mul_nonneg (mul_nonneg (sq_nonneg y) (sq_nonneg a)) (sq_nonneg y),
      mul_nonneg (mul_nonneg (sq_nonneg y) (sq_nonneg a)) (sq_nonneg a),
      pow_nonneg (sq_nonneg y) 3, pow_nonneg (sq_nonneg a) 3]
  calc
    y ^ 2 * (10 * a ^ 6 + 5 * a ^ 4 * y ^ 2 + 4 * a ^ 2 * y ^ 4 + y ^ 6) * a ^ 2 ≤
        y ^ 2 * (10 * (y ^ 2 + a ^ 2) ^ 3) * a ^ 2 :=
      by gcongr
    _ ≤ y ^ 2 * (10 * (y ^ 2 + a ^ 2) ^ 3) * (y ^ 2 + a ^ 2) := by gcongr; nlinarith [sq_nonneg y]
    _ = 5 * y ^ 2 * (2 * (y ^ 2 + a ^ 2) ^ 4) := by ring

lemma g4_eq_mul_h4 (a y : ℝ) : g4 a y = y * h4 a y := by unfold g4 h4; ring

lemma abs_g4_le' {a : ℝ} (ha : 0 < a) {y : ℝ} (hy : 0 ≤ y) : |g4 a y| ≤ 20 * y / a ^ 2 := by
  rw [g4_eq_mul_h4, abs_mul, abs_of_nonneg hy]
  have h := abs_h4_le ha y
  have h2 : 20 / (y ^ 2 + a ^ 2) ≤ 20 / a ^ 2 := by gcongr; nlinarith [sq_nonneg y]
  calc
    y * |h4 a y| ≤ y * (20 / a ^ 2) := by gcongr; exact h.trans h2
    _ = 20 * y / a ^ 2 := by ring

/-! ### Product bounds -/

/--
`|G F| ≤ 4 y^e (1+2πy)^5 / (a² q)` from `|G| ≤ c y^(m+1+e)/a²`, `|F| ≤ d (1+2πy)^(m+1)/(2π y^(m+1)
q)`,
`c d ≤ 8π`, `m + 1 ≤ 5`. -/
lemma prod_bound_aux {a y : ℝ} (ha : 0 < a) (hy : 0 < y) {G Fv c d : ℝ} {m e : ℕ}
    (hG : |G| ≤ c * y ^ (m + 1 + e) / a ^ 2)
    (hF : |Fv| ≤ d * (1 + 2 * Real.pi * y) ^ (m + 1) / (2 * Real.pi * y ^ (m + 1) * qe y))
    (hc : 0 ≤ c) (_hd : 0 ≤ d) (hcd : c * d ≤ 8 * Real.pi) (hm : m + 1 ≤ 5) :
    |G * Fv| ≤ 4 * y ^ e * (1 + 2 * Real.pi * y) ^ 5 / (a ^ 2 * qe y) := by
  have hq := qe_pos y
  have hpi := Real.pi_pos
  have hb : 1 ≤ 1 + 2 * Real.pi * y := by nlinarith
  have hpow : (1 + 2 * Real.pi * y) ^ (m + 1) ≤ (1 + 2 * Real.pi * y) ^ 5 :=
    pow_le_pow_right₀ hb hm
  rw [abs_mul]
  calc
    |G| * |Fv| ≤
        (c * y ^ (m + 1 + e) / a ^ 2) *
          (d * (1 + 2 * Real.pi * y) ^ (m + 1) / (2 * Real.pi * y ^ (m + 1) * qe y)) :=
      mul_le_mul hG hF (abs_nonneg _) (by positivity)
    _ = (c * d / (2 * Real.pi)) * (y ^ e * (1 + 2 * Real.pi * y) ^ (m + 1) / (a ^ 2 * qe y)) := by
      rw [pow_add, pow_add]
      field_simp
      try ring
    _ ≤ (8 * Real.pi / (2 * Real.pi)) * (y ^ e * (1 + 2 * Real.pi * y) ^ 5 / (a ^ 2 * qe y)) := by
      gcongr
    _ = 4 * y ^ e * (1 + 2 * Real.pi * y) ^ 5 / (a ^ 2 * qe y) := by
      field_simp
      try ring

lemma abs_g0F4_le {a : ℝ} (ha : 0 < a) {y : ℝ} (hy : 0 < y) :
    |g0 a y * F4 y| ≤ 4 * y ^ 0 * (1 + 2 * Real.pi * y) ^ 5 / (a ^ 2 * qe y) :=
  prod_bound_aux ha hy (m := 4) (e := 0) (abs_g0_le ha hy.le) (abs_F4_le hy) (by norm_num)
    (by norm_num) (by nlinarith [Real.pi_gt_three]) (by norm_num)

lemma abs_g1F3_le {a : ℝ} (ha : 0 < a) {y : ℝ} (hy : 0 < y) :
    |g1 a y * F3 y| ≤ 4 * y ^ 0 * (1 + 2 * Real.pi * y) ^ 5 / (a ^ 2 * qe y) :=
  prod_bound_aux ha hy (m := 3) (e := 0) (abs_g1_le ha hy.le) (abs_F3_le hy) (by norm_num)
    (by norm_num) (by nlinarith [Real.pi_gt_three]) (by norm_num)

lemma abs_g2F2_le {a : ℝ} (ha : 0 < a) {y : ℝ} (hy : 0 < y) :
    |g2 a y * F2 y| ≤ 4 * y ^ 0 * (1 + 2 * Real.pi * y) ^ 5 / (a ^ 2 * qe y) :=
  prod_bound_aux ha hy (m := 2) (e := 0) (abs_g2_le ha hy.le) (abs_F2_le hy) (by norm_num)
    (by norm_num) (by nlinarith [Real.pi_gt_three]) (by norm_num)

lemma abs_g3F1_le {a : ℝ} (ha : 0 < a) {y : ℝ} (hy : 0 < y) :
    |g3 a y * F1 y| ≤ 4 * y ^ 0 * (1 + 2 * Real.pi * y) ^ 5 / (a ^ 2 * qe y) :=
  prod_bound_aux ha hy (m := 1) (e := 0) (abs_g3_le ha hy.le) (abs_F1_le hy) (by norm_num)
    (by norm_num) (by nlinarith [Real.pi_gt_three]) (by norm_num)

lemma abs_g4F0_le {a : ℝ} (ha : 0 < a) {y : ℝ} (hy : 0 < y) :
    |g4 a y * F0 y| ≤ 4 * y ^ 0 * (1 + 2 * Real.pi * y) ^ 5 / (a ^ 2 * qe y) :=
  prod_bound_aux ha hy (m := 0) (e := 0) (by simpa using abs_g4_le' ha hy.le) (abs_F0_le hy)
    (by norm_num) (by norm_num) (by nlinarith [Real.pi_gt_three]) (by norm_num)

lemma abs_g0F3_le {a : ℝ} (ha : 0 < a) {y : ℝ} (hy : 0 < y) :
    |g0 a y * F3 y| ≤ 4 * y ^ 1 * (1 + 2 * Real.pi * y) ^ 5 / (a ^ 2 * qe y) :=
  prod_bound_aux ha hy (m := 3) (e := 1) (abs_g0_le ha hy.le) (abs_F3_le hy) (by norm_num)
    (by norm_num) (by nlinarith [Real.pi_gt_three]) (by norm_num)

lemma abs_g1F2_le {a : ℝ} (ha : 0 < a) {y : ℝ} (hy : 0 < y) :
    |g1 a y * F2 y| ≤ 4 * y ^ 1 * (1 + 2 * Real.pi * y) ^ 5 / (a ^ 2 * qe y) :=
  prod_bound_aux ha hy (m := 2) (e := 1) (abs_g1_le ha hy.le) (abs_F2_le hy) (by norm_num)
    (by norm_num) (by nlinarith [Real.pi_gt_three]) (by norm_num)

lemma abs_g2F1_le {a : ℝ} (ha : 0 < a) {y : ℝ} (hy : 0 < y) :
    |g2 a y * F1 y| ≤ 4 * y ^ 1 * (1 + 2 * Real.pi * y) ^ 5 / (a ^ 2 * qe y) :=
  prod_bound_aux ha hy (m := 1) (e := 1) (abs_g2_le ha hy.le) (abs_F1_le hy) (by norm_num)
    (by norm_num) (by nlinarith [Real.pi_gt_three]) (by norm_num)

lemma abs_g3F0_le {a : ℝ} (ha : 0 < a) {y : ℝ} (hy : 0 < y) :
    |g3 a y * F0 y| ≤ 4 * y ^ 1 * (1 + 2 * Real.pi * y) ^ 5 / (a ^ 2 * qe y) :=
  prod_bound_aux ha hy (m := 0) (e := 1) (abs_g3_le ha hy.le) (abs_F0_le hy) (by norm_num)
    (by norm_num) (by nlinarith [Real.pi_gt_three]) (by norm_num)

/-! ### `(1 + x)^5 e^{-x} ≤ C e^{-x/2}` -/

lemma poly_exp_bound {x : ℝ} (hx : 0 ≤ x) :
    (1 + x) ^ 5 * Real.exp (-x) ≤ 122912 * Real.exp (-(x / 2)) := by
  have h1 : (1 + x) ^ 5 ≤ 32 * (1 + x ^ 5) := by
    rcases le_or_gt x 1 with h | h
    · have : (1 + x) ^ 5 ≤ 2 ^ 5 := pow_le_pow_left₀ (by linarith) (by linarith) 5
      have : 0 ≤ x ^ 5 := by positivity
      nlinarith
    · have : (1 + x) ^ 5 ≤ (2 * x) ^ 5 := pow_le_pow_left₀ (by linarith) (by linarith) 5
      have : 0 ≤ x ^ 5 := by positivity
      nlinarith
  have h2 := Real.pow_div_factorial_le_exp (x := x / 2) (by positivity) 5
  have h3 : x ^ 5 ≤ 3840 * Real.exp (x / 2) := by
    rw [Nat.factorial] at h2; norm_num at h2
    have : (x / 2) ^ 5 = x ^ 5 / 32 := by ring
    rw [this] at h2
    linarith
  have h4 : (1 : ℝ) ≤ Real.exp (x / 2) := Real.one_le_exp (by positivity)
  have h5 : (1 + x) ^ 5 ≤ 122912 * Real.exp (x / 2) := by nlinarith
  have he : Real.exp (-x) = Real.exp (-(x / 2)) * Real.exp (-(x / 2)) := by
    rw [← Real.exp_add];
    ring_nf
  have he2 : Real.exp (x / 2) * Real.exp (-(x / 2)) = 1 := by rw [← Real.exp_add]; simp
  calc
    (1 + x) ^ 5 * Real.exp (-x) ≤ 122912 * Real.exp (x / 2) * Real.exp (-x) := by gcongr
    _ = 122912 * Real.exp (-(x / 2)) * (Real.exp (x / 2) * Real.exp (-(x / 2))) := by
      rw [he];
      ring
    _ = 122912 * Real.exp (-(x / 2)) := by rw [he2, mul_one]

lemma bound_exp {a y : ℝ} (ha : 0 < a) (hy : 0 < y) (e : ℕ) :
    4 * y ^ e * (1 + 2 * Real.pi * y) ^ 5 / (a ^ 2 * qe y) ≤
      4 * 122912 / a ^ 2 * (y ^ e * Real.exp (-(Real.pi * y))) := by
  have h := poly_exp_bound (x := 2 * Real.pi * y) (by positivity)
  have hq : qe y = Real.exp (2 * Real.pi * y) := rfl
  have hinv : 1 / qe y = Real.exp (-(2 * Real.pi * y)) := by rw [hq, Real.exp_neg, one_div]
  have hx2 : -(2 * Real.pi * y / 2) = -(Real.pi * y) := by ring
  rw [hx2] at h
  calc
    4 * y ^ e * (1 + 2 * Real.pi * y) ^ 5 / (a ^ 2 * qe y) =
        4 / a ^ 2 * y ^ e * ((1 + 2 * Real.pi * y) ^ 5 * (1 / qe y)) :=
      by field_simp
    _ = 4 / a ^ 2 * y ^ e * ((1 + 2 * Real.pi * y) ^ 5 * Real.exp (-(2 * Real.pi * y))) := by
      rw [hinv]
    _ ≤ 4 / a ^ 2 * y ^ e * (122912 * Real.exp (-(Real.pi * y))) := by gcongr
    _ = _ := by ring

/-! ### Continuity, integrability, limits -/

@[fun_prop]
lemma continuous_qe : Continuous qe := by unfold qe; fun_prop

lemma qe_sub_one_ne {y : ℝ} (hy : y ∈ Ioi (0 : ℝ)) : qe y - 1 ≠ 0 := by
  have := qe_gt_one (show (0 : ℝ) < y from hy); linarith

lemma continuousOn_F0 : ContinuousOn F0 (Ioi 0) := by
  unfold F0;
  exact ContinuousOn.div continuousOn_const (by fun_prop) fun y hy => qe_sub_one_ne hy

lemma continuousOn_F1 : ContinuousOn F1 (Ioi 0) := by
  unfold F1;
  exact ContinuousOn.div (by fun_prop) (by fun_prop) fun y hy => pow_ne_zero _ (qe_sub_one_ne hy)

lemma continuousOn_F2 : ContinuousOn F2 (Ioi 0) := by
  unfold F2;
  exact ContinuousOn.div (by fun_prop) (by fun_prop) fun y hy => pow_ne_zero _ (qe_sub_one_ne hy)

lemma continuousOn_F3 : ContinuousOn F3 (Ioi 0) := by
  unfold F3;
  exact ContinuousOn.div (by fun_prop) (by fun_prop) fun y hy => pow_ne_zero _ (qe_sub_one_ne hy)

lemma continuousOn_F4 : ContinuousOn F4 (Ioi 0) := by
  unfold F4;
  exact ContinuousOn.div (by fun_prop) (by fun_prop) fun y hy => pow_ne_zero _ (qe_sub_one_ne hy)

lemma continuous_g0 {a : ℝ} (ha : 0 < a) : Continuous (g0 a) := by
  unfold g0;
  exact (by fun_prop : Continuous fun y : ℝ => y ^ 5).div (by fun_prop) (fun y => by positivity)

lemma continuous_g1 {a : ℝ} (ha : 0 < a) : Continuous (g1 a) := by
  unfold g1;
  exact
    (by fun_prop : Continuous fun y : ℝ => y ^ 4 * (5 * a ^ 2 + 3 * y ^ 2)).div (by fun_prop)
      (fun y => by positivity)

lemma continuous_g2 {a : ℝ} (ha : 0 < a) : Continuous (g2 a) := by
  unfold g2;
  exact
    (by fun_prop :
          Continuous fun y : ℝ => y ^ 3 * (10 * a ^ 4 + 9 * a ^ 2 * y ^ 2 + 3 * y ^ 4)).div
      (by fun_prop) (fun y => by positivity)

lemma continuous_g3 {a : ℝ} (ha : 0 < a) : Continuous (g3 a) := by
  unfold g3;
  exact
    (by fun_prop :
          Continuous fun y : ℝ =>
            y ^ 2 * (10 * a ^ 6 + 5 * a ^ 4 * y ^ 2 + 4 * a ^ 2 * y ^ 4 + y ^ 6)).div
      (by fun_prop) (fun y => by positivity)

/-- Integrability on `(0, ∞)` of a product bounded by `4 y^0 (1+2πy)^5/(a² q)`. -/
lemma integrableOn_of_prod_bound {a : ℝ} (ha : 0 < a) {f : ℝ → ℝ} (hf : ContinuousOn f (Ioi 0))
    (hb : ∀ y, 0 < y → |f y| ≤ 4 * y ^ 0 * (1 + 2 * Real.pi * y) ^ 5 / (a ^ 2 * qe y)) :
    IntegrableOn f (Ioi 0) := by
  have hg :
    IntegrableOn (fun y : ℝ => 4 * 122912 / a ^ 2 * (y ^ 0 * Real.exp (-(Real.pi * y))))
      (Ioi 0) :=
    (integrableOn_pow_mul_exp_neg_mul 0 Real.pi_pos).const_mul _
  refine hg.mono' (hf.aestronglyMeasurable measurableSet_Ioi) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun y hy => ?_)
  have hy : 0 < y := hy
  rw [Real.norm_eq_abs]
  exact (hb y hy).trans (bound_exp ha hy 0)

/-- Vanishing at `0⁺` and `∞` of a product bounded by `4 y (1+2πy)^5/(a² q)`. -/
lemma tendsto_of_prod_bound {a : ℝ} (ha : 0 < a) {f : ℝ → ℝ}
    (hb : ∀ y, 0 < y → |f y| ≤ 4 * y ^ 1 * (1 + 2 * Real.pi * y) ^ 5 / (a ^ 2 * qe y)) :
    Tendsto f (𝓝[>] 0) (𝓝 0) ∧ Tendsto f atTop (𝓝 0) := by
  have hb' : ∀ y, 0 < y → |f y| ≤ 4 * 122912 / a ^ 2 * (y ^ 1 * Real.exp (-(Real.pi * y))) :=
    fun y hy => (hb y hy).trans (bound_exp ha hy 1)
  constructor
  · rw [tendsto_zero_iff_abs_tendsto_zero]
    refine
      squeeze_zero' (Filter.Eventually.of_forall fun y => abs_nonneg _)
        (eventually_nhdsWithin_of_forall fun y hy => hb' y hy) ?_
    have hc : Continuous fun y : ℝ => 4 * 122912 / a ^ 2 * (y ^ 1 * Real.exp (-(Real.pi * y))) :=
      by fun_prop
    have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    convert this using 2
    simp
  · rw [tendsto_zero_iff_abs_tendsto_zero]
    refine
      squeeze_zero' (Filter.Eventually.of_forall fun y => abs_nonneg _)
        ((eventually_gt_atTop 0).mono fun y hy => hb' y hy) ?_
    have h1 :=
      (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
        (tendsto_id.const_mul_atTop Real.pi_pos)
    have h2 : Tendsto (fun y : ℝ => y ^ 1 * Real.exp (-(Real.pi * y))) atTop (𝓝 0) := by
      have := h1.const_mul (1 / Real.pi)
      rw [mul_zero] at this
      refine this.congr' (Filter.Eventually.of_forall fun y => ?_)
      simp only [Function.comp, id, pow_one]
      have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
      field_simp
    simpa using h2.const_mul (4 * 122912 / a ^ 2)

/-! ### The integrations by parts -/

lemma ibp_step {u u' v v' : ℝ → ℝ} (hu : ∀ y ∈ Ioi (0 : ℝ), HasDerivAt u (u' y) y)
    (hv : ∀ y ∈ Ioi (0 : ℝ), HasDerivAt v (v' y) y)
    (h1 : IntegrableOn (fun y => u y * v' y) (Ioi 0))
    (h2 : IntegrableOn (fun y => u' y * v y) (Ioi 0))
    (h0 : Tendsto (fun y => u y * v y) (𝓝[>] 0) (𝓝 0))
    (hinf : Tendsto (fun y => u y * v y) atTop (𝓝 0)) :
    ∫ y in Ioi 0, u y * v' y = -∫ y in Ioi 0, u' y * v y := by
  have := integral_Ioi_mul_deriv_eq_deriv_mul hu hv h1 h2 h0 hinf
  rw [this]; ring

/-- **Four integrations by parts**: `∫₀^∞ g F₄ = ∫₀^∞ g₄ F₀`. -/
theorem integral_g0F4_eq {a : ℝ} (ha : 0 < a) :
    ∫ y in Ioi 0, g0 a y * F4 y = ∫ y in Ioi 0, g4 a y * F0 y := by
  have hg0 : ∀ y ∈ Ioi (0 : ℝ), HasDerivAt (g0 a) (g1 a y) y := fun y _ => hasDerivAt_g0 ha y
  have hg1 : ∀ y ∈ Ioi (0 : ℝ), HasDerivAt (g1 a) (g2 a y) y := fun y _ => hasDerivAt_g1 ha y
  have hg2 : ∀ y ∈ Ioi (0 : ℝ), HasDerivAt (g2 a) (g3 a y) y := fun y _ => hasDerivAt_g2 ha y
  have hg3 : ∀ y ∈ Ioi (0 : ℝ), HasDerivAt (g3 a) (g4 a y) y := fun y _ => hasDerivAt_g3 ha y
  have hF0 : ∀ y ∈ Ioi (0 : ℝ), HasDerivAt F0 (F1 y) y := fun y hy => hasDerivAt_F0 hy
  have hF1 : ∀ y ∈ Ioi (0 : ℝ), HasDerivAt F1 (F2 y) y := fun y hy => hasDerivAt_F1 hy
  have hF2 : ∀ y ∈ Ioi (0 : ℝ), HasDerivAt F2 (F3 y) y := fun y hy => hasDerivAt_F2 hy
  have hF3 : ∀ y ∈ Ioi (0 : ℝ), HasDerivAt F3 (F4 y) y := fun y hy => hasDerivAt_F3 hy
  have i04 :=
    integrableOn_of_prod_bound ha ((continuous_g0 ha).continuousOn.mul continuousOn_F4)
      (fun y hy => abs_g0F4_le ha hy)
  have i13 :=
    integrableOn_of_prod_bound ha ((continuous_g1 ha).continuousOn.mul continuousOn_F3)
      (fun y hy => abs_g1F3_le ha hy)
  have i22 :=
    integrableOn_of_prod_bound ha ((continuous_g2 ha).continuousOn.mul continuousOn_F2)
      (fun y hy => abs_g2F2_le ha hy)
  have i31 :=
    integrableOn_of_prod_bound ha ((continuous_g3 ha).continuousOn.mul continuousOn_F1)
      (fun y hy => abs_g3F1_le ha hy)
  have i40 :=
    integrableOn_of_prod_bound ha ((continuous_g4 a ha).continuousOn.mul continuousOn_F0)
      (fun y hy => abs_g4F0_le ha hy)
  obtain ⟨z03, t03⟩ :=
    tendsto_of_prod_bound ha (f := fun y => g0 a y * F3 y) (fun y hy => abs_g0F3_le ha hy)
  obtain ⟨z12, t12⟩ :=
    tendsto_of_prod_bound ha (f := fun y => g1 a y * F2 y) (fun y hy => abs_g1F2_le ha hy)
  obtain ⟨z21, t21⟩ :=
    tendsto_of_prod_bound ha (f := fun y => g2 a y * F1 y) (fun y hy => abs_g2F1_le ha hy)
  obtain ⟨z30, t30⟩ :=
    tendsto_of_prod_bound ha (f := fun y => g3 a y * F0 y) (fun y hy => abs_g3F0_le ha hy)
  have s0 := ibp_step hg0 hF3 i04 i13 z03 t03
  have s1 := ibp_step hg1 hF2 i13 i22 z12 t12
  have s2 := ibp_step hg2 hF1 i22 i31 z21 t21
  have s3 := ibp_step hg3 hF0 i31 i40 z30 t30
  rw [s0, s1, s2, s3]; ring

end Zeta5Irrational
