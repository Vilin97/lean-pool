/-
Copyright (c) 2026 Junqi Liu, Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junqi Liu, Jujian Zhang
-/

import Mathlib.Analysis.RCLike.Basic
import Mathlib.Algebra.Order.Star.Real

/-!
# LeanPool.Zeta3Irrational.Bound
-/

namespace LeanPool.Zeta3Irrational

open scoped Nat
open BigOperators

lemma max_value {x : ℝ} (x0 : 0 < x) (x1 : x < 1) : √x * √(1 - x) ≤ ((1 / 2) : ℝ) := by
  rw [← Real.sqrt_mul, le_div_iff₀,
    ← show √4 = 2 by rw [Real.sqrt_eq_iff_eq_sq] <;> linarith,
    ← Real.sqrt_mul, Real.sqrt_le_one,
    show x * (1 - x) * 4 = 1 - (2 * x - 1) ^ 2 by ring] <;>
  nlinarith [mul_self_nonneg (2 * x - 1)]

lemma max_value' {x : ℝ} (x0 : 0 < x) (x1 : x < 1) : √x * (1 - x) ≤ ((2 / 5) : ℝ) := by
  calc
  _ = √(x * (1 - x) ^ 2) := by rw [Real.sqrt_mul, pow_two, Real.sqrt_mul_self] <;> linarith
  _ ≤ √(4 / 27 : ℝ) := by
    refine Real.sqrt_le_sqrt ?_
    suffices x * (1 - x) ^ 2 - (4 / 27 : ℝ) ≤ 0 by linarith
    rw [show x * (1 - x) ^ 2 - (4 / 27 : ℝ) =
      (x - (4 / 3 : ℝ)) * (x - (1 / 3 : ℝ)) ^ 2 by ring, mul_nonpos_iff]
    right
    exact ⟨by linarith, by positivity⟩
  _ ≤ ((2 / 5) : ℝ) := by
    rw [Real.sqrt_le_left] <;> norm_num

lemma nonneg {x : ℝ} (_ : 0 < x) (_ : x < 1) : (0 : ℝ) ≤ √x * √(1 -x) :=
  mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

lemma bound_aux (x z : ℝ) (x0 : 0 < x) (x1 : x < 1) (z0 : 0 < z) (_ : z < 1) :
    2 * √(1 - x) * √(x * z) ≤ 1 - (1 - z) * x := by
  rw [← sub_pos] at x1
  have := mul_pos x0 z0
  rw [show 1 - (1 - z) * x = 1 - x + x * z by ring]
  calc
    _ ≤ (√(1 - x) - √(x * z)) * (√(1 - x) - √(x * z)) + 2 * √(1 - x) * √(x * z) :=
      by linarith [mul_self_nonneg (√(1 - x) - √(x * z))]
    _ = √(1 - x) * √(1 - x) + √(x * z) * √(x * z) := by ring
    _ = 1 - x + x * z := by rw [Real.mul_self_sqrt, Real.mul_self_sqrt] <;> linarith

lemma bound (x y z : ℝ) (x0 : 0 < x) (x1 : x < 1) (y0 : 0 < y) (y1 : y < 1)
    (z0 : 0 < z) (z1 : z < 1) :
    x * (1 -x) * y * (1 - y) * z * (1 - z) /
      ((1 - (1 - z) * x) * (1 - y * z)) < (1 / 30 : ℝ) := by
  have := mul_pos x0 z0
  have h1 : 2 * √(1 - x) * √(x * z) ≤ 1 - (1 - z) * x := by apply bound_aux <;> assumption
  have h2 : 2 * √(1 - y) * √((1 - z) * y) ≤ 1 - y * z := by
    convert bound_aux y (1 - z) y0 y1 (by linarith) (by linarith) using 2
    · rw [mul_comm]
    · ring
  rw [← sub_pos] at x1 y1 z1
  have : y * z < 1 := by nlinarith
  have : 0 < √(1 - x) := Real.sqrt_pos_of_pos x1
  have : 0 < √(x * z) := Real.sqrt_pos_of_pos (by linarith)
  have : 0 < 1 - y * z := by linarith
  have : 0 ≤ x.sqrt * (1 - x).sqrt := nonneg (by assumption) (by linarith)
  have : 0 ≤ y.sqrt * (1 - y).sqrt := nonneg (by assumption) (by linarith)
  calc
    _ ≤ x * (1 -x) * y * (1 - y) * z * (1 - z) / (2 * √(1 - x) * √(x * z) * (1 - y * z)) := by
      refine div_le_div₀ (by positivity) (le_refl _) (by positivity) ?_
      rwa [mul_le_mul_iff_of_pos_right]
      linarith
    _ ≤ x * (1 -x) * y * (1 - y) * z * (1 - z) /
        (2 * √(1 - x) * √(x * z) * 2 * √(1 - y) * √((1 - z) * y)) := by
      refine div_le_div₀ (by positivity) (le_refl _) (by positivity) ?_
      rw [mul_assoc, mul_assoc]
      rw [mul_assoc] at h2
      exact mul_le_mul_of_nonneg_left h2 (le_of_lt <| by positivity)
    _ = √x * √(1 -x) * (√y * √(1 - y)) * (√z * √(1 - z)) / 4 := by
      rw [Real.sqrt_mul (le_of_lt x0) z, Real.sqrt_mul (by linarith : 0 ≤ 1 - z) y]
      calc _
        _ =
            ((x * (1 - x)) * (y * (1 - y)) * (z * (1 - z))) /
              (4 * (√x * √(1 - x)) * (√y * √(1 - y)) * (√z * √(1 - z))) := by
          ring
        _ =
            (x / √x) * ((1 - x) / √(1 - x)) * (y / √y) *
              ((1 - y) / √(1 -y)) * (z / √z) * ((1 - z) / √(1 - z)) / 4 := by
          ring
        _ = _ := by
          simpa only [Real.div_sqrt] using (by ring)
    _ ≤ (1 / 2) * (1 / 2) * (1 / 2) / 4 := by
      refine div_le_div₀ (by norm_num)
        (mul_le_mul_of_nonneg (mul_le_mul_of_nonneg (max_value ?_ ?_) (max_value ?_ ?_) ?_ ?_)
          (max_value ?_ ?_) (mul_nonneg ?_ ?_) ?_) (by norm_num) (by norm_num) <;>
      linarith
    _ < (1 / 30 : ℝ) := by norm_num

lemma bound_aux' (x y z : ℝ) (x0 : 0 < x) (_ : x < 1) (y0 : 0 < y) (_ : y < 1)
    (z0 : 0 < z) (z1 : z < 1) :
    2 * √(1 - z) * √(x * y * z) ≤ 1 - (1 - x * y) * z := by
  rw [← sub_pos] at z1
  have := mul_pos x0 (mul_pos y0 z0)
  rw [show 1 - (1 - x * y) * z = (1 - z) + x * y * z by ring]
  calc
    _ ≤ (√(1 - z) - √(x * y * z)) * (√(1 - z) - √(x * y * z)) +
        2 * √(1 - z) * √(x * y * z) :=
      by linarith [mul_self_nonneg (√(1 - z) - √(x * y * z))]
    _ = √(1 - z) * √(1 - z) + √(x * y * z) * √(x * y * z) := by ring
    _ = 1 - z + x * y * z := by rw [Real.mul_self_sqrt, Real.mul_self_sqrt] <;> linarith

lemma bound' (x y z : ℝ) (x0 : 0 < x) (x1 : x < 1) (y0 : 0 < y) (y1 : y < 1)
    (z0 : 0 < z) (z1 : z < 1) :
    x * (1 - x) * y * (1 - y) * z * (1 - z) / (1 - (1 - x * y) * z) < (1 / 24 : ℝ) := by
  have := mul_pos x0 z0
  have h1 : 2 * √(1 - x) * √(x * z) ≤ 1 - (1 - z) * x := by apply bound_aux <;> assumption
  have h2 : 2 * √(1 - y) * √((1 - z) * y) ≤ 1 - y * z := by
    convert bound_aux y (1 - z) y0 y1 (by linarith) (by linarith) using 2
    · rw [mul_comm]
    · ring
  rw [← sub_pos] at x1 y1 z1
  have : y * z < 1 := by nlinarith
  have : 0 < √(1 - x) := Real.sqrt_pos_of_pos x1
  have : 0 < √(x * z) := Real.sqrt_pos_of_pos (by linarith)
  have : 0 < 1 - y * z := by linarith
  have : 0 ≤ x.sqrt * (1 - x) := mul_nonneg (Real.sqrt_nonneg _) (by linarith)
  have : 0 ≤ y.sqrt * (1 - y) := mul_nonneg (Real.sqrt_nonneg _) (by linarith)
  calc
    _ ≤ x * (1 -x) * y * (1 - y) * z * (1 - z) / (2 * √(1 - z) * √(x * y * z)) := by
      refine div_le_div₀ (by positivity) (le_refl _) (by positivity) ?_
      apply bound_aux' <;> linarith
    _ = √x * (1 - x) * (√y * (1 - y)) * (√z * √(1 - z)) / 2 := by
      rw [Real.sqrt_mul (by positivity : 0 ≤ x * y) z, Real.sqrt_mul (le_of_lt x0) y]
      calc _
        _ =
            ((x * (1 - x)) * (y * (1 - y)) * (z * (1 - z))) /
              (2 * √x * √y * (√z * √(1 - z))) := by
          ring
        _ =
            (x / √x) * (1 - x) * (y / √y) * (1 - y) *
              (z / √z) * ((1 - z) / √(1 - z)) / 2 := by
          ring
        _ = _ := by
          simpa only [Real.div_sqrt] using (by ring)
    _ ≤ (2 / 5) * (2 / 5) * (1 / 2) / 2 := by
      refine div_le_div₀ (by norm_num)
        (mul_le_mul_of_nonneg (mul_le_mul_of_nonneg (max_value' ?_ ?_) (max_value' ?_ ?_) ?_ ?_)
          (max_value ?_ ?_) (mul_nonneg ?_ ?_) ?_) (by norm_num) (by norm_num) <;>
      try nlinarith
    _ < (1 / 24 : ℝ) := by
      norm_num

lemma bound'' (x y z : ℝ) (x0 : 0 < x) (x1 : x < 1) (y0 : 0 < y) (y1 : y < 1)
    (z0 : 0 < z) (z1 : z < 1) :
    x * (1 - x) * y * (1 - y) * z * (1 - z) / (1 - (1 - x * y) * z) <
      (1 / 30 : ℝ) := by
  let s := √(x * y)
  have hs0 : 0 ≤ s := by positivity
  have hs1 : s ≤ 1 := by
    change √(x * y) ≤ 1
    rw [Real.sqrt_le_one]
    nlinarith
  have hs_sq : s ^ 2 = x * y := by
    change (√(x * y)) ^ 2 = x * y
    rw [pow_two, Real.mul_self_sqrt]
    positivity
  have hxy_le : (1 - x) * (1 - y) ≤ (1 - s) ^ 2 := by
    have h_amgm : 2 * s ≤ x + y := by
      have hsqrtx : √x * √x = x := Real.mul_self_sqrt (le_of_lt x0)
      have hsqrty : √y * √y = y := Real.mul_self_sqrt (le_of_lt y0)
      have hsqrtxy : √x * √y = s := by
        change √x * √y = √(x * y)
        rw [← Real.sqrt_mul (le_of_lt x0) y]
      nlinarith [sq_nonneg (√x - √y)]
    nlinarith [hs_sq]
  have hden_pos : 0 < 1 - (1 - x * y) * z := by
    have hxy_lt_one : x * y < 1 := by nlinarith
    nlinarith
  have hden_pos_s : 0 < 1 - (1 - s ^ 2) * z := by
    rw [hs_sq]
    exact hden_pos
  have hfrac :
      z * (1 - z) / (1 - (1 - s ^ 2) * z) ≤ 1 / (1 + s) ^ 2 := by
    rw [div_le_div_iff₀ hden_pos_s (by positivity : 0 < (1 + s) ^ 2)]
    ring_nf
    nlinarith [sq_nonneg (1 - (1 + s) * z)]
  have hratio_nonneg : 0 ≤ s * (1 - s) / (1 + s) := by positivity
  have hratio_le : s * (1 - s) / (1 + s) ≤ (2 / 11 : ℝ) := by
    rw [div_le_iff₀ (by positivity : 0 < 1 + s)]
    have hquad : 0 ≤ 11 * s ^ 2 - 9 * s + 2 := by
      nlinarith [sq_nonneg (22 * s - 9)]
    nlinarith
  have hratio_sq_le : (s * (1 - s) / (1 + s)) ^ 2 ≤ (2 / 11 : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((2 / 11 : ℝ) - s * (1 - s) / (1 + s)), hratio_nonneg,
      hratio_le]
  have hnum_le :
      x * (1 - x) * y * (1 - y) * z * (1 - z) ≤
        s ^ 2 * (1 - s) ^ 2 * z * (1 - z) := by
    calc
      x * (1 - x) * y * (1 - y) * z * (1 - z)
          = s ^ 2 * ((1 - x) * (1 - y)) * (z * (1 - z)) := by
            rw [hs_sq]
            ring
      _ ≤ s ^ 2 * (1 - s) ^ 2 * (z * (1 - z)) := by
        gcongr
      _ = s ^ 2 * (1 - s) ^ 2 * z * (1 - z) := by ring
  calc
    x * (1 - x) * y * (1 - y) * z * (1 - z) / (1 - (1 - x * y) * z)
        ≤ s ^ 2 * (1 - s) ^ 2 * z * (1 - z) / (1 - (1 - s ^ 2) * z) := by
          rw [← hs_sq]
          refine div_le_div₀ ?_ hnum_le hden_pos_s (le_refl _)
          positivity
    _ = s ^ 2 * (1 - s) ^ 2 * (z * (1 - z) / (1 - (1 - s ^ 2) * z)) := by
      ring
    _ ≤ s ^ 2 * (1 - s) ^ 2 * (1 / (1 + s) ^ 2) := by
      gcongr
    _ = (s * (1 - s) / (1 + s)) ^ 2 := by
      field_simp [(by positivity : 0 < 1 + s).ne']
    _ ≤ (2 / 11 : ℝ) ^ 2 := hratio_sq_le
    _ < (1 / 30 : ℝ) := by norm_num

end LeanPool.Zeta3Irrational
