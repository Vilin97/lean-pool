/-
Copyright (c) 2026 Junqi Liu, Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junqi Liu, Jujian Zhang
-/

import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Real.StarOrdered

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

end LeanPool.Zeta3Irrational
