/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! The source's exponential tail follows quantitatively from its polynomial grade base. -/

@[expose] public section


noncomputable section

namespace EulerPacketTailBound

open Real

theorem grade_ratio_le_decay (k B : ℝ) (hk : 0 < k) (hB : B ≤ k ^ (1 / 100 : ℝ)) :
    B/k ≤ k^(-99/100 : ℝ) := by
  calc
    B/k ≤ k^(1/100 : ℝ)/k := div_le_div_of_nonneg_right hB hk.le
    _ = k^(-99/100 : ℝ) := by
      rw [← Real.rpow_sub_one hk.ne']
      norm_num

theorem grade_ratio_le_half (k B : ℝ) (hk : 4 ≤ k) (hB : B ≤ k ^ (1 / 100 : ℝ)) :
    B/k ≤ 1/2 := by
  have hk0 : 0 < k := by linarith
  have hsqrt : (2 : ℝ) ≤ Real.sqrt k := by
    have h := Real.sqrt_le_sqrt hk
    norm_num at h
    exact h
  calc
    B/k ≤ k^(-99/100 : ℝ) := grade_ratio_le_decay k B hk0 hB
    _ ≤ k^(-(1/2) : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    _ = (Real.sqrt k)⁻¹ := by rw [Real.rpow_neg hk0.le, ← Real.sqrt_eq_rpow]
    _ ≤ 1/2 := by
      simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ)<2) hsqrt

theorem normalized_tail_exponential (k B C X : ℝ) (hk : 4 ≤ k) (hB0 : 0 ≤ B)
    (hC0 : 0 ≤ C) (hB : B ≤ k ^ (1 / 100 : ℝ)) (hC : C ≤ k ^ (1 / 100 : ℝ))
    (N : ℕ) (hX : 6 ≤ X) (hN : X - 1 ≤ (N : ℝ)) :
    2*C*k*B*(B/k)^(N+1) ≤ Real.exp (-(7/10)*X*Real.log k) := by
  have hk0 : 0 < k := by linarith
  have htwo : (2 : ℝ) ≤ k^(1/2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    have h := Real.sqrt_le_sqrt hk
    norm_num at h
    exact h
  have hCB : C*k*B ≤ k^(102/100 : ℝ) := by
    calc
      C*k*B ≤ k^(1/100 : ℝ)*k*k^(1/100 : ℝ) :=
        mul_le_mul (mul_le_mul_of_nonneg_right hC hk0.le) hB hB0 (by positivity)
      _ = k^(1/100 : ℝ)*k^(1 : ℝ)*k^(1/100 : ℝ) := by rw [Real.rpow_one]
      _ = k^(102/100 : ℝ) := by
        rw [← Real.rpow_add hk0, ← Real.rpow_add hk0]
        norm_num
  have hp := pow_le_pow_left₀ (div_nonneg hB0 hk0.le)
    (grade_ratio_le_decay k B hk0 hB) (N+1)
  calc
    2*C*k*B*(B/k)^(N+1) = (2*(C*k*B))*(B/k)^(N+1) := by ring
    _ ≤ (k^(1/2 : ℝ)*k^(102/100 : ℝ))*(k^(-99/100 : ℝ))^(N+1) :=
      mul_le_mul (mul_le_mul htwo hCB (by positivity) (by positivity)) hp
        (by positivity) (by positivity)
    _ = k^((53/100)-(99/100)*(N : ℝ)) := by
      rw [← Real.rpow_mul_natCast hk0.le, ← Real.rpow_add hk0, ← Real.rpow_add hk0]
      congr 1
      push_cast
      ring
    _ ≤ k^(-(7/10)*X) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    _ = Real.exp (-(7/10)*X*Real.log k) := by
      rw [Real.rpow_def_of_pos hk0]
      congr 1
      ring

end EulerPacketTailBound
