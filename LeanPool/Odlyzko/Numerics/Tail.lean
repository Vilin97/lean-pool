/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-! TODO: Add doc-string. -/

@[expose] public section

namespace NumberField.Odlyzko

theorem one_div_sinh_le_exp_tail {x : ℝ} (hx : 1 ≤ x) :
    1 / Real.sinh x ≤ (8 / 3 : ℝ) * Real.exp (-x) := by
  have he : Real.exp (-x) < 1 / 2 := by
    exact (Real.exp_le_exp.mpr (by linarith)).trans_lt Real.exp_neg_one_lt_half
  have he0 : 0 < Real.exp (-x) := Real.exp_pos _
  have hexp : Real.exp x * Real.exp (-x) = 1 := by
    rw [← Real.exp_add]
    simp
  have hsinh : 3 / 8 * Real.exp x ≤ Real.sinh x := by
    rw [Real.sinh_eq]
    have hneg : Real.exp (-x) ≤ Real.exp x / 4 := by
      nlinarith
    linarith
  have hsinh0 : 0 < Real.sinh x :=
    Real.sinh_pos_iff.mpr (lt_of_lt_of_le zero_lt_one hx)
  rw [div_le_iff₀ hsinh0]
  nlinarith

theorem one_div_sinh_le_seven_thirds_exp {x : ℝ} (hx : 1 ≤ x) :
    1 / Real.sinh x ≤ (7 / 3 : ℝ) * Real.exp (-x) := by
  have he : Real.exp (-x) < 3 / 8 := by
    exact (Real.exp_le_exp.mpr (by linarith)).trans_lt
      (Real.exp_neg_one_lt_d9.trans (by norm_num))
  have he0 : 0 < Real.exp (-x) := Real.exp_pos _
  have hexp : Real.exp x * Real.exp (-x) = 1 := by
    rw [← Real.exp_add]
    simp
  have hneg : Real.exp (-x) ≤ Real.exp x / 7 := by nlinarith
  have hsinh : 3 / 7 * Real.exp x ≤ Real.sinh x := by
    rw [Real.sinh_eq]
    linarith
  have hsinh0 : 0 < Real.sinh x :=
    Real.sinh_pos_iff.mpr (lt_of_lt_of_le zero_lt_one hx)
  rw [div_le_iff₀ hsinh0]
  nlinarith

theorem one_div_sinh_le_sixty_four_thirty_one_exp {x : ℝ} (hx : 2 ≤ x) :
    1 / Real.sinh x ≤ (64 / 31 : ℝ) * Real.exp (-x) := by
  have he1 : Real.exp (-x) < 9 / 64 := by
    have hmono : Real.exp (-x) ≤ Real.exp (-2) := Real.exp_le_exp.mpr (by linarith)
    have hpow : Real.exp (-2) = Real.exp (-1) ^ 2 := by
      calc
        Real.exp (-2) = Real.exp ((2 : ℕ) * (-1 : ℝ)) := by norm_num
        _ = Real.exp (-1) ^ 2 := Real.exp_nat_mul (-1) 2
    rw [hpow] at hmono
    have he := Real.exp_neg_one_lt_d9
    have he0 := Real.exp_pos (-1)
    nlinarith
  have he0 : 0 < Real.exp (-x) := Real.exp_pos _
  have hexp : Real.exp x * Real.exp (-x) = 1 := by
    rw [← Real.exp_add]
    simp
  have hneg : Real.exp (-x) ≤ Real.exp x / 32 := by nlinarith
  have hsinh : 31 / 64 * Real.exp x ≤ Real.sinh x := by
    rw [Real.sinh_eq]
    linarith
  have hsinh0 : 0 < Real.sinh x :=
    Real.sinh_pos_iff.mpr (lt_of_lt_of_le (by norm_num) hx)
  rw [div_le_iff₀ hsinh0]
  nlinarith

theorem one_div_sinh_le_exp_tail_four {x : ℝ} (hx : 4 ≤ x) :
    1 / Real.sinh x ≤ (512 / 255 : ℝ) * Real.exp (-x) := by
  have he1 : Real.exp (-x) < 1 / 16 := by
    have hmono : Real.exp (-x) ≤ Real.exp (-4) := Real.exp_le_exp.mpr (by linarith)
    have hpow : Real.exp (-4) = Real.exp (-1) ^ 4 := by
      calc
        Real.exp (-4) = Real.exp ((4 : ℕ) * (-1 : ℝ)) := by norm_num
        _ = Real.exp (-1) ^ 4 := Real.exp_nat_mul (-1) 4
    rw [hpow] at hmono
    have he := Real.exp_neg_one_lt_half
    nlinarith [sq_nonneg (Real.exp (-1)), mul_self_lt_mul_self (by positivity) he]
  have he0 : 0 < Real.exp (-x) := Real.exp_pos _
  have hexp : Real.exp x * Real.exp (-x) = 1 := by
    rw [← Real.exp_add]
    simp
  have hneg : Real.exp (-x) ≤ Real.exp x / 256 := by
    nlinarith
  have hsinh : 255 / 512 * Real.exp x ≤ Real.sinh x := by
    rw [Real.sinh_eq]
    linarith
  have hsinh0 : 0 < Real.sinh x :=
    Real.sinh_pos_iff.mpr (lt_of_lt_of_le (by norm_num) hx)
  rw [div_le_iff₀ hsinh0]
  nlinarith

end NumberField.Odlyzko
