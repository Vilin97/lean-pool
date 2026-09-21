/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section51.SmallWidetildeEntry

/-! # Exponent Absorption -/

namespace Homogenization
namespace Book
namespace Ch05
namespace Section51

noncomputable section

/-!
# Exponent absorption for the main annealed convergence theorem

This file contains the pure real-arithmetic step which turns a bound with a
fixed prefactor into the note-facing bound with unit prefactor, after shrinking
the algebraic exponent.
-/

theorem quarter_le_rpow_three_neg_mul_of_mul_nat_le_one
    {α : ℝ} {n : ℕ} (hαn : α * (n : ℝ) ≤ 1) :
    (1 / 4 : ℝ) ≤ Real.rpow (3 : ℝ) (-α * (n : ℝ)) := by
  have hmono :
      Real.rpow (3 : ℝ) (-(1 : ℝ)) ≤
        Real.rpow (3 : ℝ) (-α * (n : ℝ)) := by
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) ?_
    nlinarith
  have hthird : Real.rpow (3 : ℝ) (-(1 : ℝ)) = (1 / 3 : ℝ) := by
    calc
      Real.rpow (3 : ℝ) (-(1 : ℝ)) =
          Real.exp (Real.log (3 : ℝ) * (-(1 : ℝ))) := by
            simpa using
              (Real.rpow_def_of_pos (x := (3 : ℝ)) (y := -(1 : ℝ))
                (by norm_num : 0 < (3 : ℝ)))
      _ = (1 / 3 : ℝ) := by
            rw [mul_neg, mul_one, Real.exp_neg, Real.exp_log (by norm_num : 0 < (3 : ℝ))]
            norm_num
  calc
    (1 / 4 : ℝ) ≤ 1 / 3 := by norm_num
    _ = Real.rpow (3 : ℝ) (-(1 : ℝ)) := hthird.symm
    _ ≤ Real.rpow (3 : ℝ) (-α * (n : ℝ)) := hmono

theorem prefactor_decay_le_half_exponent_decay_of_large
    {α₀ K : ℝ} {n : ℕ}
    (hα₀ : 0 < α₀)
    (hlarge :
      Real.log (max (4 * K) 1) / ((α₀ / 2) * Real.log 3) ≤ (n : ℝ)) :
    4 * K * Real.rpow (3 : ℝ) (-α₀ * (n : ℝ)) ≤
      Real.rpow (3 : ℝ) (-(α₀ / 2) * (n : ℝ)) := by
  let A : ℝ := max (4 * K) 1
  let γ : ℝ := α₀ / 2
  have hγ_pos : 0 < γ := by dsimp [γ]; positivity
  have hlog3 : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
  have hden_pos : 0 < γ * Real.log 3 := mul_pos hγ_pos hlog3
  have hA_ge_pref : 4 * K ≤ A := by
    dsimp [A]
    exact le_max_left _ _
  have hA_ge_one : 1 ≤ A := by
    dsimp [A]
    exact le_max_right _ _
  have hA_pos : 0 < A := lt_of_lt_of_le zero_lt_one hA_ge_one
  have hlog_le : Real.log A ≤ γ * Real.log 3 * (n : ℝ) := by
    have hmul := (div_le_iff₀ hden_pos).mp (by simpa [A, γ] using hlarge)
    nlinarith
  have hA_le_rpow : A ≤ Real.rpow (3 : ℝ) (γ * (n : ℝ)) := by
    have hexp : A ≤ Real.exp (γ * Real.log 3 * (n : ℝ)) :=
      (Real.log_le_iff_le_exp hA_pos).mp hlog_le
    have hrpow :
        Real.rpow (3 : ℝ) (γ * (n : ℝ)) =
          Real.exp (γ * Real.log 3 * (n : ℝ)) := by
      calc
        Real.rpow (3 : ℝ) (γ * (n : ℝ)) =
            Real.exp (Real.log (3 : ℝ) * (γ * (n : ℝ))) := by
              simpa using
                (Real.rpow_def_of_pos (x := (3 : ℝ)) (y := γ * (n : ℝ))
                  (by norm_num : 0 < (3 : ℝ)))
        _ = Real.exp (γ * Real.log 3 * (n : ℝ)) := by
              congr 1
              ring
    rw [hrpow]
    exact hexp
  have hdecay_nonneg : 0 ≤ Real.rpow (3 : ℝ) (-α₀ * (n : ℝ)) :=
    Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _
  calc
    4 * K * Real.rpow (3 : ℝ) (-α₀ * (n : ℝ))
        ≤ Real.rpow (3 : ℝ) (γ * (n : ℝ)) *
            Real.rpow (3 : ℝ) (-α₀ * (n : ℝ)) := by
          exact mul_le_mul_of_nonneg_right (hA_ge_pref.trans hA_le_rpow) hdecay_nonneg
    _ = Real.rpow (3 : ℝ) (γ * (n : ℝ) + -α₀ * (n : ℝ)) := by
          exact (Real.rpow_add (by norm_num : 0 < (3 : ℝ))
            (γ * (n : ℝ)) (-α₀ * (n : ℝ))).symm
    _ = Real.rpow (3 : ℝ) (-(α₀ / 2) * (n : ℝ)) := by
          congr 1
          dsimp [γ]
          ring

theorem mul_nat_le_one_of_le_inverse_succ
    {α : ℝ} {R n : ℕ}
    (hα : α ≤ ((R + 1 : ℕ) : ℝ)⁻¹) (hn : n ≤ R) :
    α * (n : ℝ) ≤ 1 := by
  have hn_nonneg : 0 ≤ (n : ℝ) := by positivity
  have hR_pos : 0 < ((R + 1 : ℕ) : ℝ) := by positivity
  have hn_le_Rsucc : (n : ℝ) ≤ ((R + 1 : ℕ) : ℝ) := by
    exact_mod_cast (hn.trans (Nat.le_succ R))
  calc
    α * (n : ℝ) ≤ ((R + 1 : ℕ) : ℝ)⁻¹ * (n : ℝ) :=
      mul_le_mul_of_nonneg_right hα hn_nonneg
    _ = (n : ℝ) / ((R + 1 : ℕ) : ℝ) := by ring
    _ ≤ 1 := (div_le_one hR_pos).mpr hn_le_Rsucc

end

end Section51
end Ch05
end Book
end Homogenization
