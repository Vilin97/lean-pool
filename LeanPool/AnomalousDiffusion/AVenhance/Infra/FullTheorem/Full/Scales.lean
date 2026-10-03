/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.LimitSeries
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Ingredients.Q

/-! # The diffusivity scales `κ_j = ε_{j+1}^p`

Abstract-real facts used to produce the sequence `κ_j` of the combined main theorem:
the exponent `p = 2β/(qβ+1)` is positive, and `4 ε_{m+1}^p < ε_m^p` once `Λ ≥ 5^{1/p}`. -/

@[expose] public section

open Filter Topology

noncomputable section

namespace AVenhance.Infra.FullTheorem.Full

open AVenhance

/-- The exponent `2β/(qβ+1)` is positive for `1 < β < 4/3`. -/
theorem permitted_exponent_pos {β : ℝ} (h1 : 1 < β) (h2 : β < 4 / 3) :
    0 < 2 * β / (q β + 1) := by
  have hq : 0 < q β := by
    unfold q
    have : 0 < β - 1 := by linarith
    have : 0 < 2 - β := by linarith
    positivity
  have : 0 < β := by linarith
  positivity

/-- `Λ ≥ 5^{1/p}` implies `Λ^p ≥ 5`. -/
theorem five_le_rpow {p L : ℝ} (hp : 0 < p) (hL : (5 : ℝ) ^ (1 / p) ≤ L) : 5 ≤ L ^ p := by
  have h0 : (0 : ℝ) ≤ 5 ^ (1 / p) := by positivity
  have h := Real.rpow_le_rpow h0 hL hp.le
  rwa [← Real.rpow_mul (by norm_num), one_div, inv_mul_cancel₀ hp.ne', Real.rpow_one] at h

/-- The four-fold gap `4 ε_{m+1}^p < ε_m^p`. -/
theorem four_mul_epsilon_rpow_lt {β p : ℝ} (I : Ingredients β) (hp : 0 < p)
    (hΛ : (5 : ℝ) ^ (1 / p) ≤ (I.Λ : ℝ)) (m : ℕ) :
    4 * epsilon β I.Λ (m + 1) ^ p < epsilon β I.Λ m ^ p := by
  have hstep := Infra.Construction.epsilon_rpow_step_le I hp m
  have hpos : 0 < epsilon β I.Λ m ^ p := by
    have := Infra.Cutoff.epsilon_pos (Λ := I.Λ) (m := m) I.one_lt_beta I.beta_lt
      I.two_pow_seven_le
    positivity
  have hΛ0 : (0 : ℝ) < I.Λ := by
    have : (128 : ℝ) ≤ I.Λ := by exact_mod_cast I.two_pow_seven_le
    linarith
  have h5 := five_le_rpow hp hΛ
  have hneg : (I.Λ : ℝ) ^ (-p) ≤ 1 / 5 := by
    rw [Real.rpow_neg hΛ0.le, ← one_div]
    exact one_div_le_one_div_of_le (by norm_num) h5
  have h2 : epsilon β I.Λ m ^ p * (I.Λ : ℝ) ^ (-p) ≤ epsilon β I.Λ m ^ p * (1 / 5) :=
    mul_le_mul_of_nonneg_left hneg hpos.le
  linarith

end AVenhance.Infra.FullTheorem.Full
