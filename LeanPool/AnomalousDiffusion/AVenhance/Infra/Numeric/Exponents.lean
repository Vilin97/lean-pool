/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ingredients.Parameters

/-! Pure real algebra for the exponents in §§5.2–5.4. No scale powers are expanded.
The printed `γβ` at line 7441 must be `qγ`. -/

@[expose] public section

namespace AVenhance.Infra.Numeric

open AVenhance.Infra.Ingredients

/-- The gamma as a rational function of beta. -/
theorem gamma_eq_beta_fraction {β : ℝ} (hβ : 1 < β) :
    AVenhance.gamma β = β * (4 - 3 * β) / (5 * β - 4) := by
  unfold AVenhance.gamma
  rw [q_eq_beta_div_four_sub_one hβ]
  have h1 : β - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hβ)
  have h2 : 5 * β - 4 ≠ 0 := by linarith
  field_simp [h1, h2]
  ring

/-- The delta as a rational function of beta. -/
theorem delta_eq_beta_fraction {β : ℝ} (hβ : 1 < β) :
    AVenhance.delta β = (4 - 3 * β) ^ 2 / (16 * (5 * β - 4)) := by
  unfold AVenhance.delta
  rw [q_eq_beta_div_four_sub_one hβ]
  have h1 : β - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hβ)
  have h2 : 5 * β - 4 ≠ 0 := by linarith
  have h3 : -4 + β * 5 ≠ 0 := by linarith
  field_simp [h1, h2, h3]
  ring_nf
  field_simp [h1, h2, h3]
  ring

/-- The corrected `s6.exponent.8delta`: the decrement is eight delta. -/
theorem eight_delta_identity {β : ℝ} (hβ : 1 < β) :
    (2 - β) * (AVenhance.q β - 1) - AVenhance.q β * AVenhance.gamma β =
      8 * AVenhance.delta β := by
  rw [q_eq_beta_div_four_sub_one hβ, gamma_eq_beta_fraction hβ,
    delta_eq_beta_fraction hβ]
  have h1 : β - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hβ)
  have h2 : 5 * β - 4 ≠ 0 := by linarith
  have h3 : -4 + β * 5 ≠ 0 := by linarith
  field_simp [h1, h2, h3]
  ring_nf
  field_simp [h1, h2, h3]
  ring

/-- `e.put.pipe.smoke.it` and the initial-defect exponent. -/
theorem four_delta_identity {β : ℝ} (hβ : 1 < β) :
    AVenhance.q β * (1 - AVenhance.gamma β) - 1 - AVenhance.gamma β / 2 =
      4 * AVenhance.delta β := by
  rw [q_eq_beta_div_four_sub_one hβ, gamma_eq_beta_fraction hβ,
    delta_eq_beta_fraction hβ]
  have h1 : β - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hβ)
  have h2 : 5 * β - 4 ≠ 0 := by linarith
  have h3 : -4 + β * 5 ≠ 0 := by linarith
  field_simp [h1, h2, h3]
  ring_nf
  field_simp [h1, h2, h3]
  ring

/-- Re-export the existing parameter estimate needed by the error bounds. -/
theorem gamma_ge_four_delta {β : ℝ} (hβ : 1 < β) (hβ' : β < 4 / 3) :
    4 * AVenhance.delta β ≤ AVenhance.gamma β :=
  four_delta_le_gamma hβ hβ'

/-- The extra derivative is compensated by a strictly positive scale exponent. -/
theorem kill_half_gamma {β : ℝ} (hβ : 1 < β) (hβ' : β < 4 / 3) :
    0 < AVenhance.q β - 1 - AVenhance.gamma β / 2 := by
  have hd := delta_pos hβ hβ'
  have hg := gamma_pos hβ hβ'
  have hq := one_lt_q hβ hβ'
  have hi := four_delta_identity hβ
  have hp := mul_pos (lt_trans (by norm_num) hq) hg
  nlinarith only [hd, hi, hp]

/-- `Nstar` supplies the actual exponent budget used in §5.2. -/
theorem Nstar_exponent_budget {β : ℝ} (hβ : 1 < β) (hβ' : β < 4 / 3) :
    8 * AVenhance.delta β + 4 * (AVenhance.q β - 1) *
      (β + AVenhance.gamma β) ≤ AVenhance.delta β * (AVenhance.Nstar β : ℝ) := by
  have hd := delta_pos hβ hβ'
  have h := mul_le_mul_of_nonneg_left (Nstar_ge_requirement hβ hβ') hd.le
  field_simp [ne_of_gt hd] at h
  nlinarith only [h]

end AVenhance.Infra.Numeric
