/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.LRecurse
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.KappaSeq
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.OneStepAveragingUnconditional
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.LRecurseTop
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Params

/-! contract 8: the enhancement product bound, including the terminal step.
Constants are selected before the ingredients; no temperature datum occurs. -/

@[expose] public section

noncomputable section
namespace AVenhance.Infra.Section5.RelativeError
open AVenhance

theorem KappaProduct.epsilon_delta_le_inverse {β R : ℝ} (I : Ingredients β)
    (hR : 1 ≤ R) (hΛ : R ^ (delta β)⁻¹ ≤ (I.Λ : ℝ))
    {j : ℕ} (hj : 1 ≤ j) : epsilon β I.Λ j ^ delta β ≤ R⁻¹ := by
  have hd := Infra.Ingredients.delta_pos I.one_lt_beta I.beta_lt
  have hΛ1 : (1 : ℝ) ≤ (I.Λ : ℝ) := by
    exact_mod_cast (show 1 ≤ I.Λ by have := I.two_pow_seven_le; omega)
  have hΛpos : (0 : ℝ) < (I.Λ : ℝ) := lt_of_lt_of_le zero_lt_one hΛ1
  have hε := Infra.Ingredients.epsilon_le_lambda_pow
    I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := j)
  have hexp : -(j : ℝ) ≤ (-1 : ℝ) := by
    have hjr : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    linarith only [hjr]
  have hbase := Real.rpow_le_rpow_of_exponent_le hΛ1 hexp
  have hpow := Real.rpow_le_rpow
    (Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le).le
    (hε.trans hbase) hd.le
  have hRpow := Real.rpow_le_rpow (Real.rpow_nonneg (by linarith : 0 ≤ R) _)
    hΛ hd.le
  rw [Real.rpow_inv_rpow (by linarith : 0 ≤ R) hd.ne'] at hRpow
  calc
    epsilon β I.Λ j ^ delta β ≤ ((I.Λ : ℝ) ^ (-1 : ℝ)) ^ delta β := hpow
    _ = ((I.Λ : ℝ) ^ delta β)⁻¹ := by
      rw [← Real.rpow_mul hΛpos.le, neg_one_mul, Real.rpow_neg hΛpos.le]
    _ ≤ R⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le (by linarith : 0 < R) hRpow

theorem KappaProduct.averaging_small_of_inverse {L P e : ℝ}
    (hL : 0 ≤ L) (hP : 0 ≤ P) (he : 0 ≤ e)
    (hsmall : e ≤ (1 + (160 / 9) * L * (P + 1))⁻¹) :
    L * (P * e ^ 2 + e) ≤ 9 / 160 := by
  let R := 1 + (160 / 9) * L * (P + 1)
  have hR : 1 ≤ R := by
    have ht : 0 ≤ (160 / 9 : ℝ) * L * (P + 1) := by positivity
    dsimp [R]
    linarith only [ht]
  have he1 : e ≤ 1 := hsmall.trans ((inv_le_one₀ (by linarith : 0 < R)).mpr hR)
  have hesq : e ^ 2 ≤ e := by nlinarith only [mul_nonneg he (sub_nonneg.mpr he1)]
  have hRe : R * e ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left hsmall (by linarith : 0 ≤ R)
    simpa only [R, mul_inv_cancel₀ (by positivity : (1 + (160 / 9) * L * (P + 1)) ≠ 0)] using hh
  have hh := mul_le_mul_of_nonneg_left hesq hP
  have hh' := mul_le_mul_of_nonneg_left hh hL
  dsimp only [R] at hRe
  nlinarith only [hRe, hh', he]

end AVenhance.Infra.Section5.RelativeError
