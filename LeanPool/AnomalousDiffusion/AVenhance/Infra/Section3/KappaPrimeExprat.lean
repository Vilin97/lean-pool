/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.KappaPrimeUniform
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.ExpratScaling
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ingredients.TimeScaleBounds
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ingredients.EpsilonConsequences
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Numeric.Exponents

/-! The corrected `4δ` exprat estimate for the auxiliary κ′ chain. -/

@[expose] public section

noncomputable section

namespace AVenhance.Infra.Section3

open AVenhance

theorem KappaPrimeExprat.epsilon_le_one_over_128 {β : ℝ} {Λ n : ℕ}
    (hβ : 1 < β) (hβ' : β < 4 / 3) (hΛ : 2 ^ 7 ≤ Λ)
    (hn : 1 ≤ n) :
    epsilon β Λ n ≤ (1 / 128 : ℝ) := by
  have he := Infra.Ingredients.epsilon_le_lambda_pow hβ hβ' hΛ (m := n)
  have hΛ128 : (128 : ℝ) ≤ (Λ : ℝ) := by exact_mod_cast hΛ
  have hexp : -(n : ℝ) ≤ 0 := neg_nonpos.mpr (Nat.cast_nonneg n)
  have hbase : (Λ : ℝ) ^ (-(n : ℝ)) ≤ (128 : ℝ) ^ (-(n : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) hΛ128 hexp
  have hexp' : -(n : ℝ) ≤ -1 := by exact_mod_cast (show -(n : ℤ) ≤ -1 by omega)
  have h128 : (128 : ℝ) ^ (-(n : ℝ)) ≤ (128 : ℝ) ^ (-1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp'
  have hinv : (128 : ℝ) ^ (-1 : ℝ) = 1 / 128 := by norm_num
  exact he.trans (hbase.trans (hinv ▸ h128))

/-- The exponent of the normalized diffusivity factor is nonnegative. -/
theorem two_sub_beta_gamma_nonneg {β : ℝ}
    (hβ : 1 < β) (hβ' : β < 4 / 3) :
    0 ≤ 2 - β - gamma β := by
  rw [Infra.Numeric.gamma_eq_beta_fraction hβ]
  have hden : 0 < 5 * β - 4 := by nlinarith
  have hnum : 0 ≤ (2 - β) * (5 * β - 4) - β * (4 - 3 * β) := by
    have hprod := mul_nonneg (sub_nonneg.mpr (by linarith : β ≤ 4))
      (sub_nonneg.mpr (by linarith : 1 ≤ β))
    nlinarith only [hprod]
  rw [sub_nonneg]
  apply (div_le_iff₀ hden).2
  nlinarith only [hnum]

/-- Positivity of the normalization constant used in the uniform κ′ bounds. -/
theorem kappaPrimeUniformConstant_pos {β : ℝ}
    (hβ : 1 < β) (hβ' : β < 4 / 3) :
    0 < kappaPrimeUniformConstant β := by
  have hqpos : 0 < q β := lt_trans (by norm_num : (0 : ℝ) < 1)
    (Infra.Ingredients.one_lt_q hβ hβ')
  have hsupergeo : 0 ≤ Infra.Ingredients.supergeoConstant β := by
    dsimp [Infra.Ingredients.supergeoConstant]
    exact mul_nonneg (mul_nonneg (by norm_num) hqpos.le) (Real.exp_nonneg _)
  have herr : 0 ≤ kappaPrimeRatioError β := by
    dsimp [kappaPrimeRatioError]
    exact add_nonneg (mul_nonneg (by norm_num) hsupergeo)
      (div_nonneg (sq_nonneg _) (by norm_num))
  have hγ := Infra.Ingredients.gamma_pos hβ hβ'
  have hρ : (128 : ℝ) ^ (-2 * gamma β) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by nlinarith)
  have hden : 0 < 1 - (128 : ℝ) ^ (-2 * gamma β) := sub_pos.mpr hρ
  have hend : 0 < kappaPrimeEndpointConstant β := by
    have hleft : 0 < (1 + kappaPrimeRatioError β / 128) *
        (2 + 2 * (9 / 80)) := by positivity
    exact lt_of_lt_of_le hleft (le_max_left _ _)
  unfold kappaPrimeUniformConstant
  exact mul_pos hend (Real.exp_pos _)

/-- Uniform corrected `4δ` bounds for the κ′ exprat on `2 ≤ m < M`.
The constants depend only on β. -/
theorem kappaPrimeAt_exprat_bounds {β : ℝ} {Λ M : ℕ}
    (hβ : 1 < β) (hβ' : β < 4 / 3) (hΛ : 2 ^ 7 ≤ Λ)
    {κ : ℝ} (hκ : 0 < κ)
    (hpermitted : κ ∈ permittedInterval β Λ M)
    {m : ℕ} (hm : 2 ≤ m) (hmM : m < M) :
    let U := kappaPrimeUniformConstant β
    let clo := ((1 / 2 : ℝ) ^ (2 - β - gamma β)) /
      (U * (2 : ℝ) ^ (-28 : ℤ))
    let chi := (1 + Infra.Ingredients.supergeoConstant β / 128) ^
      (2 - β - gamma β) /
      ((9 / 80 / U) * (2 : ℝ) ^ (-33 : ℤ))
    clo * epsilon β Λ (m - 1) ^ (4 * delta β) ≤
        epsilon β Λ m ^ 2 /
          (kappaPrimeAt β Λ κ m (M - m) * tau β Λ m) ∧
      epsilon β Λ m ^ 2 /
          (kappaPrimeAt β Λ κ m (M - m) * tau β Λ m) ≤
        chi * epsilon β Λ (m - 1) ^ (4 * delta β) := by
  dsimp only
  let e := epsilon β Λ m
  let ep := epsilon β Λ (m - 1)
  let U := kappaPrimeUniformConstant β
  let clo := ((1 / 2 : ℝ) ^ (2 - β - gamma β)) /
    (U * (2 : ℝ) ^ (-28 : ℤ))
  let chi := (1 + Infra.Ingredients.supergeoConstant β / 128) ^
    (2 - β - gamma β) /
    ((9 / 80 / U) * (2 : ℝ) ^ (-33 : ℤ))
  have he : 0 < e := by dsimp [e]; exact Infra.Cutoff.epsilon_pos hβ hβ' hΛ
  have hep : 0 < ep := by dsimp [ep]; exact Infra.Cutoff.epsilon_pos hβ hβ' hΛ
  have htime := Infra.Ingredients.tau_bounds hβ hβ' hΛ (by omega : 1 ≤ m)
  have htimeLo : (2 : ℝ) ^ (-33 : ℤ) * ep ^
      (2 - β + 4 * delta β) ≤ tau β Λ m := by
    simpa [ep] using htime.1
  have htimeHi : tau β Λ m ≤ (2 : ℝ) ^ (-28 : ℤ) * ep ^
      (2 - β + 4 * delta β) := by
    simpa [ep] using htime.2
  have hmScale : m - 1 + 1 = m := by omega
  have hsuper := Infra.Ingredients.epsilon_supergeo hβ hβ' hΛ
    (m := m - 1) (by omega : 1 ≤ m - 1)
  rw [hmScale] at hsuper
  have hepSmall : ep ≤ 1 / 128 := by
    dsimp [ep]
    exact KappaPrimeExprat.epsilon_le_one_over_128 hβ hβ' hΛ (by omega : 1 ≤ m - 1)
  have hscaleLo : (1 / 2 : ℝ) * ep ^ q β ≤ e := by
    have hfac : (1 / 2 : ℝ) ≤ 1 - 10 * ep := by nlinarith [hepSmall]
    have hpow : 0 ≤ ep ^ q β := Real.rpow_nonneg hep.le _
    dsimp [e, ep]
    exact le_trans (mul_le_mul_of_nonneg_right hfac hpow) hsuper.1
  have hscaleHi : e ≤ (1 + Infra.Ingredients.supergeoConstant β / 128) *
      ep ^ q β := by
    have hS : 0 ≤ Infra.Ingredients.supergeoConstant β := by
      dsimp [Infra.Ingredients.supergeoConstant]
      have hqpos : 0 < q β := lt_trans (by norm_num : (0 : ℝ) < 1)
        (Infra.Ingredients.one_lt_q hβ hβ')
      exact mul_nonneg (mul_nonneg (by norm_num) hqpos.le) (Real.exp_nonneg _)
    have hfac : 1 + Infra.Ingredients.supergeoConstant β * ep ≤
        1 + Infra.Ingredients.supergeoConstant β / 128 := by
      nlinarith [mul_le_mul_of_nonneg_left hepSmall hS]
    have hpow : 0 ≤ ep ^ q β := Real.rpow_nonneg hep.le _
    calc
      e ≤ (1 + Infra.Ingredients.supergeoConstant β * ep) * ep ^ q β := by
        dsimp [e, ep]
        exact hsuper.2
      _ ≤ _ := mul_le_mul_of_nonneg_right hfac hpow
  have hprime := kappaPrimeAt_uniform_bounds hβ hβ' hΛ hκ hpermitted
    (by omega : 1 ≤ m) hmM
  have hκprimePos : 0 < kappaPrimeAt β Λ κ m (M - m) := by
    exact kappaPrimeAt_pos hβ hβ' hΛ hκ m (M - m)
  have hscaleEq : e ^ (β + gamma β) =
      a β Λ m * e ^ (2 + gamma β) := by
    change e ^ (β + gamma β) = e ^ (β - 2) * e ^ (2 + gamma β)
    rw [← Real.rpow_add he]
    congr 1
    ring
  have hkappaLo :
      (9 / 80 / U) * e ^ (β + gamma β) ≤
        kappaPrimeAt β Λ κ m (M - m) := by
    rw [hscaleEq]
    simpa [U] using hprime.1
  have hkappaHi :
      kappaPrimeAt β Λ κ m (M - m) ≤ U * e ^ (β + gamma β) := by
    rw [hscaleEq]
    simpa [U] using hprime.2
  have hκprimeLoPos : 0 < 9 / 80 / U := by
    exact div_pos (by norm_num) (kappaPrimeUniformConstant_pos hβ hβ')
  have hκprimeHiPos : 0 < U := by
    exact kappaPrimeUniformConstant_pos hβ hβ'
  have hp := two_sub_beta_gamma_nonneg hβ hβ'
  have hτpos : 0 < tau β Λ m :=
    lt_of_lt_of_le (mul_pos (zpow_pos (by norm_num : (0 : ℝ) < 2) _)
      (Real.rpow_pos_of_pos hep _)) htimeLo
  have hsupergeo : 0 ≤ Infra.Ingredients.supergeoConstant β := by
    dsimp [Infra.Ingredients.supergeoConstant]
    have hqpos : 0 < q β := lt_trans (by norm_num : (0 : ℝ) < 1)
      (Infra.Ingredients.one_lt_q hβ hβ')
    exact mul_nonneg (mul_nonneg (by norm_num) hqpos.le) (Real.exp_nonneg _)
  have hresult := exprat_bounds_of_normalized_kappa
    (β := β) (e := e) (eprev := ep) (τ := tau β Λ m)
    (κm := kappaPrimeAt β Λ κ m (M - m))
    (aLo := 1 / 2) (aHi := 1 + Infra.Ingredients.supergeoConstant β / 128)
    (tauLo := (2 : ℝ) ^ (-33 : ℤ)) (tauHi := (2 : ℝ) ^ (-28 : ℤ))
    (kappaLo := 9 / 80 / U) (kappaHi := U)
    hβ he hep hτpos hκprimePos
    (by norm_num) (by positivity)
    (zpow_pos (by norm_num : (0 : ℝ) < 2) _)
    (zpow_pos (by norm_num : (0 : ℝ) < 2) _) hκprimeLoPos hκprimeHiPos hp
    hscaleLo hscaleHi htimeLo htimeHi hkappaLo hkappaHi
  have hclo : clo = ((1 / 2 : ℝ) ^ (2 - β - gamma β)) /
      (U * (2 : ℝ) ^ (-28 : ℤ)) := rfl
  have hchi : chi =
      (1 + Infra.Ingredients.supergeoConstant β / 128) ^
        (2 - β - gamma β) /
        ((9 / 80 / U) * (2 : ℝ) ^ (-33 : ℤ)) := rfl
  simpa [clo, chi, hclo, hchi, U] using hresult

end AVenhance.Infra.Section3

end
