/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesDischargeDiffusivity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesMean

/-! # Iterates Discharge Chain

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
namespace AVenhance.Infra.Section4
open AVenhance

/-- The explicit E21c TWO-error mean comparison has the required rho scale. -/
theorem iterate_chain_mean_scale {β Ccut P κ : ℝ} (I : Ingredients β)
    (hz : I.Czeta ≤ Ccut) (hh : I.Chat ≤ Ccut) (hP : 0 ≤ P)
    {m M : ℕ} (hm : 1 ≤ m) (hκ : 0 < κ)
    (hratio : epsilon β I.Λ m ^ 2 / (I.kappaAt κ m (M - m) * tau β I.Λ m) ≤
      P * epsilon β I.Λ (m - 1) ^ (2 * delta β))
    (hsize : I.kappaAt κ m (M - m) +
      a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / I.kappaAt κ m (M - m) ≤
      (160 / 9) * I.kappaAt κ (m - 1) (M - (m - 1))) :
    iterateMeanErrorBound I (I.kappaAt κ m (M - m)) m ≤
      I.kappaAt κ (m - 1) (M - (m - 1)) * iterateMeanScaleConstant β Ccut P *
        epsilon β I.Λ (m - 1) ^ (2 * delta β) := by
  have hk := Infra.Section3.kappaAt_pos I hκ m (M - m)
  have hkp := Infra.Section3.kappaAt_pos I hκ (m - 1) (M - (m - 1))
  have hz0 : 0 ≤ I.Czeta := by linarith only [I.one_le_Czeta]
  have hh0 : 0 ≤ I.Chat := by linarith only [I.one_le_Chat]
  have hcut : 0 ≤ Ccut := hz0.trans hz
  have hA : 4 * Real.pi ^ 2 * I.Czeta * Nstar β * 2 ^ Nstar β ≤
      4 * Real.pi ^ 2 * Ccut * Nstar β * 2 ^ Nstar β := by gcongr
  have hD : 2 * Nstar β * I.Czeta * ((Nstar β).factorial : ℝ) *
      2 ^ Nstar β * 2 ^ Nstar β * I.Chat ^ 2 * 8 ^ Nstar β ≤
      2 * Nstar β * Ccut * ((Nstar β).factorial : ℝ) *
      2 ^ Nstar β * 2 ^ Nstar β * Ccut ^ 2 * 8 ^ Nstar β := by gcongr
  have hB : 0 ≤ a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / I.kappaAt κ m (M - m) := by positivity
  have hBsize : a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / I.kappaAt κ m (M - m) ≤
      (160 / 9) * I.kappaAt κ (m - 1) (M - (m - 1)) := by linarith only [hsize, hk.le]
  have he := Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m - 1)
  have he1 := Infra.Construction.epsilon_le_one I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m
      - 1)
  have hn : 2 ≤ Nstar β := by
    have ht := Infra.Ingredients.Nstar_ge_256 I.one_lt_beta I.beta_lt
    omega
  have ht := (time_ratio_bounds I.one_lt_beta I.beta_lt I.two_pow_seven_le hm).2
  have hr0 : 0 ≤ epsilon β I.Λ m ^ 2 / (I.kappaAt κ m (M - m) * tau β I.Λ m) :=
    div_nonneg (sq_nonneg _) (mul_nonneg hk.le (I.tau_pos' m).le)
  have ht0 : 0 ≤ tau β I.Λ m / tauP β I.Λ m :=
    div_nonneg (I.tau_pos' m).le
      (Infra.Cutoff.tauP_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le).le
  have herr := iterate_two_error_mean_scale he he1
    (Infra.Ingredients.delta_pos I.one_lt_beta I.beta_lt) hn hkp.le
    (by positivity : 0 ≤ 4 * Real.pi ^ 2 * Ccut * Nstar β * 2 ^ Nstar β)
    (by positivity : 0 ≤ 2 * Nstar β * Ccut * ((Nstar β).factorial : ℝ) *
      2 ^ Nstar β * 2 ^ Nstar β * Ccut ^ 2 * 8 ^ Nstar β) hP
    hr0 hratio ht0 ht hBsize
  apply le_trans _ herr
  unfold iterateMeanErrorBound
  apply mul_le_mul_of_nonneg_left _ hB
  exact add_le_add (mul_le_mul_of_nonneg_right hA (pow_nonneg hr0 _))
    (mul_le_mul_of_nonneg_right hD (pow_nonneg ht0 _))

end AVenhance.Infra.Section4
