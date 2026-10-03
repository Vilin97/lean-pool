/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesDischargeChain

/-! # Iterates Discharge Bounds

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
namespace AVenhance.Infra.Section4
open AVenhance

/-- Uniform ratio coefficient, covering the interior diffusivity-recursion estimate and the
    terminal step. -/
def iterateRatioConstant (β Ck : ℝ) : ℝ :=
  max 1 (max Ck (Infra.Section3.kappaPrimeEndpointExpratConstant β))

/-- The coefficient smallness threshold is fixed before choosing ingredients. -/
def iterateDischargeThreshold (β Ccut Ck : ℝ) : ℝ :=
  smallnessBudget 0 (iterateRatioConstant β Ck)
    (max 0 (Infra.Section3.lAmtOneStepConstant β Ccut))

/-- The zeroth Kmat entry coefficient after one-step enhancement. -/
def iterateKmatConstant (β Ccut : ℝ) : ℝ :=
  (160 / 9) * (1 + (Nstar β : ℝ) * Ccut)

/-- Package the three cheap inputs of the actual T upgrade. The diffusivity-recursion ratio
premise is stated explicitly here. -/
theorem iterate_chain_upgrade_inputs {β Ccut Ck C₀ κ : ℝ} (I : Ingredients β)
    (hz : I.Czeta ≤ Ccut) (hh : I.Chat ≤ Ccut)
    {m M : ℕ} (hm : 2 ≤ m) (hmM : m ≤ M) (hκ : 0 < κ)
    (hPerm : κ ∈ permittedInterval β I.Λ M) (hCk : 0 ≤ Ck)
    (hC₀ : 1 ≤ C₀) (hthreshold : iterateDischargeThreshold β Ccut Ck ≤ C₀)
    (hsmall : epsilon β I.Λ (m - 1) ^ (2 * delta β) ≤ (4 * C₀ ^ 3)⁻¹)
    (hA5 : ∀ j : ℕ, 2 ≤ j → j < M →
      epsilon β I.Λ j ^ 2 / (I.kappaAt κ j (M - j) * tau β I.Λ j) ≤
        Ck * epsilon β I.Λ (j - 1) ^ (4 * delta β)) :
    (∀ t j k, |I.Kmat (I.kappaAt κ m (M - m)) m t j k| ≤
      iterateKmatConstant β Ccut * I.kappaAt κ (m - 1) (M - (m - 1))) ∧
    epsilon β I.Λ m ^ 2 ≤ I.kappaAt κ m (M - m) * tau β I.Λ m / 2 ∧
    iterateMeanErrorBound I (I.kappaAt κ m (M - m)) m ≤
      I.kappaAt κ (m - 1) (M - (m - 1)) *
        iterateMeanScaleConstant β Ccut (iterateRatioConstant β Ck) *
          epsilon β I.Λ (m - 1) ^ (2 * delta β) := by
  let P := iterateRatioConstant β Ck
  let L := max 0 (Infra.Section3.lAmtOneStepConstant β Ccut)
  have hP1 : 1 ≤ P := le_max_left _ _
  have hP : 0 ≤ P := by linarith only [hP1]
  have hPk : Ck ≤ P := (le_max_left _ _).trans (le_max_right _ _)
  have hPt : Infra.Section3.kappaPrimeEndpointExpratConstant β ≤ P :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hL : 0 ≤ L := le_max_left _ _
  have hr := iterate_chain_ratio_bound I hCk hPk hPt hm hmM hκ hPerm hA5
  have he := Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m - 1)
  have he1 := Infra.Construction.epsilon_le_one I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m
      - 1)
  have hd := Infra.Ingredients.delta_pos I.one_lt_beta I.beta_lt
  have hx : 0 ≤ epsilon β I.Λ (m - 1) ^ delta β := Real.rpow_nonneg he.le _
  have hx1 : epsilon β I.Λ (m - 1) ^ delta β ≤ 1 :=
    Real.rpow_le_one he.le he1 hd.le
  have hρeq : (epsilon β I.Λ (m - 1) ^ delta β) ^ 2 =
      epsilon β I.Λ (m - 1) ^ (2 * delta β) := by
    rw [← Real.rpow_mul_natCast he.le]
    congr 1
    ring
  have hD : 0 < iterateDischargeThreshold β Ccut Ck := by
    unfold iterateDischargeThreshold smallnessBudget
    positivity
  have hs := iterate_discharge_threshold_from_source hC₀ hD hthreshold hsmall
  rw [← hρeq] at hr hs
  have hb := iterate_discharge_smallness hx hx1 hP hL hr hs
  have hk := Infra.Section3.kappaAt_pos I hκ m (M - m)
  have hden := mul_pos hk (I.tau_pos' m)
  have hcondition : epsilon β I.Λ m ^ 2 ≤ I.kappaAt κ m (M - m) * tau β I.Λ m / 2 := by
    have ht := (div_le_iff₀ hden).mp hb.1
    linarith only [ht]
  have hsum : 0 ≤ epsilon β I.Λ m ^ 2 / (I.kappaAt κ m (M - m) * tau β I.Λ m) +
      epsilon β I.Λ (m - 1) ^ delta β := by positivity
  have herror := (mul_le_mul_of_nonneg_right (le_max_right 0
    (Infra.Section3.lAmtOneStepConstant β Ccut)) hsum).trans hb.2
  have hsize := iterate_chain_step_size I hz hh (by omega) hmM hκ herror
  exact ⟨iterate_chain_Kmat_entry_bound I hz (by omega) hκ hcondition hsize,
    hcondition, iterate_chain_mean_scale I hz hh hP (by omega) hκ
      (iterate_chain_ratio_bound I hCk hPk hPt hm hmM hκ hPerm hA5) hsize⟩

end AVenhance.Infra.Section4
