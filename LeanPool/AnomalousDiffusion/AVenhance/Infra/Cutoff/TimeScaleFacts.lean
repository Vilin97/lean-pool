/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Ingredients.Ingredients

/-! Positivity and spacing facts for the time scales. -/

@[expose] public section

noncomputable section

namespace AVenhance.Infra.Cutoff

theorem q_eq_beta_div_four_sub_one {β : ℝ} (hβ : 1 < β) :
    AVenhance.q β = β / (4 * (β - 1)) := by
  unfold AVenhance.q
  field_simp [ne_of_gt (sub_pos.mpr hβ)]
  ring

theorem q_gt_one {β : ℝ} (hβ : 1 < β) (hβ' : β < 4 / 3) : 1 < AVenhance.q β := by
  rw [q_eq_beta_div_four_sub_one hβ]
  rw [lt_div_iff₀ (by positivity : 0 < 4 * (β - 1))]
  nlinarith

theorem delta_pos {β : ℝ} (hβ : 1 < β) (hβ' : β < 4 / 3) :
    0 < AVenhance.delta β := by
  have hq : 1 < AVenhance.q β := q_gt_one hβ hβ'
  have hqden : 0 < 2 * AVenhance.q β + 2 := by positivity
  have hfactor : 0 < 1 -
      ((2 * AVenhance.q β + 1) / (2 * AVenhance.q β + 2)) * β := by
    have hqform := q_eq_beta_div_four_sub_one hβ
    have hnum : (2 * AVenhance.q β + 1) * β < 2 * AVenhance.q β + 2 := by
      rw [hqform]
      have hden : 0 < 4 * (β - 1) := by positivity
      have hβm1 : 0 < β - 1 := sub_pos.mpr hβ
      field_simp [ne_of_gt hden, ne_of_gt hβm1]
      have hβm1' : 0 < β - 1 := sub_pos.mpr hβ
      have hfour : 0 < 4 - 3 * β := by linarith
      have hprod := mul_pos hβm1' hfour
      nlinarith [hprod]
    rw [sub_pos]
    have hratio :
        ((2 * AVenhance.q β + 1) / (2 * AVenhance.q β + 2)) * β < 1 := by
      rw [div_mul_eq_mul_div]
      exact (div_lt_iff₀ hqden).2 (by nlinarith [hnum])
    exact hratio
  unfold AVenhance.delta
  exact mul_pos (mul_pos (by norm_num) (sub_pos.mpr hq)) hfactor

theorem epsilon_pos {β : ℝ} {Λ m : ℕ} (hβ : 1 < β) (hβ' : β < 4 / 3)
    (hΛ : 2 ^ 7 ≤ Λ) : 0 < AVenhance.epsilon β Λ m := by
  by_cases hm : m = 0
  · simp [AVenhance.epsilon, hm]
  · have hbase : 0 < (Λ : ℝ) := by positivity
    have hq : 1 < AVenhance.q β := q_gt_one hβ hβ'
    have hexp : 0 < (AVenhance.q β) ^ m / (AVenhance.q β - 1) := by
      apply div_pos
      · exact pow_pos (by linarith) _
      · linarith
    have hpow : 0 < (Λ : ℝ) ^ ((AVenhance.q β) ^ m /
        (AVenhance.q β - 1)) := Real.rpow_pos_of_pos hbase _
    have hceil : 0 < ⌈(Λ : ℝ) ^ ((AVenhance.q β) ^ m /
        (AVenhance.q β - 1))⌉₊ := Nat.ceil_pos.mpr hpow
    have hceilReal : 0 <
        (⌈(Λ : ℝ) ^ ((AVenhance.q β) ^ m /
          (AVenhance.q β - 1))⌉₊ : ℝ) := by exact_mod_cast hceil
    simpa [AVenhance.epsilon, hm] using
      (inv_pos.mpr hceilReal)

theorem a_pos {β : ℝ} {Λ m : ℕ} (hβ : 1 < β) (hβ' : β < 4 / 3)
    (hΛ : 2 ^ 7 ≤ Λ) : 0 < AVenhance.a β Λ m := by
  unfold AVenhance.a
  exact Real.rpow_pos_of_pos (epsilon_pos hβ hβ' hΛ) _

theorem tauPP_pos {β : ℝ} {Λ m : ℕ} (hβ : 1 < β) (hβ' : β < 4 / 3)
    (hΛ : 2 ^ 7 ≤ Λ) : 0 < AVenhance.tauPP β Λ m := by
  have heps : 0 < AVenhance.epsilon β Λ (m - 1) := epsilon_pos hβ hβ' hΛ
  have ha : 0 < AVenhance.a β Λ (m - 1) := a_pos hβ hβ' hΛ
  have hdelta : 0 < AVenhance.delta β := delta_pos hβ hβ'
  have hnum : 0 < AVenhance.a β Λ (m - 1) /
      AVenhance.epsilon β Λ (m - 1) ^ (2 * AVenhance.delta β) := by
    exact div_pos ha (Real.rpow_pos_of_pos heps _)
  have hceil : 0 <
      ⌈AVenhance.a β Λ (m - 1) /
        AVenhance.epsilon β Λ (m - 1) ^ (2 * AVenhance.delta β)⌉₊ :=
    Nat.ceil_pos.mpr hnum
  unfold AVenhance.tauPP
  exact mul_pos (zpow_pos (by norm_num : (0 : ℝ) < 2) _)
    (inv_pos.mpr (by exact_mod_cast hceil))

theorem tauP_pos {β : ℝ} {Λ m : ℕ} (hβ : 1 < β) (hβ' : β < 4 / 3)
    (hΛ : 2 ^ 7 ≤ Λ) : 0 < AVenhance.tauP β Λ m := by
  have heps : 0 < AVenhance.epsilon β Λ (m - 1) := epsilon_pos hβ hβ' hΛ
  have hdelta : 0 < AVenhance.delta β := delta_pos hβ hβ'
  have hceil : 0 ≤
      (⌈AVenhance.epsilon β Λ (m - 1) ^ (-AVenhance.delta β)⌉₊ : ℕ) :=
    Nat.cast_nonneg _
  unfold AVenhance.tauP
  apply mul_pos
  · apply inv_pos.mpr
    have : 0 ≤ 4 * (⌈AVenhance.epsilon β Λ (m - 1) ^
        (-AVenhance.delta β)⌉₊ : ℝ) := by positivity
    linarith
  · exact tauPP_pos hβ hβ' hΛ

theorem four_tauP_le_tauPP {β : ℝ} {Λ m : ℕ} (hβ : 1 < β) (hβ' : β < 4 / 3)
    (hΛ : 2 ^ 7 ≤ Λ) :
    4 * AVenhance.tauP β Λ m ≤ AVenhance.tauPP β Λ m := by
  have heps := epsilon_pos hβ hβ' hΛ (m := m - 1)
  have hceilnat : 0 <
      ⌈AVenhance.epsilon β Λ (m - 1) ^ (-AVenhance.delta β)⌉₊ := by
    have hdelta := delta_pos hβ hβ'
    have hpow : 0 < AVenhance.epsilon β Λ (m - 1) ^ (-AVenhance.delta β) :=
      Real.rpow_pos_of_pos heps _
    exact Nat.ceil_pos.mpr hpow
  have hceilone : 1 ≤
      (⌈AVenhance.epsilon β Λ (m - 1) ^ (-AVenhance.delta β)⌉₊ : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr hceilnat)
  have hden : 0 < 4 *
      (⌈AVenhance.epsilon β Λ (m - 1) ^ (-AVenhance.delta β)⌉₊ : ℝ) + 1 := by
    positivity
  have hfive : 5 ≤ 4 *
      (⌈AVenhance.epsilon β Λ (m - 1) ^ (-AVenhance.delta β)⌉₊ : ℝ) + 1 := by
    nlinarith [hceilone]
  have hratio :
      4 * (((4 *
        (⌈AVenhance.epsilon β Λ (m - 1) ^ (-AVenhance.delta β)⌉₊ : ℝ) + 1)⁻¹) *
        AVenhance.tauPP β Λ m) ≤ AVenhance.tauPP β Λ m := by
    have hpp := tauPP_pos hβ hβ' hΛ (m := m)
    calc
      4 * ((4 *
          (⌈AVenhance.epsilon β Λ (m - 1) ^ (-AVenhance.delta β)⌉₊ : ℝ) + 1)⁻¹ *
          AVenhance.tauPP β Λ m) =
          (4 * AVenhance.tauPP β Λ m) /
            (4 * (⌈AVenhance.epsilon β Λ (m - 1) ^ (-AVenhance.delta β)⌉₊ : ℝ) + 1) := by
        ring
      _ ≤ AVenhance.tauPP β Λ m := by
        apply (div_le_iff₀ hden).2
        have hmul := mul_le_mul_of_nonneg_left hfive hpp.le
        nlinarith [hmul]
  simpa [AVenhance.tauP, mul_assoc] using hratio

end AVenhance.Infra.Cutoff
