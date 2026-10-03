/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.FlipFlop.Steps

/-! # Top step of the flip-flop

For `k = t ε_{m+1}^{β-γ}`, `t ≥ 1/2`: `log (KBar(k)/(√(9/80) ε_m^{β+γ}))` equals
`log (t √(80/9))` up to `O(ε_m^δ)`. -/

@[expose] public section

open Homogenization

noncomputable section

namespace AVenhance.Infra.FullTheorem.FlipFlop

open AVenhance

theorem top_step {β : ℝ} (I : Ingredients β) {m : ℕ} (hm : 1 ≤ m) {t : ℝ}
    (ht : 1 / 2 ≤ t)
    (hr : 4 * epsilon β I.Λ m ^ delta β ≤ 1)
    (hsm : 2 * ksConst β * epsilon β I.Λ m ≤ 1) :
    |Real.log (I.KhomScalar (t * epsilon β I.Λ (m + 1) ^ (β - gamma β)) (m + 1) /
        (Real.sqrt (9 / 80) * epsilon β I.Λ m ^ (β + gamma β))) -
      Real.log (t * Real.sqrt (80 / 9))| ≤
      (4 + 2 * (β - gamma β) * ksConst β) * epsilon β I.Λ m ^ delta β := by
  have hβ := I.one_lt_beta
  have hβ' := I.beta_lt
  have hΛ7 := I.two_pow_seven_le
  have hε0 : 0 < epsilon β I.Λ m := Infra.Cutoff.epsilon_pos hβ hβ' hΛ7
  have hε1 : 0 < epsilon β I.Λ (m + 1) := Infra.Cutoff.epsilon_pos hβ hβ' hΛ7
  have hp := beta_sub_gamma_pos hβ hβ'
  have hc0 := sqrt_ninth_pos
  set e := epsilon β I.Λ m ^ delta β with he
  set E := epsilon β I.Λ (m + 1) with hE
  have he0 : 0 ≤ e := Real.rpow_nonneg hε0.le _
  have hEγ : E ^ (2 * gamma β) ≤ e := eps_two_gamma_le I m
  have ht0 : 0 < t := by linarith
  have hEp : 0 < E ^ (β - gamma β) := Real.rpow_pos_of_pos hε1 _
  set k := t * E ^ (β - gamma β) with hk_def
  have hk : 0 < k := by positivity
  have hKk : k ≤ I.KhomScalar k (m + 1) := Infra.Section3.khomScalar_ge_input I (by omega) k hk
  have hKup := Infra.Section3.khomScalar_le_input_add_amplitude I (m := m + 1) (by omega) k hk
  rw [a_sq_mul_eps_four hβ hβ' hΛ7 (m + 1)] at hKup
  set K := I.KhomScalar k (m + 1) with hK
  have hkge : E ^ (β - gamma β) / 2 ≤ k := by rw [hk_def]; nlinarith
  have hsplit : E ^ (2 * β) = E ^ (β - gamma β) * E ^ (β - gamma β) * E ^ (2 * gamma β) := by
    rw [← Real.rpow_add hε1, ← Real.rpow_add hε1]; congr 1; ring
  have hamp : E ^ (2 * β) / (2 * k) ≤ k * (2 * e) := by
    rw [div_le_iff₀ (by positivity), hsplit]
    have h1 : E ^ (β - gamma β) * E ^ (β - gamma β) ≤ 4 * (k * k) := by nlinarith
    have h2 : 0 ≤ E ^ (2 * gamma β) := Real.rpow_nonneg hε1.le _
    calc E ^ (β - gamma β) * E ^ (β - gamma β) * E ^ (2 * gamma β)
        ≤ 4 * (k * k) * E ^ (2 * gamma β) := mul_le_mul_of_nonneg_right h1 h2
      _ ≤ 4 * (k * k) * e := mul_le_mul_of_nonneg_left hEγ (by positivity)
      _ = k * (2 * e) * (2 * k) := by ring
  set r := K / k - 1 with hr_def
  have hKr : K = k * (1 + r) := by rw [hr_def]; field_simp; ring
  have hr0 : 0 ≤ r := by
    rw [hr_def, sub_nonneg, le_div_iff₀ hk]; linarith
  have hr2 : r ≤ 2 * e := by
    have : K - k ≤ k * (2 * e) := by linarith
    have : k * r ≤ k * (2 * e) := by rw [hKr] at this; nlinarith
    exact le_of_mul_le_mul_left this hk
  have hrhalf : |r| ≤ 1 / 2 := by rw [abs_of_nonneg hr0]; linarith
  have h1r : 0 < 1 + r := by linarith
  have hF : 0 < epsilon β I.Λ m ^ (β + gamma β) := Real.rpow_pos_of_pos hε0 _
  have hratio_pos : 0 < E ^ (β - gamma β) / epsilon β I.Λ m ^ (β + gamma β) := div_pos hEp hF
  have hX : K / (Real.sqrt (9 / 80) * epsilon β I.Λ m ^ (β + gamma β)) =
      (t * Real.sqrt (80 / 9)) *
        ((1 + r) * (E ^ (β - gamma β) / epsilon β I.Λ m ^ (β + gamma β))) := by
    have hinv : Real.sqrt (80 / 9) = 1 / Real.sqrt (9 / 80) := by
      rw [eq_div_iff hc0.ne']; exact sqrt_inv_mul
    rw [hKr, hk_def, hinv]
    field_simp
  have hc1 : 0 < Real.sqrt (80 / 9) := Real.sqrt_pos.2 (by norm_num)
  rw [hX, Real.log_mul (by positivity) (by positivity), add_sub_cancel_left,
    Real.log_mul h1r.ne' hratio_pos.ne']
  have hlog1 := abs_log_one_add_le hrhalf
  have hlog2 := log_eps_ratio hβ hβ' hΛ7 hm hsm
  have hε_le : epsilon β I.Λ m ≤ e := by
    have := eps_rpow_le_delta I m (s := 1)
      (by linarith [Infra.Ingredients.delta_le_one_sixteenth hβ hβ'])
    simpa using this
  calc _ ≤ |Real.log (1 + r)| +
        |Real.log (E ^ (β - gamma β) / epsilon β I.Λ m ^ (β + gamma β))| := abs_add_le _ _
    _ ≤ 2 * |r| + 2 * (β - gamma β) * ksConst β * e := by
        refine add_le_add hlog1 (hlog2.trans ?_)
        have : 0 ≤ 2 * (β - gamma β) * ksConst β := by
          have := ksConst_ge_ten β
          positivity
        exact mul_le_mul_of_nonneg_left hε_le this
    _ ≤ 2 * (2 * e) + 2 * (β - gamma β) * ksConst β * e := by
        rw [abs_of_nonneg hr0]; linarith
    _ = _ := by ring

end AVenhance.Infra.FullTheorem.FlipFlop
