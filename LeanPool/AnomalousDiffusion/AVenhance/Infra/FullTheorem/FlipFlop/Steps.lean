/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.FlipFlop.Scales
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.OneStepAveragingUnconditional
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.KappaAtBounds
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.LimitSeries

/-! # Inner and top steps of the flip-flop

* `inner_step`: for a level `m+1 ≥ 2`, a diffusivity `k` with `k ≤ C ε_{m+1}^{β+γ}` and
  `q_{m+1} ≤ C ε_m^{4δ}`, the logarithms of the normalised `KBar(k)` and `k` have sum `O(ε_m^δ)`;
* `top_step`: for `k = t ε_{m+1}^{β-γ}`, `t ∈ [1/2, 2]`, `log (KBar(k)/(√(9/80) ε_m^{β+γ}))` is
  `log (t √(80/9)) + O(ε_m^δ)`. -/

@[expose] public section

open Homogenization

noncomputable section

namespace AVenhance.Infra.FullTheorem.FlipFlop

open AVenhance

/-- The relative error constant of the inner step. -/
def innerC (β C₀ C : ℝ) : ℝ :=
  (80 / 9) * (C ^ 2 + Infra.Section3.lAmtOneStepConstant β C₀ * (C + 1))

theorem lAmt_ge_two {β C₀ : ℝ} (hC₀ : 0 ≤ C₀) :
    2 ≤ Infra.Section3.lAmtOneStepConstant β C₀ := by
  unfold Infra.Section3.lAmtOneStepConstant
  have : 0 ≤ (Nstar β : ℝ) * C₀ +
      (4 * Real.pi ^ 2 * C₀ * Nstar β * 2 ^ Nstar β) +
      (2 * Nstar β * C₀ * ((Nstar β).factorial : ℝ) *
        2 ^ Nstar β * 2 ^ Nstar β * C₀ ^ 2 * 8 ^ Nstar β) := by positivity
  linarith

theorem innerC_nonneg {β C₀ C : ℝ} (hC : 0 ≤ C) (hC₀ : 0 ≤ C₀) : 0 ≤ innerC β C₀ C := by
  have h2 := lAmt_ge_two (β := β) hC₀
  unfold innerC
  have : 0 ≤ Infra.Section3.lAmtOneStepConstant β C₀ := by linarith
  positivity

theorem sqrt_ninth_pos : 0 < Real.sqrt (9 / 80) := Real.sqrt_pos.2 (by norm_num)

theorem sqrt_sq_ninth : Real.sqrt (9 / 80) * Real.sqrt (9 / 80) = 9 / 80 :=
  Real.mul_self_sqrt (by norm_num)

theorem sqrt_inv_mul : Real.sqrt (80 / 9) * Real.sqrt (9 / 80) = 1 := by
  rw [← Real.sqrt_mul (by norm_num)]
  norm_num

/-- `ε_{m+1}^{2γ} ≤ ε_m^δ`. -/
theorem eps_two_gamma_le {β : ℝ} (I : Ingredients β) (m : ℕ) :
    epsilon β I.Λ (m + 1) ^ (2 * gamma β) ≤ epsilon β I.Λ m ^ delta β := by
  have hβ := I.one_lt_beta
  have hβ' := I.beta_lt
  have hγ : 0 < gamma β := Infra.Ingredients.gamma_pos hβ hβ'
  have h4 := Infra.Ingredients.four_delta_le_gamma hβ hβ'
  have hδ := Infra.Ingredients.delta_pos hβ hβ'
  have hpos : 0 < epsilon β I.Λ m := Infra.Cutoff.epsilon_pos hβ hβ' I.two_pow_seven_le
  have h1 := Infra.Construction.epsilon_rpow_antitone I (by linarith : 0 < 2 * gamma β)
    (Nat.le_succ m)
  exact h1.trans (Real.rpow_le_rpow_of_exponent_ge hpos
    (Infra.Construction.epsilon_le_one hβ hβ' I.two_pow_seven_le) (by linarith))

/-- `ε^s ≤ ε^δ` for `s ≥ δ`. -/
theorem eps_rpow_le_delta {β : ℝ} (I : Ingredients β) (m : ℕ) {s : ℝ} (hs : delta β ≤ s) :
    epsilon β I.Λ m ^ s ≤ epsilon β I.Λ m ^ delta β :=
  Real.rpow_le_rpow_of_exponent_ge (Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt
    I.two_pow_seven_le) (Infra.Construction.epsilon_le_one I.one_lt_beta I.beta_lt
    I.two_pow_seven_le) hs

theorem inner_step {β C₀ C : ℝ} (I : Ingredients β) (hz : I.Czeta ≤ C₀) (hh : I.Chat ≤ C₀)
    (hC : 0 ≤ C) {m : ℕ} (hm : 1 ≤ m) {k : ℝ} (hk : 0 < k)
    (hkU : k ≤ C * epsilon β I.Λ (m + 1) ^ (β + gamma β))
    (hq : epsilon β I.Λ (m + 1) ^ 2 / (k * tau β I.Λ (m + 1)) ≤
      C * epsilon β I.Λ m ^ (4 * delta β))
    (hr : innerC β C₀ C * epsilon β I.Λ m ^ delta β ≤ 1 / 2)
    (hsm : 2 * ksConst β * epsilon β I.Λ m ≤ 1) :
    |Real.log (I.KhomScalar k (m + 1) / (Real.sqrt (9 / 80) * epsilon β I.Λ m ^ (β + gamma β)))
      + Real.log (k / (Real.sqrt (9 / 80) * epsilon β I.Λ (m + 1) ^ (β + gamma β)))| ≤
      (2 * innerC β C₀ C + 2 * (β - gamma β) * ksConst β) * epsilon β I.Λ m ^ delta β := by
  have hβ := I.one_lt_beta
  have hβ' := I.beta_lt
  have hΛ7 := I.two_pow_seven_le
  have hC₀ : 0 ≤ C₀ := le_trans (by linarith [I.one_le_Czeta]) hz
  have hIC := innerC_nonneg (β := β) (C₀ := C₀) hC hC₀
  have hε0 : 0 < epsilon β I.Λ m := Infra.Cutoff.epsilon_pos hβ hβ' hΛ7
  have hε1 : 0 < epsilon β I.Λ (m + 1) := Infra.Cutoff.epsilon_pos hβ hβ' hΛ7
  have hε1' : epsilon β I.Λ m ≤ 1 := Infra.Construction.epsilon_le_one hβ hβ' hΛ7
  have hδ := Infra.Ingredients.delta_pos hβ hβ'
  have hδ1 := Infra.Ingredients.delta_le_one_sixteenth hβ hβ'
  have hγ : 0 < gamma β := Infra.Ingredients.gamma_pos hβ hβ'
  have hp := beta_sub_gamma_pos hβ hβ'
  have hc0 := sqrt_ninth_pos
  set e := epsilon β I.Λ m ^ delta β with he
  set E := epsilon β I.Λ (m + 1) with hE
  have he0 : 0 ≤ e := Real.rpow_nonneg hε0.le _
  have hEγ : E ^ (2 * gamma β) ≤ e := eps_two_gamma_le I m
  -- the one-step error
  have herr := Infra.Section3.KhomScalar_one_step_error_unconditional I hz hh (m := m + 1)
    (by omega) hk
  simp only [Nat.add_sub_cancel] at herr
  rw [a_sq_mul_eps_four hβ hβ' hΛ7 (m + 1)] at herr
  set S := E ^ (2 * β) / k with hS
  have hS0 : 0 < S := by positivity
  have hSk : S * k = E ^ (2 * β) := by rw [hS]; field_simp
  set C₁ := Infra.Section3.lAmtOneStepConstant β C₀
  have hqe : E ^ 2 / (k * tau β I.Λ (m + 1)) ≤ C * e :=
    hq.trans (mul_le_mul_of_nonneg_left (eps_rpow_le_delta I m (by linarith)) hC)
  have hC₁ : 0 ≤ C₁ := by linarith [lAmt_ge_two (β := β) hC₀]
  -- k ≤ S C² e
  have hkS : k ≤ S * (C ^ 2 * e) := by
    have hFF : E ^ (2 * β) * E ^ (2 * gamma β) = (E ^ (β + gamma β)) ^ 2 := by
      rw [← Real.rpow_add hε1, ← Real.rpow_natCast, ← Real.rpow_mul hε1.le]
      congr 1
      push_cast
      ring
    have h1 : k * k ≤ (C * E ^ (β + gamma β)) ^ 2 := by
      rw [← sq]
      exact pow_le_pow_left₀ hk.le hkU 2
    have h2 : k * k ≤ C ^ 2 * (E ^ (2 * β) * E ^ (2 * gamma β)) := by
      rw [hFF]; nlinarith [h1]
    have h3 : C ^ 2 * (E ^ (2 * β) * E ^ (2 * gamma β)) ≤ C ^ 2 * (E ^ (2 * β) * e) := by
      gcongr
    have h4 : k * k ≤ S * k * (C ^ 2 * e) := by
      rw [hSk]; nlinarith [h2, h3]
    have : k * k ≤ k * (S * (C ^ 2 * e)) := by nlinarith [h4]
    exact le_of_mul_le_mul_left this hk
  -- relative error
  set K := I.KhomScalar k (m + 1) with hK
  have hKk : k ≤ K := Infra.Section3.khomScalar_ge_input I (by omega) k hk
  have hdiff : |K - (9 / 80) * S| ≤ (9 / 80) * S * (innerC β C₀ C * e) := by
    have hD : |K - (k + 9 / 80 * S)| ≤ C₁ * S * (C * e + e) := by
      refine herr.trans ?_
      gcongr
    have htri : |K - (9 / 80) * S| ≤ |K - (k + 9 / 80 * S)| + k := by
      have : K - (9 / 80) * S = (K - (k + 9 / 80 * S)) + k := by ring
      rw [this]
      calc |(K - (k + 9 / 80 * S)) + k| ≤ |K - (k + 9 / 80 * S)| + |k| := abs_add_le _ _
        _ = _ := by rw [abs_of_pos hk]
    have : (9 / 80) * S * (innerC β C₀ C * e) =
        S * (C ^ 2 * e) + C₁ * S * (C * e + e) := by
      unfold innerC; ring
    rw [this]
    linarith
  set r := K / ((9 / 80) * S) - 1 with hr_def
  have hKr : K = (9 / 80) * S * (1 + r) := by rw [hr_def]; field_simp; ring
  have hrabs : |r| ≤ innerC β C₀ C * e := by
    have : r = (K - (9 / 80) * S) / ((9 / 80) * S) := by rw [hr_def]; field_simp
    rw [this, abs_div, abs_of_pos (by positivity : 0 < (9 / 80) * S), div_le_iff₀ (by positivity)]
    linarith
  have hrhalf : |r| ≤ 1 / 2 := hrabs.trans hr
  have h1r : 0 < 1 + r := by linarith [(abs_le.1 hrhalf).1]
  -- product identity
  have hKpos : 0 < K := lt_of_lt_of_le hk hKk
  have hE1 : 0 < epsilon β I.Λ m ^ (β + gamma β) := Real.rpow_pos_of_pos hε0 _
  have hE2 : 0 < E ^ (β + gamma β) := Real.rpow_pos_of_pos hε1 _
  have hsplit : E ^ (2 * β) = E ^ (β - gamma β) * E ^ (β + gamma β) := by
    rw [← Real.rpow_add hε1]; congr 1; ring
  have hprod : K / (Real.sqrt (9 / 80) * epsilon β I.Λ m ^ (β + gamma β)) *
      (k / (Real.sqrt (9 / 80) * E ^ (β + gamma β))) =
      (1 + r) * (E ^ (β - gamma β) / epsilon β I.Λ m ^ (β + gamma β)) := by
    have hsq := sqrt_sq_ninth
    have hkS' : K * k = (9 / 80) * (1 + r) * E ^ (2 * β) := by
      rw [hKr, ← hSk]; ring
    rw [div_mul_div_comm, hkS', hsplit]
    have : Real.sqrt (9 / 80) * epsilon β I.Λ m ^ (β + gamma β) *
        (Real.sqrt (9 / 80) * E ^ (β + gamma β)) =
        (9 / 80) * (epsilon β I.Λ m ^ (β + gamma β) * E ^ (β + gamma β)) := by
      calc _ = (Real.sqrt (9 / 80) * Real.sqrt (9 / 80)) *
            (epsilon β I.Λ m ^ (β + gamma β) * E ^ (β + gamma β)) := by ring
        _ = _ := by rw [hsq]
    rw [this]
    field_simp
  have hratio_pos : 0 < E ^ (β - gamma β) / epsilon β I.Λ m ^ (β + gamma β) :=
    div_pos (Real.rpow_pos_of_pos hε1 _) hE1
  have hXpos : 0 < K / (Real.sqrt (9 / 80) * epsilon β I.Λ m ^ (β + gamma β)) := by positivity
  have hYpos : 0 < k / (Real.sqrt (9 / 80) * E ^ (β + gamma β)) := by positivity
  rw [← Real.log_mul hXpos.ne' hYpos.ne', hprod, Real.log_mul h1r.ne' hratio_pos.ne']
  have hlog1 := abs_log_one_add_le hrhalf
  have hlog2 := log_eps_ratio hβ hβ' hΛ7 hm hsm
  have hε_le : epsilon β I.Λ m ≤ e := by
    have := eps_rpow_le_delta I m (s := 1) (by linarith)
    simpa using this
  calc _ ≤ |Real.log (1 + r)| +
        |Real.log (E ^ (β - gamma β) / epsilon β I.Λ m ^ (β + gamma β))| := abs_add_le _ _
    _ ≤ 2 * (innerC β C₀ C * e) + 2 * (β - gamma β) * ksConst β * e := by
        refine add_le_add (hlog1.trans (by linarith)) (hlog2.trans ?_)
        have : 0 ≤ 2 * (β - gamma β) * ksConst β := by
          have := ksConst_ge_ten β
          positivity
        exact mul_le_mul_of_nonneg_left hε_le this
    _ = _ := by ring

end AVenhance.Infra.FullTheorem.FlipFlop
