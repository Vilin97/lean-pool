/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.LebronStep.KappaBounds
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.MTheta0IsLeast
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.AssemblyScales

/-! # Scale facts for the analytic case of `r.LeBron.2`

* the lower bound `ε_{m₀-1} ≥ c · min(1,R)^{q/(1+γ/2)}` for `m₀ = mTheta0 R` (minimality);
* the elementary exponent identities `2β/(q+1) = β - γ`, `γ < β`;
* two-sided bound of an element of a permitted interval;
* `E^{-e} ≤ c^{-e} (1 + R^{-re})` from `c min(1,R)^r ≤ E`. -/

@[expose] public section

open MeasureTheory Homogenization

noncomputable section

namespace AVenhance.Infra.FullTheorem

open AVenhance

theorem gamma_lt_beta {β : ℝ} (hβ : 1 < β) (hβ' : β < 4 / 3) : gamma β < β := by
  have hq : 1 < q β := Infra.Ingredients.one_lt_q hβ hβ'
  unfold gamma
  rw [div_lt_iff₀ (by linarith)]
  nlinarith

theorem two_beta_div_eq {β : ℝ} (hβ : 1 < β) (hβ' : β < 4 / 3) :
    2 * β / (q β + 1) = β - gamma β := by
  have hq : 1 < q β := Infra.Ingredients.one_lt_q hβ hβ'
  unfold gamma
  have : q β + 1 ≠ 0 := by linarith
  field_simp
  ring

/-- Lower bound for the scale `ε_{m₀ - 1}`. -/
theorem epsilon_mTheta0_lower {β : ℝ} {Λ : ℕ} (hβ : 1 < β) (hβ' : β < 4 / 3)
    (hΛ : 2 ^ 7 ≤ Λ) {R : ℝ} (hR : 0 < R) :
    min (epsilon β Λ 1) (1 / 2) * min 1 R ^ (q β / (1 + gamma β / 2)) ≤
      epsilon β Λ (mTheta0 β Λ R - 1) := by
  obtain ⟨⟨h2, hle⟩, hmin⟩ := mTheta0_isLeast hβ hβ' hΛ hR
  have hq : 1 < q β := Infra.Ingredients.one_lt_q hβ hβ'
  have hγ : 0 < gamma β := Infra.Ingredients.gamma_pos hβ hβ'
  have hs : 0 < 1 + gamma β / 2 := by linarith
  have hr : 0 ≤ q β / (1 + gamma β / 2) := by positivity
  have hmpos : 0 < min 1 R := lt_min one_pos hR
  have hx1 : min 1 R ^ (q β / (1 + gamma β / 2)) ≤ 1 :=
    Real.rpow_le_one hmpos.le (min_le_left _ _) hr
  have hx0 : 0 ≤ min 1 R ^ (q β / (1 + gamma β / 2)) := Real.rpow_nonneg hmpos.le _
  have hε1 : 0 < epsilon β Λ 1 := Infra.Cutoff.epsilon_pos hβ hβ' hΛ
  rcases Nat.lt_or_ge (mTheta0 β Λ R) 3 with h3 | h3
  · have e : mTheta0 β Λ R - 1 = 1 := by omega
    rw [e]
    calc _ ≤ epsilon β Λ 1 * 1 :=
          mul_le_mul (min_le_left _ _) hx1 hx0 hε1.le
      _ = _ := mul_one _
  · set m₀ := mTheta0 β Λ R with hm₀
    have hn : 1 ≤ m₀ - 1 - 1 := by omega
    have hnot : ¬ epsilon β Λ (m₀ - 1 - 1) ^ (1 + gamma β / 2) ≤ R := by
      intro hh
      have := hmin ⟨by omega, hh⟩
      omega
    replace hnot := not_le.mp hnot
    have hεn : 0 < epsilon β Λ (m₀ - 1 - 1) := Infra.Cutoff.epsilon_pos hβ hβ' hΛ
    have h1 : R ^ (1 / (1 + gamma β / 2)) < epsilon β Λ (m₀ - 1 - 1) := by
      have := Real.rpow_lt_rpow hR.le hnot (by positivity : 0 < 1 / (1 + gamma β / 2))
      rwa [← Real.rpow_mul hεn.le, mul_one_div_cancel hs.ne', Real.rpow_one] at this
    have h2' : (1 / 2) * epsilon β Λ (m₀ - 1 - 1) ^ q β ≤ epsilon β Λ (m₀ - 1) := by
      have := epsilon_succ_ge hβ hβ' hΛ hn
      rwa [show m₀ - 1 - 1 + 1 = m₀ - 1 by omega] at this
    have h3' : R ^ (q β / (1 + gamma β / 2)) ≤ epsilon β Λ (m₀ - 1 - 1) ^ q β := by
      have := Real.rpow_le_rpow (Real.rpow_nonneg hR.le _) h1.le (by linarith : 0 ≤ q β)
      rwa [← Real.rpow_mul hR.le, one_div, ← div_eq_inv_mul, ] at this
    have h4 : min 1 R ^ (q β / (1 + gamma β / 2)) ≤ R ^ (q β / (1 + gamma β / 2)) :=
      Real.rpow_le_rpow hmpos.le (min_le_right _ _) hr
    calc min (epsilon β Λ 1) (1 / 2) * min 1 R ^ (q β / (1 + gamma β / 2))
        ≤ (1 / 2) * R ^ (q β / (1 + gamma β / 2)) :=
          mul_le_mul (min_le_right _ _) h4 hx0 (by norm_num)
      _ ≤ (1 / 2) * epsilon β Λ (m₀ - 1 - 1) ^ q β := by gcongr
      _ ≤ _ := h2'

/-- `E^{-e} ≤ c^{-e} (1 + R^{-(r e)})` from `c min(1,R)^r ≤ E`. -/
theorem inv_rpow_le {c R r e E : ℝ} (hc : 0 < c) (hR : 0 < R) (he : 0 ≤ e)
    (hE : c * min 1 R ^ r ≤ E) : E ^ (-e) ≤ c ^ (-e) * (1 + R ^ (-(r * e))) := by
  have hm : 0 < min 1 R := lt_min one_pos hR
  have hmr : 0 < min 1 R ^ r := Real.rpow_pos_of_pos hm r
  have hpos : 0 < c * min 1 R ^ r := mul_pos hc hmr
  have h1 : E ^ (-e) ≤ (c * min 1 R ^ r) ^ (-e) :=
    Real.rpow_le_rpow_of_nonpos hpos hE (by linarith)
  rw [Real.mul_rpow hc.le hmr.le, ← Real.rpow_mul hm.le] at h1
  have h2 : min 1 R ^ (r * -e) ≤ 1 + R ^ (-(r * e)) := by
    rcases le_total 1 R with h | h
    · rw [min_eq_left h, Real.one_rpow]
      have := Real.rpow_nonneg hR.le (-(r * e))
      linarith
    · rw [min_eq_right h, show r * -e = -(r * e) by ring]
      linarith
  have hc' : 0 ≤ c ^ (-e) := Real.rpow_nonneg hc.le _
  calc E ^ (-e) ≤ c ^ (-e) * min 1 R ^ (r * -e) := h1
    _ ≤ c ^ (-e) * (1 + R ^ (-(r * e))) := mul_le_mul_of_nonneg_left h2 hc'

/-- Every element of a permitted interval (`M ≥ 1`, `Λ` large) lies in `[½ ε_M^{β-γ}, 1]`. -/
theorem permitted_bounds {β : ℝ} {Λ : ℕ} (hβ : 1 < β) (hβ' : β < 4 / 3) (hΛ : 2 ^ 7 ≤ Λ)
    (hΛs : (2 : ℝ) ^ (1 / (β - gamma β)) ≤ (Λ : ℝ)) {κ : ℝ} {M : ℕ} (hM : 1 ≤ M)
    (hκM : κ ∈ permittedInterval β Λ M) :
    (1 / 2) * epsilon β Λ M ^ (β - gamma β) ≤ κ ∧ κ ≤ 1 := by
  have hγβ := gamma_lt_beta hβ hβ'
  have hspos : 0 < β - gamma β := by linarith
  have hΛpos : (0 : ℝ) < Λ := by
    have : (128 : ℝ) ≤ Λ := by exact_mod_cast hΛ
    linarith
  obtain ⟨hlo, hup⟩ := hκM
  rw [two_beta_div_eq hβ hβ'] at hlo hup
  refine ⟨hlo, hup.trans ?_⟩
  have h1 : epsilon β Λ M ^ (β - gamma β) ≤ ((Λ : ℝ)⁻¹) ^ (β - gamma β) :=
    epsilon_rpow_le_inv_rpow hβ hβ' hΛ hM hspos.le
  calc 2 * epsilon β Λ M ^ (β - gamma β) ≤ 2 * ((Λ : ℝ)⁻¹) ^ (β - gamma β) := by gcongr
    _ ≤ 1 := two_mul_inv_rpow_le_one hspos hΛpos hΛs

end AVenhance.Infra.FullTheorem
