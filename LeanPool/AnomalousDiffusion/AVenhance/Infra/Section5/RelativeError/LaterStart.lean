/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftToShow.Scales
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.A0Facts
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.MTheta0IsLeast

/-! # the later start `m₊(R)` and the exponent `p₊` (2), §4, §6 item 11.  The relative induction
of starts at `m₊(R) = 1 + min {j ≥ 1 : ε_j^{1+γ/2-δ} ≤ R}`; here `laterStart β Λ R` is the
index `j = m₊(R) - 1`.  This module proves that the minimum exists, that every `m ≥ m₊(R)` also
satisfies the original `mTheta0` bound, the exponent facts `0 < p₊ < 2`, the radius bound for
smooth analytic data, and the lower bound `ε_j^{β+γ} ≥ 2^{-(β+γ)} R^{p₊}` for `j ≥ 2`.
-/

@[expose] public section

noncomputable section

namespace AVenhance.Infra.Section5.RelativeError

open AVenhance Homogenization

/-- `m₊(R) − 1`: the least `j ≥ 1` with `ε_j^{1+γ/2−δ} ≤ R` ((1)). -/
noncomputable def laterStart (β : ℝ) (Λ : ℕ) (R : ℝ) : ℕ :=
  sInf {j : ℕ | 1 ≤ j ∧ epsilon β Λ j ^ (1 + gamma β / 2 - delta β) ≤ R}

/-- `p₊ = q(β+γ)/(1+γ/2−δ)` ((2)). -/
noncomputable def pPlus (β : ℝ) : ℝ := q β * (β + gamma β) / (1 + gamma β / 2 - delta β)

section Elementary

variable {β : ℝ} {Λ : ℕ}

theorem LaterStart.eps_pos (hβ : 1 < β) (hβ' : β < 4 / 3) (hΛ : 2 ^ 7 ≤ Λ) {m : ℕ} :
    0 < epsilon β Λ m :=
  Infra.Cutoff.epsilon_pos hβ hβ' hΛ

theorem LaterStart.eps_le_one (hβ : 1 < β) (hβ' : β < 4 / 3) (hΛ : 2 ^ 7 ≤ Λ) {m : ℕ} :
    epsilon β Λ m ≤ 1 :=
  Infra.Construction.epsilon_le_one hβ hβ' hΛ

/-- The exponent `1 + γ/2 − δ` is positive on the range. -/
theorem later_exponent_pos (hβ : 1 < β) (hβ' : β < 4 / 3) : 0 < 1 + gamma β / 2 - delta β := by
  have hγ := Infra.Ingredients.gamma_pos hβ hβ'
  have hδ := Infra.Ingredients.delta_le_one_sixteenth hβ hβ'
  linarith

/-- The exponent `1 + γ/2 − δ` is at most `1 + γ/2`. -/
theorem later_exponent_le (hβ : 1 < β) (hβ' : β < 4 / 3) :
    1 + gamma β / 2 - delta β ≤ 1 + gamma β / 2 := by
  have hδ := Infra.Ingredients.delta_pos hβ hβ'
  linarith

/-- The length scales are antitone in the index. -/
theorem epsilon_antitone (hβ : 1 < β) (hβ' : β < 4 / 3) (hΛ : 2 ^ 7 ≤ Λ) {n m : ℕ}
    (hnm : n ≤ m) : epsilon β Λ m ≤ epsilon β Λ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact LaterStart.eps_le_one hβ hβ' hΛ
  · have hm : m ≠ 0 := by omega
    have hn0 : n ≠ 0 := by omega
    have hq := Infra.Ingredients.one_lt_q hβ hβ'
    have hΛ1 : (1 : ℝ) ≤ Λ := by exact_mod_cast (le_trans (by norm_num : 1 ≤ 2 ^ 7) hΛ)
    have hΛ0 : (0 : ℝ) < Λ := by linarith
    have hexp : q β ^ n / (q β - 1) ≤ q β ^ m / (q β - 1) :=
      div_le_div_of_nonneg_right (pow_le_pow_right₀ hq.le hnm) (by linarith)
    have hX : (Λ : ℝ) ^ (q β ^ n / (q β - 1)) ≤ (Λ : ℝ) ^ (q β ^ m / (q β - 1)) :=
      Real.rpow_le_rpow_of_exponent_le hΛ1 hexp
    have hceil := Nat.ceil_mono hX
    have hpos : (0 : ℝ) < (⌈(Λ : ℝ) ^ (q β ^ n / (q β - 1))⌉₊ : ℝ) := by
      exact_mod_cast Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hΛ0 _)
    simp only [epsilon, hm, hn0, ite_false]
    exact inv_anti₀ hpos (by exact_mod_cast hceil)

/-- `(Λ^{-j})^e = (Λ^{-e})^j`, used for the decay of `ε_j^e`. -/
theorem LaterStart.rpow_neg_nat_rpow {Λ : ℝ} (hΛ : 0 < Λ) (j : ℕ) (e : ℝ) :
    (Λ ^ (-(j : ℝ))) ^ e = (Λ ^ (-e)) ^ j := by
  rw [← Real.rpow_mul hΛ.le, ← Real.rpow_natCast, ← Real.rpow_mul hΛ.le]
  congr 1
  ring

/-- The defining set of `laterStart` is nonempty. -/
theorem laterStart_set_nonempty (hβ : 1 < β) (hβ' : β < 4 / 3) (hΛ : 2 ^ 7 ≤ Λ) {R : ℝ}
    (hR : 0 < R) :
    {j : ℕ | 1 ≤ j ∧ epsilon β Λ j ^ (1 + gamma β / 2 - delta β) ≤ R}.Nonempty := by
  set e := 1 + gamma β / 2 - delta β with he_def
  have he : 0 < e := later_exponent_pos hβ hβ'
  have hΛ128 : (128 : ℝ) ≤ Λ := by exact_mod_cast hΛ
  have hΛ0 : (0 : ℝ) < Λ := by linarith
  have hb : (Λ : ℝ) ^ (-e) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by linarith) (by linarith)
  have hb0 : 0 ≤ (Λ : ℝ) ^ (-e) := Real.rpow_nonneg hΛ0.le _
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hR hb
  refine ⟨N + 1, by omega, ?_⟩
  have hε := Infra.Ingredients.epsilon_le_lambda_pow (β := β) (Λ := Λ) (m := N + 1) hβ hβ' hΛ
  have hε0 : 0 ≤ epsilon β Λ (N + 1) := (LaterStart.eps_pos hβ hβ' hΛ).le
  calc epsilon β Λ (N + 1) ^ e
      ≤ ((Λ : ℝ) ^ (-((N + 1 : ℕ) : ℝ))) ^ e := Real.rpow_le_rpow hε0 hε he.le
    _ = ((Λ : ℝ) ^ (-e)) ^ (N + 1) := LaterStart.rpow_neg_nat_rpow hΛ0 _ e
    _ ≤ ((Λ : ℝ) ^ (-e)) ^ N := pow_le_pow_of_le_one hb0 hb.le (Nat.le_succ N)
    _ ≤ R := hN.le

end Elementary

variable {β : ℝ} {Λ : ℕ}

theorem laterStart_isLeast (hβ : 1 < β) (hβ' : β < 4 / 3) (hΛ : 2 ^ 7 ≤ Λ)
    {R : ℝ} (hR : 0 < R) :
    IsLeast {j : ℕ | 1 ≤ j ∧ epsilon β Λ j ^ (1 + gamma β / 2 - delta β) ≤ R}
      (laterStart β Λ R) :=
  ⟨Nat.sInf_mem (laterStart_set_nonempty hβ hβ' hΛ hR), fun _ hj => Nat.sInf_le hj⟩

/-- Every level `m ≥ m₊(R)` satisfies the later scale condition and the original `mTheta0` bound. -/
theorem later_scale_of_le (hβ : 1 < β) (hβ' : β < 4 / 3) (hΛ : 2 ^ 7 ≤ Λ)
    {R : ℝ} (hR : 0 < R) {m : ℕ} (hm : laterStart β Λ R + 1 ≤ m) :
    epsilon β Λ (m - 1) ^ (1 + gamma β / 2 - delta β) ≤ R ∧ mTheta0 β Λ R ≤ m := by
  obtain ⟨⟨hj1, hjR⟩, _⟩ := laterStart_isLeast hβ hβ' hΛ hR
  have he := later_exponent_pos hβ hβ'
  have hmono : epsilon β Λ (m - 1) ≤ epsilon β Λ (laterStart β Λ R) :=
    epsilon_antitone hβ hβ' hΛ (by omega)
  have hlater : epsilon β Λ (m - 1) ^ (1 + gamma β / 2 - delta β) ≤ R :=
    (Real.rpow_le_rpow (LaterStart.eps_pos hβ hβ' hΛ).le hmono he.le).trans hjR
  refine ⟨hlater, (mTheta0_isLeast hβ hβ' hΛ hR).2 ⟨by omega, ?_⟩⟩
  exact (Real.rpow_le_rpow_of_exponent_ge (LaterStart.eps_pos hβ hβ' hΛ) (LaterStart.eps_le_one hβ
      hβ' hΛ)
    (later_exponent_le hβ hβ')).trans hlater

/-! ### The exponent `p₊ < 2` -/

/-- The cubic certificate behind `p₊ < 2`: positive on `(1, 3/2]`. -/
theorem LaterStart.pPlus_poly {q : ℝ} (h1 : 1 < q) (h2 : q ≤ 3 / 2) :
    0 < 23 * q ^ 2 + 6 * q - 5 - 16 * q ^ 3 := by
  have hprod : 0 ≤ (q - 1) * (3 / 2 - q) := mul_nonneg (by linarith) (by linarith)
  nlinarith [mul_nonneg hprod (by linarith : (0:ℝ) ≤ 16 * q + 17)]

/-- `q(β+γ) < 2(1+γ/2−δ)` as a statement about abstract reals satisfying the defining
relations of `β, γ, δ` in terms of `q ∈ (1, 3/2]`. -/
theorem LaterStart.pPlus_ineq_aux {q β γ δ : ℝ} (h1 : 1 < q) (h2 : q ≤ 3 / 2)
    (hβ : β * (4 * q - 1) = 4 * q) (hγ : γ * (q + 1) = (q - 1) * β)
    (hδ : δ * (4 * (q + 1) * (4 * q - 1)) = (q - 1) ^ 2) :
    q * (β + γ) < 2 * (1 + γ / 2 - δ) := by
  have h4 : 0 < 4 * q - 1 := by linarith
  have h5 : 0 < q + 1 := by linarith
  have hpoly := LaterStart.pPlus_poly h1 h2
  have hβ' : β = 4 * q / (4 * q - 1) := (eq_div_iff h4.ne').2 hβ
  have hγ' : γ = (q - 1) * β / (q + 1) := (eq_div_iff h5.ne').2 hγ
  have hδ' : δ = (q - 1) ^ 2 / (4 * (q + 1) * (4 * q - 1)) :=
    (eq_div_iff (by positivity)).2 hδ
  have hd : 2 * (1 + γ / 2 - δ) - q * (β + γ) =
      (23 * q ^ 2 + 6 * q - 5 - 16 * q ^ 3) / (2 * (q + 1) * (4 * q - 1)) := by
    rw [hγ', hδ', hβ']
    generalize hb : 4 * q - 1 = b at *
    have hq : q = (b + 1) / 4 := by linarith
    subst hq
    field_simp
    ring
  have : 0 < 2 * (1 + γ / 2 - δ) - q * (β + γ) := by
    rw [hd]; exact div_pos hpoly (by positivity)
  linarith

theorem pPlus_pos_lt_two (hβ : 6 / 5 ≤ β) (hβ' : β < 4 / 3) : 0 < pPlus β ∧ pPlus β < 2 := by
  have hβ1 : 1 < β := by linarith
  have hq1 := Infra.Ingredients.one_lt_q hβ1 hβ'
  have hqeq := Infra.Ingredients.q_eq_beta_div_four_sub_one hβ1
  have hβm : 0 < β - 1 := by linarith
  have hq32 : q β ≤ 3 / 2 := by
    rw [hqeq, div_le_iff₀ (by positivity)]
    linarith
  have hβq : β * (4 * q β - 1) = 4 * q β := by
    have h : q β * (4 * (β - 1)) = β := by rw [hqeq]; field_simp
    linarith
  have hγq : gamma β * (q β + 1) = (q β - 1) * β := by
    unfold gamma
    exact div_mul_cancel₀ _ (by linarith)
  have hδq : delta β * (4 * (q β + 1) * (4 * q β - 1)) = (q β - 1) ^ 2 := by
    rw [Infra.Ingredients.delta_eq_q_fraction hβ1 hβ']
    exact div_mul_cancel₀ _ (by nlinarith)
  have hlt := LaterStart.pPlus_ineq_aux hq1 hq32 hβq hγq hδq
  have he := later_exponent_pos hβ1 hβ'
  have hγ := Infra.Ingredients.gamma_pos hβ1 hβ'
  unfold pPlus
  constructor
  · exact div_pos (mul_pos (by linarith) (by linarith)) he
  · rw [div_lt_iff₀ he]
    linarith

/-! ### Radius bound -/

/-- Smooth analytic nonzero data have `R ≤ 1/(√2 π)` (Poincaré + the n = 1 analytic bound). -/
theorem analytic_radius_le {R : ℝ} (hR : 0 < R) {g : Vec 2 → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgp : IsZ2Periodic g) (hgm : MeanZeroOn unitCube g) (hga : IsThetaAnalytic R g)
    (hg0 : 0 < l2NormSq g) : R ≤ 1 / (Real.sqrt 2 * Real.pi) :=
  analytic_radius_bound (hg.of_le (by exact_mod_cast le_top)) hgp hgm hg0 hR hga

/-! ### The lower bound for `ε_j^{β+γ}` at the later start -/

/-- Pure-real chain: `R < y^e`, `y^q/2 ≤ z` give `2^{-h} R^{qh/e} ≤ z^h`. -/
theorem rpow_chain_lower {R y z e q h : ℝ} (hR : 0 < R) (hy : 0 < y) (he : 0 < e) (hq : 0 < q)
    (hh : 0 < h) (hRy : R < y ^ e) (hz : y ^ q / 2 ≤ z) :
    (1 / 2) ^ h * R ^ (q * h / e) ≤ z ^ h := by
  have hx : 0 ≤ q * h / e := by positivity
  have h1 : R ^ (q * h / e) ≤ (y ^ e) ^ (q * h / e) :=
    Real.rpow_le_rpow hR.le hRy.le hx
  have h2 : (y ^ e) ^ (q * h / e) = (y ^ q) ^ h := by
    rw [← Real.rpow_mul hy.le, ← Real.rpow_mul hy.le]
    congr 1
    field_simp
  have hyq : 0 ≤ y ^ q := Real.rpow_nonneg hy.le _
  calc (1 / 2) ^ h * R ^ (q * h / e) ≤ (1 / 2) ^ h * (y ^ q) ^ h := by
        rw [← h2]
        exact mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg (by norm_num) _)
    _ = (y ^ q / 2) ^ h := by
        rw [← Real.mul_rpow (by norm_num) hyq]
        congr 1
        ring
    _ ≤ z ^ h := Real.rpow_le_rpow (by positivity) hz hh.le

/-- For `j = laterStart ≥ 2`, minimality gives `2^{-(β+γ)} R^{p₊} ≤ ε_j^{β+γ}`. -/
theorem later_eps_pow_lower (hβ : 1 < β) (hβ' : β < 4 / 3) (hΛ : 2 ^ 7 ≤ Λ)
    {R : ℝ} (hR : 0 < R) (hj : 2 ≤ laterStart β Λ R) :
    (1 / 2) ^ (β + gamma β) * R ^ pPlus β ≤
      epsilon β Λ (laterStart β Λ R) ^ (β + gamma β) := by
  have hmin : R < epsilon β Λ (laterStart β Λ R - 1) ^ (1 + gamma β / 2 - delta β) := by
    by_contra hcon
    have hmem : laterStart β Λ R - 1 ∈
        {j : ℕ | 1 ≤ j ∧ epsilon β Λ j ^ (1 + gamma β / 2 - delta β) ≤ R} :=
      ⟨by omega, not_lt.mp hcon⟩
    exact absurd (Nat.sInf_le hmem) (by unfold laterStart at hj ⊢; omega)
  have hz := Infra.Section5.LeftToShow.epsilon_pred_pow_q_div_two_le (Λ := Λ) hβ hβ' hΛ (m :=
      laterStart β Λ R) hj
  have hγ := Infra.Ingredients.gamma_pos hβ hβ'
  exact rpow_chain_lower hR (LaterStart.eps_pos hβ hβ' hΛ) (later_exponent_pos hβ hβ')
    (by linarith [Infra.Ingredients.one_lt_q hβ hβ']) (by linarith) hmin hz

end AVenhance.Infra.Section5.RelativeError
