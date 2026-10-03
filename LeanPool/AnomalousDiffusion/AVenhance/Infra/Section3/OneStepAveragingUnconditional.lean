/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import Mathlib.Analysis.Real.Pi.Bounds

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.OneStepAveraging
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.KappaAtBounds
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ingredients.TimeScaleArithmetic
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.Scalars
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ingredients.Parameters

/-! The one-step averaged-flux estimate with both source errors retained. -/

@[expose] public section

noncomputable section

namespace AVenhance.Infra.Section3

open AVenhance

theorem OneStepAveragingUnconditional.rpow_ceil_bounds_local {x : ℝ} (hx : 1 ≤ x) :
    x ≤ (⌈x⌉₊ : ℝ) ∧ (⌈x⌉₊ : ℝ) ≤ 2 * x := by
  constructor
  · exact_mod_cast Nat.le_ceil x
  · have hceil : (⌈x⌉₊ : ℝ) < x + 1 := by
      exact_mod_cast (Nat.ceil_lt_add_one
        (le_of_lt (lt_of_lt_of_le zero_lt_one hx)))
    linarith

theorem OneStepAveragingUnconditional.tau_over_tauP_le_prev_delta {β : ℝ} (I : Ingredients β)
    {m : ℕ} (hm : 1 ≤ m) :
    tau β I.Λ m / tauP β I.Λ m ≤
      epsilon β I.Λ (m - 1) ^ delta β / 4 := by
  let e := epsilon β I.Λ (m - 1)
  let d := delta β
  let F := Infra.Ingredients.tauCellFactor β I.Λ m
  have he : 0 < e := by
    dsimp [e]
    exact Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have he1 : e ≤ 1 := by
    dsimp [e]
    exact Infra.Construction.epsilon_le_one I.one_lt_beta I.beta_lt
      I.two_pow_seven_le
  have hd : 0 < d := by dsimp [d]; exact Infra.Cutoff.delta_pos I.one_lt_beta I.beta_lt
  have hx : 1 ≤ e ^ (-d) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos he he1 (by linarith)
  have hceil := OneStepAveragingUnconditional.rpow_ceil_bounds_local hx
  have hF : 4 * e ^ (-d) ≤ F := by
    dsimp [F, Infra.Ingredients.tauCellFactor]
    have hceil' : 4 * e ^ (-d) ≤ 4 * (⌈e ^ (-d)⌉₊ : ℝ) :=
      mul_le_mul_of_nonneg_left hceil.1 (by norm_num)
    linarith
  have hFpos : 0 < F := by
    dsimp [F, Infra.Ingredients.tauCellFactor]
    positivity
  have hcancel : e ^ (-d) * e ^ d = 1 := by
    rw [← Real.rpow_add he]
    simp
  have hFscaled : 4 ≤ F * e ^ d := by
    have h := mul_le_mul_of_nonneg_right hF (Real.rpow_nonneg he.le d)
    calc
      4 = 4 * (e ^ (-d) * e ^ d) := by rw [hcancel]; ring
      _ = (4 * e ^ (-d)) * e ^ d := by ring
      _ ≤ F * e ^ d := h
  have hinv : F⁻¹ ≤ e ^ d / 4 := by
    have hFscaled' : (1 : ℝ) * 4 ≤ F * e ^ d := by
      simpa only [one_mul] using hFscaled
    have hscaled : 1 ≤ (F * e ^ d) / 4 :=
      (le_div_iff₀ (by norm_num : (0 : ℝ) < 4)).2 hFscaled'
    have hscaled' : 1 ≤ (e ^ d / 4) * F := by
      rw [show (F * e ^ d) / 4 = (e ^ d / 4) * F by ring] at hscaled
      exact hscaled
    have hdiv : 1 / F ≤ e ^ d / 4 := (div_le_iff₀ hFpos).2 hscaled'
    simpa only [one_div] using hdiv
  have hratio : tau β I.Λ m / tauP β I.Λ m = F⁻¹ := by
    have hτ := I.tau_pos' m
    rw [Infra.Ingredients.tauP_eq_cellFactor_mul_tau hm]
    change tau β I.Λ m / (F * tau β I.Λ m) = F⁻¹
    field_simp [ne_of_gt hτ, ne_of_gt hFpos]
  rw [hratio]
  simpa [e, d] using hinv

theorem OneStepAveragingUnconditional.pow_le_self_of_unit_interval {x : ℝ} {n : ℕ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hn : 1 ≤ n) : x ^ n ≤ x := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  rw [pow_succ]
  calc
    x ^ k * x ≤ 1 * x :=
      mul_le_mul_of_nonneg_right (pow_le_one₀ hx0 hx1) hx0
    _ = x := by ring

/-- Uniform coefficient in the unconditional one-step estimate. -/
def lAmtOneStepConstant (β C₀ : ℝ) : ℝ :=
  2 + (Nstar β : ℝ) * C₀ +
    (4 * Real.pi ^ 2 * C₀ * Nstar β * 2 ^ Nstar β) +
    (2 * Nstar β * C₀ * ((Nstar β).factorial : ℝ) *
      2 ^ Nstar β * 2 ^ Nstar β * C₀ ^ 2 * 8 ^ Nstar β)

private theorem OneStepAveragingUnconditional.small_error_xq1 :
  ∀ {β : ℝ} (I : Ingredients β) {m : ℕ}, (1 : ℕ) ≤ m → ∀ {κ : ℝ}, (0 : ℝ) < κ →
  let q : ℝ := epsilon β I.Λ m ^ (2 : ℕ) / (κ * tau β I.Λ m);
  (0 : ℝ) < epsilon β I.Λ m →
  let x : ℝ := (4 : ℝ) * Real.pi ^ (2 : ℕ) * κ / epsilon β I.Λ m ^ (2 : ℕ) * tauP β I.Λ m;
  (1 : ℝ) ≤ x * q
    := by
  intro β I m hm κ hκ q hε x
  have hF5 : 5 ≤ Infra.Ingredients.tauCellFactor β I.Λ m := by
    unfold Infra.Ingredients.tauCellFactor
    have heps := Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt
      I.two_pow_seven_le (m := m - 1)
    have hpow : 0 < epsilon β I.Λ (m - 1) ^ (-delta β) :=
      Real.rpow_pos_of_pos heps _
    have hceil : 1 ≤ ⌈epsilon β I.Λ (m - 1) ^ (-delta β)⌉₊ :=
      Nat.ceil_pos.mpr hpow
    exact_mod_cast (show 5 ≤ 4 *
      ⌈epsilon β I.Λ (m - 1) ^ (-delta β)⌉₊ + 1 by omega)
  have hτratio : tauP β I.Λ m / tau β I.Λ m =
      Infra.Ingredients.tauCellFactor β I.Λ m := by
    rw [Infra.Ingredients.tauP_eq_cellFactor_mul_tau hm]
    field_simp [ne_of_gt (I.tau_pos' m)]
  have hπ : 1 ≤ 4 * Real.pi ^ 2 := by
    have hπ1 : (1 : ℝ) ≤ Real.pi ^ 2 :=
      one_le_pow₀ (le_trans (by norm_num) Real.pi_gt_three.le)
    linarith only [hπ1]
  have hprod : x * q =
      (4 * Real.pi ^ 2) * (tauP β I.Λ m / tau β I.Λ m) := by
    dsimp [x, q]
    field_simp [ne_of_gt hκ, ne_of_gt (I.tau_pos' m), ne_of_gt hε]
  rw [hprod, hτratio]
  have hF5real : (5 : ℝ) ≤ Infra.Ingredients.tauCellFactor β I.Λ m := by
    exact_mod_cast hF5
  calc
    1 ≤ 4 * Real.pi ^ 2 := hπ
    _ ≤ 4 * Real.pi ^ 2 * 5 := by
      simpa only [mul_one] using
        (mul_le_mul_of_nonneg_left (by norm_num : (1 : ℝ) ≤ 5)
          (show 0 ≤ 4 * Real.pi ^ 2 by positivity))
    _ ≤ 4 * Real.pi ^ 2 * Infra.Ingredients.tauCellFactor β I.Λ m :=
      mul_le_mul_of_nonneg_left hF5real (by positivity)

private theorem OneStepAveragingUnconditional.small_error_bound2 :
  ∀ {β C₀ : ℝ} (I : Ingredients β) {m : ℕ} {κ : ℝ}, (0 : ℝ) < κ →
  let S : ℝ := a β I.Λ m ^ (2 : ℕ) * epsilon β I.Λ m ^ (4 : ℕ) / κ;
  let q : ℝ := epsilon β I.Λ m ^ (2 : ℕ) / (κ * tau β I.Λ m);
  let e : ℝ := epsilon β I.Λ (m - (1 : ℕ)) ^ delta β;
  let N : ℕ := Nstar β;
  let A : ℝ := (4 : ℝ) * Real.pi ^ (2 : ℕ) * C₀ * (↑N : ℝ) * (2 : ℝ) ^ N;
  let B : ℝ := (2 : ℝ) * (↑N : ℝ) * C₀ * (↑N.factorial : ℝ) * (2 : ℝ) ^ N * (2 : ℝ) ^ N * C₀ ^
    (2 : ℕ) * (8 : ℝ) ^ N;
  (0 : ℝ) < q → (0 : ℝ) ≤ tau β I.Λ m / tauP β I.Λ m → tau β I.Λ m / tauP β I.Λ m ≤ e / (4 : ℝ)
    → (0 : ℝ) < epsilon β I.Λ m → |I.KhomScalar κ m - (κ + (9 / 80 : ℝ) * S)| ≤ (9 / 80 : ℝ) * S
    * ((5 : ℝ) * (tau β I.Λ m / tauP β I.Λ m) + q) + (↑N : ℝ) * (C₀ * S) * q + S * (A * q + B *
    e / (4 : ℝ)) → |I.KhomScalar κ m - (κ + (9 / 80 : ℝ) * S)| ≤ S * ((9 / 80 : ℝ) * (q + (5 :
    ℝ) * e / (4 : ℝ)) + (↑N : ℝ) * C₀ * q + A * q + B * e / (4 : ℝ))
    := by
  intro β C₀ I m κ hκ S q e N A B hq hs0 hsE hε hfinite'
  calc
    _ ≤ (9 / 80) * S * (5 * (tau β I.Λ m / tauP β I.Λ m) + q) +
        (N : ℝ) * (C₀ * S) * q +
          S * (A * q + B * e / 4) := hfinite'
    _ ≤ S * ((9 / 80) * (q + 5 * e / 4) +
        (N : ℝ) * C₀ * q + A * q + B * e / 4) := by
      have hqnon : 0 ≤ q := hq.le
      have hsnon : 0 ≤ tau β I.Λ m / tauP β I.Λ m := hs0
      have hfirst : (9 / 80) * S *
          (5 * (tau β I.Λ m / tauP β I.Λ m) + q) ≤
          S * ((9 / 80) * (q + 5 * e / 4)) := by
        have hinner : 5 * (tau β I.Λ m / tauP β I.Λ m) + q ≤ q + 5 * e / 4 := by
          nlinarith only [hsE]
        calc
          _ ≤ (9 / 80) * S * (q + 5 * e / 4) :=
            mul_le_mul_of_nonneg_left hinner (by positivity)
          _ = _ := by ring
      have hsecond : (N : ℝ) * (C₀ * S) * q = S * ((N : ℝ) * C₀ * q) := by ring
      calc
        _ = (9 / 80) * S *
              (5 * (tau β I.Λ m / tauP β I.Λ m) + q) +
            S * ((N : ℝ) * C₀ * q) + S * (A * q + B * e / 4) := by
          rw [hsecond]
        _ ≤ S * ((9 / 80) * (q + 5 * e / 4)) +
            S * ((N : ℝ) * C₀ * q) + S * (A * q + B * e / 4) := by
          exact add_le_add (add_le_add hfirst (le_refl _)) (le_refl _)
        _ = _ := by ring

private theorem OneStepAveragingUnconditional.small_error_freqle3 :
  ∀ {β : ℝ} (I : Ingredients β) {m : ℕ} {κ : ℝ}, (0 : ℝ) < κ →
  let q : ℝ := epsilon β I.Λ m ^ (2 : ℕ) / (κ * tau β I.Λ m);
  (2 : ℝ) * epsilon β I.Λ m ^ (2 : ℕ) / ((4 : ℝ) * Real.pi ^ (2 : ℕ) * κ * tau β I.Λ m) ≤ q
    := by
  intro β I m κ hκ q
  change 2 * epsilon β I.Λ m ^ 2 /
    (4 * Real.pi ^ 2 * κ * tau β I.Λ m) ≤
      epsilon β I.Λ m ^ 2 / (κ * tau β I.Λ m)
  have hpi : 1 ≤ 2 * Real.pi ^ 2 := by nlinarith only [Real.pi_gt_three]
  have hden : 0 < κ * tau β I.Λ m := mul_pos hκ (I.tau_pos' m)
  have hfactor : 2 ≤ 4 * Real.pi ^ 2 := by nlinarith only [Real.pi_gt_three]
  have hnum' : 2 * epsilon β I.Λ m ^ 2 ≤
      (4 * Real.pi ^ 2) * epsilon β I.Λ m ^ 2 :=
    mul_le_mul_of_nonneg_right hfactor (sq_nonneg (epsilon β I.Λ m))
  have hnum : 2 * epsilon β I.Λ m ^ 2 ≤
      epsilon β I.Λ m ^ 2 * (4 * Real.pi ^ 2) := by
    calc
      _ ≤ (4 * Real.pi ^ 2) * epsilon β I.Λ m ^ 2 := hnum'
      _ = _ := by ring
  have h4piPos : 0 < 4 * Real.pi ^ 2 :=
    mul_pos (by norm_num : (0 : ℝ) < 4) (sq_pos_of_pos Real.pi_pos)
  have hdenL : 0 < 4 * Real.pi ^ 2 * κ * tau β I.Λ m := by
    convert mul_pos h4piPos hden using 1; ring
  apply (div_le_div_iff₀ hdenL hden).2
  calc
    2 * epsilon β I.Λ m ^ 2 * (κ * tau β I.Λ m) ≤
        (epsilon β I.Λ m ^ 2 * (4 * Real.pi ^ 2)) *
          (κ * tau β I.Λ m) := mul_le_mul_of_nonneg_right hnum hden.le
    _ = epsilon β I.Λ m ^ 2 *
        (4 * Real.pi ^ 2 * κ * tau β I.Λ m) := by ring

/-- Small-ratio part of the one-step estimate, retaining both finite
approximation losses and the cutoff-period contribution. -/
theorem OneStepAveragingUnconditional.KhomScalar_one_step_error_small_uniform {β C₀ : ℝ}
    (I : Ingredients β) (hCz : I.Czeta ≤ C₀) (hCh : I.Chat ≤ C₀)
    {m : ℕ} (hm : 1 ≤ m) {κ : ℝ} (hκ : 0 < κ)
    (hsmall : epsilon β I.Λ m ^ 2 / (κ * tau β I.Λ m) ≤ 1 / 2) :
    let S := a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κ
    let q := epsilon β I.Λ m ^ 2 / (κ * tau β I.Λ m)
    |I.KhomScalar κ m - (κ + (9 / 80) * S)| ≤
      lAmtOneStepConstant β C₀ * S *
        (q + epsilon β I.Λ (m - 1) ^ delta β) := by
  dsimp only
  let S := a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κ
  let q := epsilon β I.Λ m ^ 2 / (κ * tau β I.Λ m)
  let e := epsilon β I.Λ (m - 1) ^ delta β
  let N := Nstar β
  let A := 4 * Real.pi ^ 2 * C₀ * N * 2 ^ N
  let B := 2 * N * C₀ * (N.factorial : ℝ) *
    2 ^ N * 2 ^ N * C₀ ^ 2 * 8 ^ N
  let C := lAmtOneStepConstant β C₀
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hq : 0 < q := by
    dsimp [q]
    have hε : 0 < epsilon β I.Λ m :=
      Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
    exact div_pos (by positivity) (mul_pos hκ (I.tau_pos' m))
  have he0 : 0 ≤ e := by
    dsimp [e]
    exact Real.rpow_nonneg (le_of_lt (Infra.Cutoff.epsilon_pos
      I.one_lt_beta I.beta_lt I.two_pow_seven_le)) _
  have hCz0 : 0 ≤ C₀ := le_trans (by linarith [I.one_le_Czeta]) hCz
  have hN : 256 ≤ N := by
    exact Infra.Ingredients.Nstar_ge_256 I.one_lt_beta I.beta_lt
  have hNpos : 1 ≤ N := by omega
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hCge : C ≥ 2 + (N : ℝ) * C₀ + A + B := by
    change 2 + (N : ℝ) * C₀ + A + B ≥
      2 + (N : ℝ) * C₀ + A + B
    exact le_rfl
  have hC2 : 2 ≤ C := by
    have hNC : 0 ≤ (N : ℝ) * C₀ := mul_nonneg (by positivity) hCz0
    linarith [hCge, hNC, hA, hB]
  have hcondition : epsilon β I.Λ m ^ 2 ≤ κ * tau β I.Λ m / 2 := by
    change epsilon β I.Λ m ^ 2 / (κ * tau β I.Λ m) ≤ 1 / 2 at hsmall
    have hden : 0 < κ * tau β I.Λ m := mul_pos hκ (I.tau_pos' m)
    apply (div_le_iff₀ hden).mp at hsmall
    linarith only [hsmall]
  have hfinite := KhomScalar_one_step_error_finite_uniform I hCz hCh hm hκ hcondition
  have hq0 : 0 ≤ q := hq.le
  have hq1 : q ≤ 1 := hsmall.trans (by norm_num)
  have hqpow : q ^ N ≤ q := OneStepAveragingUnconditional.pow_le_self_of_unit_interval hq0 hq1 hNpos
  have hprev : epsilon β I.Λ (m - 1) ≤ 1 :=
    Infra.Construction.epsilon_le_one I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hprevpos : 0 < epsilon β I.Λ (m - 1) :=
    Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hδ : 0 < delta β := Infra.Cutoff.delta_pos I.one_lt_beta I.beta_lt
  have he1 : epsilon β I.Λ (m - 1) ^ delta β ≤ 1 :=
    Real.rpow_le_one hprevpos.le hprev hδ.le
  have hsbound := OneStepAveragingUnconditional.tau_over_tauP_le_prev_delta I hm
  have hs0 : 0 ≤ tau β I.Λ m / tauP β I.Λ m := by
    exact div_nonneg (I.tau_pos' m).le (Infra.Cutoff.tauP_pos
      I.one_lt_beta I.beta_lt I.two_pow_seven_le).le
  have hs1 : tau β I.Λ m / tauP β I.Λ m ≤ 1 := by
    linarith only [hsbound, he1]
  have hspow : (tau β I.Λ m / tauP β I.Λ m) ^ N ≤
      tau β I.Λ m / tauP β I.Λ m :=
    OneStepAveragingUnconditional.pow_le_self_of_unit_interval hs0 hs1 hNpos
  have hsE : tau β I.Λ m / tauP β I.Λ m ≤ e / 4 := by
    change tau β I.Λ m / tauP β I.Λ m ≤
      epsilon β I.Λ (m - 1) ^ delta β / 4
    exact hsbound
  have hsPowE : (tau β I.Λ m / tauP β I.Λ m) ^ N ≤ e / 4 := hspow.trans hsE
  have htauRatio : tauP β I.Λ m / tauPP β I.Λ m =
      tau β I.Λ m / tauP β I.Λ m := by
    have hτ := I.tau_pos' m
    have hF := Infra.Ingredients.tauP_eq_cellFactor_mul_tau
      (β := β) (Λ := I.Λ) hm
    have hF' := Infra.Ingredients.tauPP_eq_cellFactor_mul_tauP
      (β := β) (Λ := I.Λ) hm
    have hFpos : 0 < Infra.Ingredients.tauCellFactor β I.Λ m := by
      unfold Infra.Ingredients.tauCellFactor
      positivity
    have hPpos : 0 < tauP β I.Λ m :=
      Infra.Cutoff.tauP_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
    calc
      tauP β I.Λ m / tauPP β I.Λ m =
          tauP β I.Λ m / (Infra.Ingredients.tauCellFactor β I.Λ m *
            tauP β I.Λ m) := by rw [hF']
      _ = (Infra.Ingredients.tauCellFactor β I.Λ m)⁻¹ := by
        field_simp [ne_of_gt hPpos, ne_of_gt hFpos]
      _ = tau β I.Λ m / tauP β I.Λ m := by
        rw [hF]
        field_simp [ne_of_gt hτ, ne_of_gt hFpos]
  have hε : 0 < epsilon β I.Λ m :=
    Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hρ : 0 < 4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2 := by positivity
  let x := (4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2) * tauP β I.Λ m
  have hx : 0 < x := by
    dsimp [x]
    exact mul_pos (div_pos (by positivity) (by positivity))
      (Infra.Cutoff.tauP_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le)
  have hxq : 1 ≤ x * q := by
    exact @OneStepAveragingUnconditional.small_error_xq1 β I m hm κ hκ hε
  have hexp : Real.exp (-x) ≤ q := by
    have hxexp : x ≤ Real.exp x := by
      exact le_trans (le_add_of_nonneg_right (by norm_num)) (Real.add_one_le_exp x)
    have hinv : (Real.exp x)⁻¹ ≤ x⁻¹ :=
      (inv_le_inv₀ (Real.exp_pos x) hx).mpr hxexp
    have hrecip : x⁻¹ ≤ q := by
      have hdiv : 1 / x ≤ q := (div_le_iff₀ hx).2 (by simpa [mul_comm] using hxq)
      simpa only [one_div] using hdiv
    rw [Real.exp_neg]
    exact hinv.trans hrecip
  have hfreqle : 2 * epsilon β I.Λ m ^ 2 /
      (4 * Real.pi ^ 2 * κ * tau β I.Λ m) ≤ q := by
    exact @OneStepAveragingUnconditional.small_error_freqle3 β I m κ hκ
  have hfirst : (9 / 80) * S *
      (5 * tauP β I.Λ m / tauPP β I.Λ m +
        Real.exp (-(4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2) * tauP β I.Λ m)) ≤
      (9 / 80) * S * (5 * (tau β I.Λ m / tauP β I.Λ m) + q) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ (9 / 80) * S)
    have hratio5 : 5 * tauP β I.Λ m / tauPP β I.Λ m =
        5 * (tau β I.Λ m / tauP β I.Λ m) := by
      calc
        5 * tauP β I.Λ m / tauPP β I.Λ m =
        5 * (tauP β I.Λ m / tauPP β I.Λ m) := by ring
        _ = 5 * (tau β I.Λ m / tauP β I.Λ m) := by rw [htauRatio]
    have harg :
        -(4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2) * tauP β I.Λ m = -x := by
      dsimp [x]
      ring
    rw [hratio5]
    apply add_le_add le_rfl
    rw [harg]
    exact hexp
  have hsecond : (N : ℝ) * (C₀ * S) *
      (2 * epsilon β I.Λ m ^ 2 /
        (4 * Real.pi ^ 2 * κ * tau β I.Λ m)) ≤
      (N : ℝ) * (C₀ * S) * q :=
    mul_le_mul_of_nonneg_left hfreqle (by positivity)
  have hthird : S * (A * q ^ N + B *
      (tau β I.Λ m / tauP β I.Λ m) ^ N) ≤ S * (A * q + B * e / 4) := by
    apply mul_le_mul_of_nonneg_left _ hS
    have hAq := mul_le_mul_of_nonneg_left hqpow hA
    have hBs := mul_le_mul_of_nonneg_left hsPowE hB
    have hBs' : B * (tau β I.Λ m / tauP β I.Λ m) ^ N ≤ B * e / 4 := by
      calc
        B * (tau β I.Λ m / tauP β I.Λ m) ^ N ≤ B * (e / 4) := hBs
        _ = B * e / 4 := by ring
    exact add_le_add hAq hBs'
  have hfinite' : |I.KhomScalar κ m - (κ + (9 / 80) * S)| ≤
      (9 / 80) * S *
          (5 * tauP β I.Λ m / tauPP β I.Λ m +
            Real.exp (-(4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2) * tauP β I.Λ m)) +
        (N : ℝ) * (C₀ * S) *
          (2 * epsilon β I.Λ m ^ 2 /
            (4 * Real.pi ^ 2 * κ * tau β I.Λ m)) +
        S * (A * q ^ N + B * (tau β I.Λ m / tauP β I.Λ m) ^ N) := by
    convert hfinite using 1; ring
  have hfinite'' : |I.KhomScalar κ m - (κ + (9 / 80) * S)| ≤
      (9 / 80) * S * (5 * (tau β I.Λ m / tauP β I.Λ m) + q) +
      (N : ℝ) * (C₀ * S) * q + S * (A * q + B * e / 4) := by
    calc
      _ ≤ (9 / 80) * S *
            (5 * tauP β I.Λ m / tauPP β I.Λ m +
              Real.exp (-(4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2) * tauP β I.Λ m)) +
          (N : ℝ) * (C₀ * S) *
            (2 * epsilon β I.Λ m ^ 2 /
              (4 * Real.pi ^ 2 * κ * tau β I.Λ m)) +
          S * (A * q ^ N + B * (tau β I.Λ m / tauP β I.Λ m) ^ N) := hfinite'
      _ ≤ _ :=
        add_le_add (add_le_add hfirst hsecond) hthird
  have hfinite' := hfinite''
  have hbound : |I.KhomScalar κ m - (κ + (9 / 80) * S)| ≤
      S * ((9 / 80) * (q + 5 * e / 4) +
        (N : ℝ) * C₀ * q + A * q + B * e / 4) := by
    exact @OneStepAveragingUnconditional.small_error_bound2 β C₀ I m κ hκ hq hs0 hsE hε hfinite'
  have hcoefQ : (9 / 80) + (N : ℝ) * C₀ + A ≤ C := by
    have hsmallQ : (9 / 80 : ℝ) ≤ 2 := by norm_num
    have hNC : 0 ≤ (N : ℝ) * C₀ := mul_nonneg (by positivity) hCz0
    have hcoef : (9 / 80) + (N : ℝ) * C₀ + A ≤
        2 + (N : ℝ) * C₀ + A + B := by
      nlinarith only [hB, hA, hNC, hsmallQ]
    exact hcoef.trans hCge
  have hcoefE : (9 / 80) * (5 / 4) + B / 4 ≤ C := by
    have hsmallcoef : (9 / 80) * (5 / 4) ≤ 1 := by norm_num
    have hBpart : B / 4 ≤ B := by nlinarith only [hB]
    have hNC : 0 ≤ (N : ℝ) * C₀ := mul_nonneg (by positivity) hCz0
    have hcoef : (9 / 80) * (5 / 4) + B / 4 ≤
        2 + (N : ℝ) * C₀ + A + B := by
      nlinarith only [hB, hsmallcoef, hBpart, hNC, hA]
    exact hcoef.trans hCge
  have hcombine : (9 / 80) * (q + 5 * e / 4) +
      (N : ℝ) * C₀ * q + A * q + B * e / 4 ≤ C * (q + e) := by
    rw [show (9 / 80) * (q + 5 * e / 4) +
        (N : ℝ) * C₀ * q + A * q + B * e / 4 =
          ((9 / 80) + (N : ℝ) * C₀ + A) * q +
            ((9 / 80) * (5 / 4) + B / 4) * e by ring]
    rw [show C * (q + e) = C * q + C * e by ring]
    exact add_le_add (mul_le_mul_of_nonneg_right hcoefQ hq.le)
      (mul_le_mul_of_nonneg_right hcoefE he0)
  rw [show C * S * (q + e) = S * (C * (q + e)) by ring]
  exact hbound.trans (mul_le_mul_of_nonneg_left hcombine hS)

/-- One-step averaging estimate for the actual scalar flux, valid at every
positive input diffusivity. It retains both finite-regularity losses and
converts the cutoff-period loss to `ε_(m-1)^δ`; the large-ratio case follows
from the pointwise flux cap. -/
theorem KhomScalar_one_step_error_unconditional {β C₀ : ℝ}
    (I : Ingredients β) (hCz : I.Czeta ≤ C₀) (hCh : I.Chat ≤ C₀)
    {m : ℕ} (hm : 1 ≤ m) {κ : ℝ} (hκ : 0 < κ) :
    let S := a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κ
    let q := epsilon β I.Λ m ^ 2 / (κ * tau β I.Λ m)
    |I.KhomScalar κ m - (κ + (9 / 80) * S)| ≤
      lAmtOneStepConstant β C₀ * S *
        (q + epsilon β I.Λ (m - 1) ^ delta β) := by
  dsimp only
  let S := a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κ
  let q := epsilon β I.Λ m ^ 2 / (κ * tau β I.Λ m)
  let e := epsilon β I.Λ (m - 1) ^ delta β
  let C := lAmtOneStepConstant β C₀
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hqpos : 0 < q := by
    dsimp [q]
    have hε : 0 < epsilon β I.Λ m :=
      Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
    exact div_pos (by positivity) (mul_pos hκ (I.tau_pos' m))
  have he0 : 0 ≤ e := by
    dsimp [e]
    exact Real.rpow_nonneg (le_of_lt (Infra.Cutoff.epsilon_pos
      I.one_lt_beta I.beta_lt I.two_pow_seven_le)) _
  have hC₀ : 0 ≤ C₀ := le_trans (by linarith [I.one_le_Czeta]) hCz
  have hC2 : 2 ≤ C := by
    have htail : 0 ≤ (Nstar β : ℝ) * C₀ +
        (4 * Real.pi ^ 2 * C₀ * Nstar β * 2 ^ Nstar β) +
        (2 * Nstar β * C₀ * ((Nstar β).factorial : ℝ) *
          2 ^ Nstar β * 2 ^ Nstar β * C₀ ^ 2 * 8 ^ Nstar β) := by
      positivity
    dsimp [C, lAmtOneStepConstant]
    linarith [htail]
  by_cases hsmall : q ≤ 1 / 2
  · exact OneStepAveragingUnconditional.KhomScalar_one_step_error_small_uniform I hCz hCh hm hκ
      hsmall
  · have hlarge : 1 / 2 < q := lt_of_not_ge hsmall
    have hlow := khomScalar_ge_input I hm κ hκ
    have hhigh := khomScalar_le_input_add_amplitude I hm κ hκ
    have hhigh' : I.KhomScalar κ m ≤ κ + S / 2 := by
      calc
        I.KhomScalar κ m ≤ κ +
            a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / (2 * κ) := hhigh
        _ = κ + S / 2 := by dsimp [S]; ring
    have htargetLower : κ ≤ κ + (9 / 80) * S := by nlinarith only [hS]
    have htargetUpper : κ + (9 / 80) * S ≤ κ + S / 2 := by
      nlinarith only [hS]
    have hdiff : |I.KhomScalar κ m - (κ + (9 / 80) * S)| ≤ S / 2 := by
      rw [abs_le]
      constructor <;> linarith only [hlow, hhigh', htargetLower, htargetUpper]
    have hCnon : 0 ≤ C := le_trans (by norm_num : (0 : ℝ) ≤ 2) hC2
    have hCq : 1 ≤ C * q := by
      have hhalf : 1 ≤ C / 2 := by linarith only [hC2]
      have hmul : C * (1 / 2) ≤ C * q :=
        mul_le_mul_of_nonneg_left (le_of_lt hlarge) hCnon
      nlinarith only [hhalf, hmul]
    have hrate : S / 2 ≤ C * S * (q + e) := by
      calc
        S / 2 ≤ S := by nlinarith only [hS]
        _ ≤ S * (C * q) := by nlinarith only [hS, hCq]
        _ ≤ S * (C * (q + e)) := by
          apply mul_le_mul_of_nonneg_left
          · exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right he0) hCnon
          · exact hS
        _ = C * S * (q + e) := by ring
    exact hdiff.trans hrate

end AVenhance.Infra.Section3

end
