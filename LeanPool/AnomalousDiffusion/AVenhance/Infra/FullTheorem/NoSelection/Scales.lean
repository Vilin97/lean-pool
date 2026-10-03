/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.LebronStep.KappaBounds
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.AssemblyScales

/-! # Abstract-real scale lemmas for the separated-chains argument

Pure real algebra (no stream sequences): the choice of the cosine mode in a window
`[E^s, c₁ E^{s-d}]`, the exponent bookkeeping `λ E^{2s} ≤ 1`, `E^{2d} ≤ c₁² λ E^{2s}`, the passage
from a log-ratio near `log 4` to a ratio in `[3,5]`, the geometric sum, and the decay of the scales
`ε_m → 0`. -/

@[expose] public section

open Filter Topology

noncomputable section

namespace AVenhance.Infra.FullTheorem.NoSel

/-- `C (x⁻¹)^ρ ≤ θ` for all large `x`. -/
theorem exists_big (C θ ρ : ℝ) (hρ : 0 < ρ) (hθ : 0 < θ) :
    ∃ Λ₀ : ℝ, ∀ x : ℝ, Λ₀ ≤ x → C * (x⁻¹) ^ ρ ≤ θ := by
  have h1 : Tendsto (fun x : ℝ => (x⁻¹) ^ ρ) atTop (𝓝 0) := by
    have := tendsto_inv_atTop_zero.rpow_const (p := ρ) (Or.inr hρ.le)
    simpa [Real.zero_rpow hρ.ne'] using this
  have h2 : Tendsto (fun x : ℝ => C * (x⁻¹) ^ ρ) atTop (𝓝 0) := by
    simpa using h1.const_mul C
  obtain ⟨Λ₀, h⟩ := eventually_atTop.1 (h2.eventually (gt_mem_nhds hθ))
  exact ⟨Λ₀, fun x hx => (h x hx).le⟩

/-- Monotonicity used to pass from `ε ≤ x⁻¹` to the smallness condition. -/
theorem mul_rpow_le_inv {C ε x ρ : ℝ} (hC : 0 ≤ C) (hε : 0 ≤ ε) (hεx : ε ≤ x⁻¹) (hρ : 0 ≤ ρ) :
    C * ε ^ ρ ≤ C * (x⁻¹) ^ ρ :=
  mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hε hεx hρ) hC

/-- A cosine mode `n` with `L_n := 1/(2πn)` in the window `[E^s, c₁ E^{s-d}]`, and `n` large. -/
theorem exists_mode {c₁ E s d : ℝ} (hc₁ : 0 < c₁) (hE : 0 < E)
    (hE2 : 2 * E ^ d ≤ c₁) (hX : 2 * Real.pi * (c₁ * E ^ (s - d)) ≤ 1 / 2) :
    ∃ n : ℕ, 1 ≤ n ∧ E ^ s ≤ 1 / (2 * Real.pi * n) ∧
      1 / (2 * Real.pi * n) ≤ c₁ * E ^ (s - d) ∧
      1 / (2 * Real.pi * (c₁ * E ^ (s - d))) ≤ n := by
  set X := c₁ * E ^ (s - d) with hXdef
  have hX0 : 0 < X := mul_pos hc₁ (Real.rpow_pos_of_pos hE _)
  set P := 2 * Real.pi * X with hP
  have hP0 : 0 < P := by positivity
  set n : ℕ := ⌈1 / P⌉₊ with hn
  have hn1 : 1 / P ≤ (n : ℝ) := Nat.le_ceil _
  have hn2 : (n : ℝ) < 1 / P + 1 := Nat.ceil_lt_add_one (by positivity)
  have h2P : (2 : ℝ) ≤ 1 / P := by
    rw [le_div_iff₀ hP0]; linarith
  have hn2' : (2 : ℝ) ≤ n := h2P.trans hn1
  have hnpos : (0 : ℝ) < n := by linarith
  refine ⟨n, by exact_mod_cast (by linarith : (1 : ℝ) ≤ n), ?_, ?_, hn1⟩
  · rw [le_div_iff₀ (by positivity)]
    have hEs : E ^ s ≤ X / 2 := by
      have : E ^ s = E ^ (s - d) * E ^ d := by rw [← Real.rpow_add hE]; ring_nf
      rw [this, hXdef]
      have h0 : 0 ≤ E ^ (s - d) := Real.rpow_nonneg hE.le _
      nlinarith
    have hPn : P * n < 3 / 2 := by
      calc P * n < P * (1 / P + 1) := mul_lt_mul_of_pos_left hn2 hP0
        _ = 1 + P := by field_simp
        _ ≤ 3 / 2 := by linarith
    calc E ^ s * (2 * Real.pi * n) ≤ X / 2 * (2 * Real.pi * n) :=
          mul_le_mul_of_nonneg_right hEs (by positivity)
      _ = (P * n) / 2 := by rw [hP]; ring
      _ ≤ 1 := by linarith
  · rw [div_le_iff₀ (by positivity)]
    have : 1 ≤ P * n := by
      have := mul_le_mul_of_nonneg_left hn1 hP0.le
      rwa [mul_one_div_cancel hP0.ne'] at this
    calc (1 : ℝ) ≤ P * n := this
      _ = X * (2 * Real.pi * n) := by rw [hP]; ring

/-- Exponent bookkeeping for the cosine window. -/
theorem scale_algebra {E L lam c₁ s d : ℝ} (hE : 0 < E) (hL : 0 < L) (hlam : lam * L ^ 2 = 1)
    (hlo : E ^ s ≤ L) (hup : L ≤ c₁ * E ^ (s - d)) :
    lam * E ^ (2 * s) ≤ 1 ∧ E ^ (2 * d) ≤ c₁ ^ 2 * (lam * E ^ (2 * s)) := by
  have hlam0 : 0 ≤ lam := by
    by_contra h
    have : lam * L ^ 2 < 0 := mul_neg_of_neg_of_pos (not_le.mp h) (by positivity)
    linarith
  have hsq : ∀ r : ℝ, E ^ (2 * r) = (E ^ r) ^ 2 := by
    intro r
    rw [mul_comm, Real.rpow_mul hE.le, Real.rpow_two]
  constructor
  · rw [hsq]
    calc lam * (E ^ s) ^ 2 ≤ lam * L ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Real.rpow_nonneg hE.le _) hlo 2) hlam0
      _ = 1 := hlam
  · have h1 : L ^ 2 ≤ c₁ ^ 2 * E ^ (2 * (s - d)) := by
      rw [hsq, ← mul_pow]
      exact pow_le_pow_left₀ hL.le hup 2
    have h2 : E ^ (2 * s) = E ^ (2 * (s - d)) * E ^ (2 * d) := by
      rw [← Real.rpow_add hE]; ring_nf
    have h3 : 0 ≤ E ^ (2 * d) := Real.rpow_nonneg hE.le _
    have h4 : 1 ≤ lam * (c₁ ^ 2 * E ^ (2 * (s - d))) := by
      calc (1 : ℝ) = lam * L ^ 2 := hlam.symm
        _ ≤ _ := mul_le_mul_of_nonneg_left h1 hlam0
    calc E ^ (2 * d) = 1 * E ^ (2 * d) := (one_mul _).symm
      _ ≤ lam * (c₁ ^ 2 * E ^ (2 * (s - d))) * E ^ (2 * d) :=
          mul_le_mul_of_nonneg_right h4 h3
      _ = c₁ ^ 2 * (lam * E ^ (2 * s)) := by rw [h2]; ring

/-- A log-ratio within `log (5/4)` of `log 4` forces the ratio into `[3,5]`. -/
theorem ratio_of_log {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h : |Real.log (b / a) - Real.log 4| ≤ Real.log (5 / 4)) : 3 * a ≤ b ∧ b ≤ 5 * a := by
  have hba : 0 < b / a := div_pos hb ha
  obtain ⟨h1, h2⟩ := abs_le.1 h
  have e1 : Real.log 4 + Real.log (5 / 4) = Real.log 5 := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have e2 : Real.log 4 - Real.log (5 / 4) = Real.log (16 / 5) := by
    rw [← Real.log_div (by norm_num) (by norm_num)]; norm_num
  have hu : Real.log (b / a) ≤ Real.log 5 := by linarith
  have hl : Real.log (16 / 5) ≤ Real.log (b / a) := by linarith
  rw [Real.log_le_log_iff hba (by norm_num)] at hu
  rw [Real.log_le_log_iff (by norm_num) hba] at hl
  rw [div_le_iff₀ ha] at hu
  rw [le_div_iff₀ ha] at hl
  constructor <;> linarith

/-- Reverse ratio: `|log (b/a) + log 4| ≤ log (5/4)` gives `3 b ≤ a ≤ 5 b`. -/
theorem ratio_of_log' {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h : |Real.log (b / a) + Real.log 4| ≤ Real.log (5 / 4)) : 3 * b ≤ a ∧ a ≤ 5 * b := by
  refine ratio_of_log hb ha ?_
  have : Real.log (a / b) = -Real.log (b / a) := by
    rw [← Real.log_inv, inv_div]
  rw [this]
  have e : |-Real.log (b / a) - Real.log 4| = |Real.log (b / a) + Real.log 4| := by
    rw [← abs_neg]; congr 1; ring
  rw [e]; exact h

/-- Triangle bookkeeping of the final comparison. -/
theorem final_ineq {a b v₁ v₂ u₁ u₂ G τ e : ℝ} (h1 : |a - v₁| ≤ τ) (h2 : |b - v₂| ≤ τ)
    (h3 : |v₁ - u₁| ≤ e) (h4 : |v₂ - u₂| ≤ e) (hG : G ≤ |u₁ - u₂|) :
    G - 2 * τ - 2 * e ≤ |a - b| := by
  obtain ⟨a1, a2⟩ := abs_le.1 h1
  obtain ⟨b1, b2⟩ := abs_le.1 h2
  obtain ⟨c1, c2⟩ := abs_le.1 h3
  obtain ⟨d1, d2⟩ := abs_le.1 h4
  have : |u₁ - u₂| ≤ |a - b| + 2 * τ + 2 * e := by
    rw [abs_le]
    have := neg_abs_le (a - b)
    have := le_abs_self (a - b)
    constructor <;> linarith
  linarith

/-- Geometric sum `∑_{l ∈ (n₀, M]} a (l-1) ≤ 2 a n₀`. -/
theorem geom_sum_le {a : ℕ → ℝ} {n₀ : ℕ}
    (hr : ∀ k, n₀ ≤ k → a (k + 1) ≤ a k / 2) (M : ℕ) (hM : n₀ ≤ M) :
    ∑ l ∈ Finset.Ioc n₀ M, a (l - 1) ≤ 2 * a n₀ - 2 * a M := by
  induction M, hM using Nat.le_induction with
  | base => simp
  | succ M hM ih =>
    rw [Finset.sum_Ioc_succ_top (by omega)]
    have := hr M hM
    simp only [Nat.add_sub_cancel]
    linarith

/-- `ε_m → 0`. -/
theorem epsilon_tendsto {β : ℝ} {Λ : ℕ} (hβ : 1 < β) (hβ' : β < 4 / 3) (hΛ : 2 ^ 7 ≤ Λ) :
    Tendsto (fun m : ℕ => epsilon β Λ m) atTop (𝓝 0) := by
  have hΛ1 : (Λ : ℝ)⁻¹ < 1 := by
    have : (1 : ℝ) < Λ := by
      have : (2 : ℝ) ^ 7 ≤ Λ := by exact_mod_cast hΛ
      linarith
    exact inv_lt_one_of_one_lt₀ this
  have hΛpos : (0 : ℝ) < Λ := by
    have : (2 : ℝ) ^ 7 ≤ Λ := by exact_mod_cast hΛ
    linarith
  have hlim : Tendsto (fun m : ℕ => ((Λ : ℝ)⁻¹) ^ m) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (inv_nonneg.2 hΛpos.le) hΛ1
  refine squeeze_zero (fun m => (Infra.Cutoff.epsilon_pos hβ hβ' hΛ).le) (fun m => ?_) hlim
  have := Infra.Ingredients.epsilon_le_lambda_pow (m := m) hβ hβ' hΛ
  refine this.trans (le_of_eq ?_)
  rw [Real.rpow_neg hΛpos.le, Real.rpow_natCast, inv_pow]

/-- `K ε_M^a ≤ X` for all large `M`. -/
theorem epsilon_rpow_eventually {β : ℝ} {Λ : ℕ} (hβ : 1 < β) (hβ' : β < 4 / 3)
    (hΛ : 2 ^ 7 ≤ Λ) {a X : ℝ} (K : ℝ) (ha : 0 < a) (hX : 0 < X) :
    ∃ J : ℕ, ∀ M : ℕ, J ≤ M → K * epsilon β Λ M ^ a ≤ X := by
  have h1 := (epsilon_tendsto hβ hβ' hΛ).rpow_const (p := a) (Or.inr ha.le)
  have h2 : Tendsto (fun m : ℕ => K * epsilon β Λ m ^ a) atTop (𝓝 0) := by
    simpa [Real.zero_rpow ha.ne'] using h1.const_mul K
  obtain ⟨J, h⟩ := eventually_atTop.1 (h2.eventually (gt_mem_nhds hX))
  exact ⟨J, fun M hM => (h M hM).le⟩

/-- Some large level has `c₁ ε_m^e` small. -/
theorem epsilon_exists_small {β : ℝ} {Λ : ℕ} (hβ : 1 < β) (hβ' : β < 4 / 3)
    (hΛ : 2 ^ 7 ≤ Λ) {e X : ℝ} (c₁ : ℝ) (he : 0 < e) (hX : 0 < X) (N₀ : ℕ) :
    ∃ m : ℕ, N₀ ≤ m ∧ c₁ * epsilon β Λ m ^ e < X := by
  have h1 := (epsilon_tendsto hβ hβ' hΛ).rpow_const (p := e) (Or.inr he.le)
  have h2 : Tendsto (fun m : ℕ => c₁ * epsilon β Λ m ^ e) atTop (𝓝 0) := by
    simpa [Real.zero_rpow he.ne'] using h1.const_mul c₁
  obtain ⟨J, h⟩ := eventually_atTop.1 (h2.eventually (gt_mem_nhds hX))
  exact ⟨max J N₀, le_max_right _ _, h _ (le_max_left _ _)⟩

end AVenhance.Infra.FullTheorem.NoSel
