/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.LeadingErrorFlow

/-! # The derivative of the transition cutoff `ξ_{m,k}`

`ξ_{m,k}'(t) ≠ 0` forces `ξ_{m,k}(t) ≠ 0` and `3/4 ≤ |t/τ_m - k|` (both extrema of `ξ` have zero
derivative), and `|ξ_{m,k}'| ≤ C_ξ / τ_m`. -/

@[expose] public section

open Homogenization

noncomputable section

namespace AVenhance.Infra.Section5.Contracts

open AVenhance

theorem sb_one_le_Nstar {β : ℝ} (hβ : 1 < β) (hβ' : β < 4 / 3) : 1 ≤ Nstar β := by
  have h := Infra.Ingredients.Nstar_ge_eight_add_div hβ hβ'
  have hq := Infra.Ingredients.one_lt_q hβ hβ'
  have hd : 0 ≤ 128 * q β ^ 2 / (q β - 1) :=
    div_nonneg (by positivity) (by linarith)
  have : (1 : ℝ) ≤ (Nstar β : ℝ) := by linarith
  exact_mod_cast this

theorem sb_xi_nonneg_le_one {β : ℝ} (I : Ingredients β) (s : ℝ) : 0 ≤ I.xi s ∧ I.xi s ≤ 1 := by
  have h1 := I.ind_le_xi s
  have h2 := I.xi_le_ind s
  have h3 : 0 ≤ indIcc (-(3 / 4) : ℝ) (3 / 4) s := indIcc_nonneg' _ _ _
  have h4 : indIcc (-(5 / 4) : ℝ) (5 / 4) s ≤ 1 := by
    by_cases h : s ∈ Set.Icc (-(5 / 4) : ℝ) (5 / 4) <;> simp [indIcc, h]
  exact ⟨h3.trans h1, h2.trans h4⟩

/-- `ξ' (s) ≠ 0` forces `ξ s ∈ (0,1)`-type support information. -/
theorem sb_deriv_xi_ne_zero {β : ℝ} (I : Ingredients β) {s : ℝ} (h : deriv I.xi s ≠ 0) :
    I.xi s ≠ 0 ∧ 3 / 4 < |s| := by
  have hsm := I.xi_smooth.differentiable (by simp)
  constructor
  · intro h0
    apply h
    have hmin : IsLocalMin I.xi s := Filter.Eventually.of_forall fun y => by
      rw [h0]; exact (sb_xi_nonneg_le_one I y).1
    exact hmin.deriv_eq_zero
  · by_contra hc
    rw [not_lt] at hc
    apply h
    have hs : s ∈ Set.Icc (-(3 / 4) : ℝ) (3 / 4) := abs_le.1 hc
    have h1 : 1 ≤ I.xi s := by
      have := I.ind_le_xi s
      simpa [indIcc, hs] using this
    have hmax : IsLocalMax I.xi s := Filter.Eventually.of_forall fun y => by
      have := (sb_xi_nonneg_le_one I y).2
      linarith [(sb_xi_nonneg_le_one I s).2]
    exact hmax.deriv_eq_zero

theorem sb_deriv_xiMK {β : ℝ} (I : Ingredients β) (m : ℕ) (k : ℤ) (t : ℝ) :
    deriv (I.xiMK m k) t =
      deriv I.xi ((t - (k : ℝ) * tau β I.Λ m) / tau β I.Λ m) * (tau β I.Λ m)⁻¹ := by
  have hτ := I.tau_pos' m
  have hx := (I.xi_smooth.differentiable (by simp)) ((t - (k : ℝ) * tau β I.Λ m) / tau β I.Λ m)
  have hin : HasDerivAt (fun t : ℝ => (t - (k : ℝ) * tau β I.Λ m) / tau β I.Λ m)
      (tau β I.Λ m)⁻¹ t := by
    simpa using ((hasDerivAt_id t).sub_const ((k : ℝ) * tau β I.Λ m)).div_const (tau β I.Λ m)
  have := hx.hasDerivAt.comp t hin
  exact this.deriv

/-- Support and size of `ξ'_{m,k}`. -/
theorem sb_deriv_xiMK_facts {β : ℝ} (I : Ingredients β) {m : ℕ} (k : ℤ) {t : ℝ}
    (h : deriv (I.xiMK m k) t ≠ 0) :
    I.xiMK m k t ≠ 0 ∧
      (((k : ℝ) + 3 / 4) * tau β I.Λ m ≤ t ∨ t ≤ ((k : ℝ) - 3 / 4) * tau β I.Λ m) ∧
      |deriv (I.xiMK m k) t| ≤ I.Cxi / tau β I.Λ m := by
  have hτ := I.tau_pos' m
  rw [sb_deriv_xiMK] at h
  have hd : deriv I.xi ((t - (k : ℝ) * tau β I.Λ m) / tau β I.Λ m) ≠ 0 :=
    left_ne_zero_of_mul h
  obtain ⟨h1, h2⟩ := sb_deriv_xi_ne_zero I hd
  refine ⟨h1, ?_, ?_⟩
  · set u := (t - (k : ℝ) * tau β I.Λ m) / tau β I.Λ m with hu
    have htu : t = (k : ℝ) * tau β I.Λ m + u * tau β I.Λ m := by
      rw [hu]; field_simp; ring
    rcases lt_abs.1 h2 with h3 | h3
    · left; rw [htu]; nlinarith
    · right; rw [htu]; nlinarith
  · rw [sb_deriv_xiMK, abs_mul, abs_of_pos (inv_pos.2 hτ)]
    have h1 := I.xi_deriv_le 1 (sb_one_le_Nstar I.one_lt_beta I.beta_lt)
      ((t - (k : ℝ) * tau β I.Λ m) / tau β I.Λ m)
    rw [iteratedDeriv_one] at h1
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right h1 (inv_nonneg.2 hτ.le)

end AVenhance.Infra.Section5.Contracts
end
