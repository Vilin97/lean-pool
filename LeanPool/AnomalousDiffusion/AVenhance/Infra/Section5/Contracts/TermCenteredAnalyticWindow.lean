/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.LeadingErrorFlow

/-! # Flow-slice identification and time window on `supp ξ_{m,k}`

Shared basics for the analytic inputs of the centered ergodic estimates: the actual flow slices
are the Section 2 flows started at `s = l_k τ''_m` run for time `t - s`, the time `t - s` lies in
the Section 2 window, and the window gives the sharp smallness `2^23 |t - s| a_{m-1} ≤
    ε_{m-1}^{2δ}/4`. -/

@[expose] public section

open MeasureTheory Homogenization
open scoped ContDiff

noncomputable section

namespace AVenhance.Infra.Section5.Contracts

open AVenhance AVenhance.Infra.Construction AVenhance.Infra.Section5

section Slices

variable {β : ℝ} {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}

theorem sdw_xFlow_slice_eq (hΦ : IsStreamSeq I Φ) (m : ℕ) (l : ℤ) (t : ℝ) :
    (fun y => I.xFlow hΦ m l t y) = fun y =>
      constructionFlow hΦ (m - 1) (((l : ℝ) * tauPP β I.Λ m) + (t - (l : ℝ) * tauPP β I.Λ m))
        y ((l : ℝ) * tauPP β I.Λ m) := by
  funext y
  rw [add_sub_cancel]
  rfl

theorem sdw_xFlowInv_slice_eq (hΦ : IsStreamSeq I Φ) (m : ℕ) (l : ℤ) (t : ℝ) :
    (fun y => I.xFlowInv hΦ m l t y) = fun y =>
      constructionFlowInv hΦ (m - 1)
        (((l : ℝ) * tauPP β I.Λ m) + (t - (l : ℝ) * tauPP β I.Λ m))
        y ((l : ℝ) * tauPP β I.Λ m) := by
  funext y
  rw [add_sub_cancel]
  rfl

end Slices

/-- Abstract-real scale arithmetic: if `x ≤ 2^{-25} e^{2-b+2δ}` then `2^23 x e^{b-2} ≤ e^{2δ}/4`. -/
theorem sdw_scale_arith {e b x d : ℝ} (he : 0 < e)
    (hx : x ≤ 2 ^ (-25 : ℤ) * e ^ (2 - b + 2 * d)) :
    2 ^ 23 * x * e ^ (b - 2) ≤ e ^ (2 * d) / 4 := by
  have hmul : e ^ (2 - b + 2 * d) * e ^ (b - 2) = e ^ (2 * d) := by
    rw [← Real.rpow_add he]
    congr 1
    ring
  have hpos : 0 ≤ e ^ (b - 2) := (Real.rpow_pos_of_pos he _).le
  have h2 : (2 : ℝ) ^ 23 * 2 ^ (-25 : ℤ) = 1 / 4 := by norm_num
  calc
    2 ^ 23 * x * e ^ (b - 2)
        ≤ 2 ^ 23 * (2 ^ (-25 : ℤ) * e ^ (2 - b + 2 * d)) * e ^ (b - 2) := by gcongr
    _ = ((2 : ℝ) ^ 23 * 2 ^ (-25 : ℤ)) * (e ^ (2 - b + 2 * d) * e ^ (b - 2)) := by ring
    _ = e ^ (2 * d) / 4 := by rw [h2, hmul]; ring

/-- Abstract-real scale arithmetic: `2^{-25} e^{2-b+2δ} ≤ 2^{-25} (e^{b-2})⁻¹` for `e ≤ 1`,
`0 ≤ δ`. -/
theorem sdw_scale_window {e b x d : ℝ} (he : 0 < e) (he1 : e ≤ 1) (hd : 0 ≤ d)
    (hx : x ≤ 2 ^ (-25 : ℤ) * e ^ (2 - b + 2 * d)) :
    x ≤ 2 ^ (-25 : ℤ) * (e ^ (b - 2))⁻¹ := by
  have hpow : e ^ (2 - b + 2 * d) ≤ e ^ (2 - b) :=
    Real.rpow_le_rpow_of_exponent_ge he he1 (by linarith)
  have hinv : (e ^ (b - 2))⁻¹ = e ^ (2 - b) := by
    rw [show 2 - b = -(b - 2) by ring, Real.rpow_neg he.le]
  rw [hinv]
  exact hx.trans (mul_le_mul_of_nonneg_left hpow (by positivity))

theorem sdw_eps_pos {β : ℝ} (I : Ingredients β) (n : ℕ) : 0 < epsilon β I.Λ n :=
  Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt (by exact_mod_cast I.two_pow_seven_le)

theorem sdw_eps_le_one {β : ℝ} (I : Ingredients β) (n : ℕ) : epsilon β I.Λ n ≤ 1 :=
  Infra.Construction.epsilon_le_one I.one_lt_beta I.beta_lt
    (by exact_mod_cast I.two_pow_seven_le)

/-- Flow-time window and the resulting smallness `2^23 |t - l_kτ''| a_{m-1} ≤ ε_{m-1}^{2δ}/4`. -/
theorem sdw_flow_window_scale {β : ℝ} (I : Ingredients β) {m : ℕ} (hm : 2 ≤ m) (k : ℤ)
    {t : ℝ} (hξ : I.xiMK m k t ≠ 0) :
    |t - (lIdx β I.Λ m k : ℝ) * tauPP β I.Λ m| ≤
        2 ^ (-25 : ℤ) * (a β I.Λ (m - 1))⁻¹ ∧
      2 ^ 23 * |t - (lIdx β I.Λ m k : ℝ) * tauPP β I.Λ m| * a β I.Λ (m - 1) ≤
        epsilon β I.Λ (m - 1) ^ (2 * delta β) / 4 := by
  have hwin := RelativeError.xi_flow_time_window_tauPP I hm k hξ
  have hpp := Infra.Ingredients.tauPP_bounds I.one_lt_beta I.beta_lt
    (by exact_mod_cast I.two_pow_seven_le) (by omega : 1 ≤ m)
  have hx := hwin.trans hpp.2
  have he := sdw_eps_pos I (m - 1)
  have he1 := sdw_eps_le_one I (m - 1)
  have hδ : 0 < delta β := Infra.Ingredients.delta_pos I.one_lt_beta I.beta_lt
  exact ⟨sdw_scale_window he he1 hδ.le hx, sdw_scale_arith he hx⟩

end AVenhance.Infra.Section5.Contracts
end
