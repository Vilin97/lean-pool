/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ingredients.Parameters
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Numeric.Exponents

/-! # Exponent budget for the `tiny` source contract

`δ N_* ≥ 10 + q β`: the `N_*` is large enough to absorb every negative power of
`ε_{m-1}` (the lower bound `ε_m ≳ ε_{m-1}^q` and the analytic-radius losses) occurring in the
estimate of `e.monster.est.tiny` (`enhance.tex` 7848-7930). -/

@[expose] public section

open Homogenization

noncomputable section

namespace AVenhance.Infra.Section5.Contracts

open AVenhance

/-- Abstract-real core, in terms of `q > 1` only: if `δ = (q-1)²/(4(q+1)(4q-1))` and
`N ≥ 500/δ + 128 q²(q-1)` then `10 + 4q/3 ≤ δ N`. -/
theorem sc_budget_core {q δ N : ℝ} (hq : 1 < q)
    (hδ : δ = (q - 1) ^ 2 / (4 * (q + 1) * (4 * q - 1)))
    (hN : 500 / δ + 128 * q ^ 2 * (q - 1) ≤ N) :
    10 + 4 * q / 3 ≤ δ * N := by
  have hq1 : 0 < q - 1 := by linarith
  have hden : 0 < 4 * (q + 1) * (4 * q - 1) := by
    have : 0 < 4 * q - 1 := by linarith
    positivity
  have hδpos : 0 < δ := by rw [hδ]; positivity
  have hmul := mul_le_mul_of_nonneg_left hN hδpos.le
  have h500 : δ * (500 / δ) = 500 := by field_simp
  have hmain : 500 + δ * (128 * q ^ 2 * (q - 1)) ≤ δ * N := by
    calc 500 + δ * (128 * q ^ 2 * (q - 1)) = δ * (500 / δ + 128 * q ^ 2 * (q - 1)) := by
          rw [mul_add, h500]
      _ ≤ δ * N := hmul
  have hnn : 0 ≤ δ * (128 * q ^ 2 * (q - 1)) := by positivity
  by_cases hsmall : q ≤ 300
  · linarith
  · replace hsmall := not_le.mp hsmall
    have hδ100 : 1 / 100 ≤ δ := by
      rw [hδ, div_le_div_iff₀ (by norm_num) hden]
      nlinarith
    have hpos : 0 ≤ 128 * q ^ 2 * (q - 1) := by positivity
    have h1 := mul_le_mul_of_nonneg_right hδ100 hpos
    have h2 : 4 * q / 3 + 10 ≤ 1 / 100 * (128 * q ^ 2 * (q - 1)) := by nlinarith
    linarith

/-- **Exponent budget**: `10 + q β ≤ δ N_*`. -/
theorem sc_delta_Nstar_budget {β : ℝ} (hβ : 1 < β) (hβ' : β < 4 / 3) :
    10 + q β * β ≤ delta β * (Nstar β : ℝ) := by
  have hq := Infra.Ingredients.one_lt_q hβ hβ'
  have hd := Infra.Ingredients.delta_pos hβ hβ'
  have hδ := Infra.Ingredients.delta_eq_q_fraction hβ hβ'
  have hN1 := Infra.Ingredients.Nstar_ge_defining_real hβ hβ'
  have hN2 := Infra.Ingredients.Nstar_ge_eight_add_mul hβ hβ'
  have hsq : 0 ≤ 1 / (delta β) ^ 2 := by positivity
  have hN : 500 / delta β + 128 * q β ^ 2 * (q β - 1) ≤ (Nstar β : ℝ) := by
    obtain ⟨h1, h2, h3⟩ := Infra.Ingredients.Nstar_corrections_nonneg hβ hβ'
    rw [Infra.Ingredients.Nstar_eq_ceil]
    refine le_trans ?_ (Nat.le_ceil _)
    have hdef : 0 ≤ 1 / (delta β) ^ 2 := hsq
    linarith
  have hcore := sc_budget_core hq hδ hN
  have hqb : q β * β ≤ 4 * q β / 3 := by
    have : 0 < q β := by linarith
    nlinarith
  linarith

end AVenhance.Infra.Section5.Contracts
end
