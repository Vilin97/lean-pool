/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.RelativeAnalytic
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.OpenInputs

/-! # Monotonicity of the jet inputs and real-variable scale facts -/

@[expose] public section

open Homogenization

noncomputable section

namespace AVenhance.Infra.Section5.Contracts

open AVenhance AVenhance.Infra.Section5 AVenhance.Infra.Section5.RelativeError

/-- The positive-jet hypothesis is monotone in the constant. -/
theorem sd_jets_mono {A A' ρ S : ℝ} {T : ℝ → Vec 2 → ℝ} (hA : 0 ≤ A) (hAA : A ≤ A')
    (hρ : 0 < ρ) (hS : 0 ≤ S) (h : PositiveTemperatureJets A ρ S T) :
    PositiveTemperatureJets A' ρ S T := by
  intro n i hn t ht
  refine (h n i hn t ht).trans ?_
  have hn0 : (0 : ℝ) ≤ n.factorial := by positivity
  have h1 : (A / ρ) ^ n ≤ (A' / ρ) ^ n :=
    pow_le_pow_left₀ (div_nonneg hA hρ.le) (div_le_div_of_nonneg_right hAA hρ.le) n
  have h2 : 0 ≤ A * S * n.factorial := by positivity
  calc A * S * n.factorial * (A / ρ) ^ n ≤ A * S * n.factorial * (A' / ρ) ^ n :=
        mul_le_mul_of_nonneg_left h1 h2
    _ ≤ A' * S * n.factorial * (A' / ρ) ^ n := by
        have : 0 ≤ (A' / ρ) ^ n := pow_nonneg (div_nonneg (hA.trans hAA) hρ.le) n
        have : A * S * n.factorial ≤ A' * S * n.factorial := by
          have := mul_le_mul_of_nonneg_right hAA hS
          exact mul_le_mul_of_nonneg_right this hn0
        exact mul_le_mul_of_nonneg_right this (by positivity)

/-- Real-variable lower bound of the exponential argument `r N / 4096`, with `r = x^{1+g/2}/c₂`,
`N = y⁻¹`, `y ≤ K x^q`, `2δ ≤ q - 1 - g/2`. -/
theorem sd_rN_facts {x y K c₂ q g δ : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) (hy : 0 < y)
    (hyK : y ≤ K * x ^ q) (hK : 1 ≤ K) (hc₂ : 0 < c₂) (hexp : 2 * δ ≤ q - 1 - g / 2)
    (hsmall : x ^ (2 * δ) ≤ 1 / (2 * c₂ * K)) :
    (1 / (4096 * c₂ * K)) * x ^ (-(2 * δ)) ≤ (x ^ (1 + g / 2) / c₂ * y⁻¹) / 4096 ∧
      2 ≤ x ^ (1 + g / 2) / c₂ * y⁻¹ := by
  have hK0 : 0 < K := by linarith
  have hxq : 0 < x ^ q := Real.rpow_pos_of_pos hx _
  have hxg : 0 < x ^ (1 + g / 2) := Real.rpow_pos_of_pos hx _
  have hyinv : (K * x ^ q)⁻¹ ≤ y⁻¹ := inv_anti₀ hy hyK
  have hpow : x ^ (-(2 * δ)) ≤ x ^ (-(q - 1 - g / 2)) :=
    Real.rpow_le_rpow_of_exponent_ge hx hx1 (by linarith)
  have heq : x ^ (1 + g / 2) * (x ^ q)⁻¹ = x ^ (-(q - 1 - g / 2)) := by
    rw [← Real.rpow_neg hx.le, ← Real.rpow_add hx]
    congr 1
    ring
  have hmain : x ^ (-(2 * δ)) / (c₂ * K) ≤ x ^ (1 + g / 2) / c₂ * y⁻¹ := by
    calc x ^ (-(2 * δ)) / (c₂ * K) ≤ x ^ (-(q - 1 - g / 2)) / (c₂ * K) :=
          div_le_div_of_nonneg_right hpow (by positivity)
      _ = x ^ (1 + g / 2) / c₂ * (K * x ^ q)⁻¹ := by
          rw [← heq]
          field_simp
      _ ≤ x ^ (1 + g / 2) / c₂ * y⁻¹ :=
          mul_le_mul_of_nonneg_left hyinv (by positivity)
  constructor
  · calc (1 / (4096 * c₂ * K)) * x ^ (-(2 * δ)) = (x ^ (-(2 * δ)) / (c₂ * K)) / 4096 := by
          field_simp
      _ ≤ _ := div_le_div_of_nonneg_right hmain (by norm_num)
  · refine le_trans ?_ hmain
    have hx2 : 0 < x ^ (2 * δ) := Real.rpow_pos_of_pos hx _
    have : x ^ (-(2 * δ)) = (x ^ (2 * δ))⁻¹ := Real.rpow_neg hx.le _
    rw [this, le_div_iff₀ (by positivity)]
    have h2 : 2 * (c₂ * K) ≤ (x ^ (2 * δ))⁻¹ := by
      rw [le_inv_comm₀ (by positivity) hx2]
      calc x ^ (2 * δ) ≤ 1 / (2 * c₂ * K) := hsmall
        _ = (2 * (c₂ * K))⁻¹ := by field_simp
    linarith

end AVenhance.Infra.Section5.Contracts
end
