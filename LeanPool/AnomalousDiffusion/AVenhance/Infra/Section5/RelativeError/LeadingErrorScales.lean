/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Ingredients.Q
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Ingredients.Delta
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Ingredients.Gamma

/-! # Exponent lemmas for the leading-error estimate (`e.leadingord`)

Abstract-real arithmetic on the exponents `q`, `γ`, `δ`: the exponent of the
`χTilde · ∇G` term dominates `2δ`, so `ε_m / ε_{m-1}^{1+γ/2} ≤ K ε_{m-1}^{2δ}` follows
from monotonicity of `ε ↦ ε^s` on `(0, 1]`.
-/

@[expose] public section

namespace AVenhance.Infra.Section5.RelativeError

open AVenhance

/-- For `1 < β < 4/3` we have `q > 1`. -/
theorem one_lt_q_of_lt_four_thirds {β : ℝ} (hβ : 1 < β) (hβ' : β < 4 / 3) : 1 < q β := by
  have h : 1 < (2 - β) / (2 * (β - 1)) := by
    rw [lt_div_iff₀ (by linarith)]
    linarith
  unfold q
  linarith

/-- Exponent of the `χTilde · ∇G` term dominates `2δ`: `ε_m/ε_{m-1}^{1+γ/2} ≤ K ε_{m-1}^{2δ}`
holds at the level of exponents, `2 δ ≤ q - 1 - γ/2`. -/
theorem corrector_second_term_exponent {β : ℝ} (hβ : 1 < β) (hβ' : β < 4 / 3) :
    2 * delta β ≤ q β - 1 - gamma β / 2 := by
  have hq := one_lt_q_of_lt_four_thirds hβ hβ'
  have hβ0 : 0 < β := by linarith
  have hq1 : 0 < q β + 1 := by linarith
  have hdiff : q β - 1 - gamma β / 2 - 2 * delta β =
      (q β - 1) * (1 / 2 + β * (2 * q β - 1) / (4 * (q β + 1))) := by
    unfold gamma delta
    have h2 : 2 * q β + 2 ≠ 0 := by linarith
    have h3 : q β + 1 ≠ 0 := hq1.ne'
    field_simp
    ring
  have hpos : 0 ≤ (q β - 1) * (1 / 2 + β * (2 * q β - 1) / (4 * (q β + 1))) := by
    have h1 : 0 ≤ q β - 1 := by linarith
    have h2 : 0 ≤ β * (2 * q β - 1) / (4 * (q β + 1)) := by
      apply div_nonneg
      · exact mul_nonneg hβ0.le (by linarith)
      · linarith
    exact mul_nonneg h1 (by linarith)
  linarith

end AVenhance.Infra.Section5.RelativeError
