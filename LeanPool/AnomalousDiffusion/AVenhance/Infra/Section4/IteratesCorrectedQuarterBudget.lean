/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesCorrectedRecursion

/-! # Iterates Corrected Quarter Budget

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
namespace AVenhance.Infra.Section4

/-- Additional constant room controls independently maximized scalar and
coordinate-gradient norms while retaining the C/C0 contribution. -/
theorem iterate_corrected_scalar_budget_quarter {C C₀ F c d : ℝ}
    (hC : 0 ≤ C) (hC₀ : 1 ≤ C₀) (hF : C₀ ≤ F)
    (hlarge : 32 * C ≤ C₀) (hc : c ≤ C / C₀ ^ 3)
    (hd : d ≤ C / C₀ + 2 * C / C₀ ^ 2) :
    C / F ^ 2 + 2 * (C / F ^ 4) + 2 * c + d ≤ 1 / 4 := by
  have hp : 0 < C₀ := by linarith only [hC₀]
  have hpow₀ (n : ℕ) (hn : 1 ≤ n) : C₀ ≤ C₀ ^ n := by
    simpa only [pow_one] using pow_le_pow_right₀ hC₀ hn
  have hpowF (n : ℕ) (hn : 1 ≤ n) : C₀ ≤ F ^ n :=
    hF.trans (by simpa only [pow_one] using pow_le_pow_right₀ (hC₀.trans hF) hn)
  have h₂ : C / F ^ 2 ≤ C / C₀ := div_le_div_of_nonneg_left hC hp (hpowF 2 (by omega))
  have h₄ : C / F ^ 4 ≤ C / C₀ := div_le_div_of_nonneg_left hC hp (hpowF 4 (by omega))
  have h₃ : C / C₀ ^ 3 ≤ C / C₀ := div_le_div_of_nonneg_left hC hp (hpow₀ 3 (by omega))
  have hsq : C / C₀ ^ 2 ≤ C / C₀ := div_le_div_of_nonneg_left hC hp (hpow₀ 2 (by omega))
  have hsmall : C / C₀ ≤ 1 / 32 := (div_le_iff₀ hp).mpr (by linarith only [hlarge])
  have hd' : d ≤ C / C₀ + 2 * (C / C₀ ^ 2) := by
    simpa only [mul_div_assoc] using hd
  linarith only [h₂, h₄, hc, hd', h₃, hsq, hsmall]

end AVenhance.Infra.Section4
