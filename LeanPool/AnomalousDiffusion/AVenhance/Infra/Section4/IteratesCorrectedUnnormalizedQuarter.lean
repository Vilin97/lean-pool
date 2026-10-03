/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesCorrectedQuarterBudget

/-! # Iterates Corrected Unnormalized Quarter

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
namespace AVenhance.Infra.Section4

/-- Corrected total induction budget in unnormalized form. Its material term
contains C/C0, and C0 is chosen large enough to absorb it. -/
theorem iterate_corrected_unnormalized_quarter_budget {C C₀ ρ F : ℝ} {i : ℕ}
    (hC : 0 ≤ C) (hC₀ : 1 ≤ C₀) (hρ : 0 < ρ) (hF : C₀ ≤ F)
    (hlarge : 32 * C ≤ C₀) (hsmall : C₀ * (ρ * F ^ 2) ≤ 1) (hi : 1 ≤ i) :
    (C / F ^ 2 + 2 * (C / F ^ 4)) * iterateAmplitude (C₀ * (ρ * F ^ 2)) i ^ 2 +
      2 * C * ρ * iterateAmplitude (C₀ * (ρ * F ^ 2)) (i - 1) *
        iterateAmplitude (C₀ * (ρ * F ^ 2)) i +
      (C / C₀ + 2 * C / C₀ ^ 2) * iterateAmplitude (C₀ * (ρ * F ^ 2)) i ^ 2 ≤
      iterateAmplitude (C₀ * (ρ * F ^ 2)) i ^ 2 / 4 := by
  have hp : 0 < C₀ := by linarith only [hC₀]
  have hFp : 0 < F := hp.trans_le hF
  have hAi := iterateAmplitude_pos (mul_pos hp (mul_pos hρ (sq_pos_of_pos hFp))) i
  have hc := mul_le_mul_of_nonneg_left
    (iterate_source_linear_ratio_le hp hρ hF hsmall hi) hC
  have hc' : C * (ρ * iterateAmplitude (C₀ * (ρ * F ^ 2)) (i - 1) /
      iterateAmplitude (C₀ * (ρ * F ^ 2)) i) ≤ C / C₀ ^ 3 := by
    simpa only [mul_one_div] using hc
  have hb := iterate_corrected_scalar_budget_quarter hC hC₀ hF hlarge hc'
    (le_refl (C / C₀ + 2 * C / C₀ ^ 2))
  have hm := mul_le_mul_of_nonneg_right hb
    (sq_nonneg (iterateAmplitude (C₀ * (ρ * F ^ 2)) i))
  generalize iterateAmplitude (C₀ * (ρ * F ^ 2)) i = A at hAi hm ⊢
  generalize iterateAmplitude (C₀ * (ρ * F ^ 2)) (i - 1) = Ap at hm ⊢
  convert hm using 1
  · field_simp
  · ring

end AVenhance.Infra.Section4
