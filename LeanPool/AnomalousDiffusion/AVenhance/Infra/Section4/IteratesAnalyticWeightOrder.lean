/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesHigherEnergyBudget

/-! # Iterates Analytic Weight Order

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
namespace AVenhance.Infra.Section4

/-- Increasing the increment index increases its factorial weight. -/
theorem iterateAnalyticWeight_mono {n i j : ℕ} {L : ℝ}
    (hL : 0 ≤ L) (hij : i ≤ j) :
    iterateAnalyticWeight n i L ≤ iterateAnalyticWeight n j L := by
  unfold iterateAnalyticWeight
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg hL _)
  exact_mod_cast Nat.factorial_le (by omega : n + 2 * i ≤ n + 2 * j)

theorem iterateAnalyticWeight_nonneg (n i : ℕ) {L : ℝ} (hL : 0 ≤ L) :
    0 ≤ iterateAnalyticWeight n i L := by
  unfold iterateAnalyticWeight
  positivity

end AVenhance.Infra.Section4
