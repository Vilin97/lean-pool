/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesAnalyticWeightOrder

/-! # Iterates Analytic Radius Doubling

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
namespace AVenhance.Infra.Section4

/-- Enlarging the norm frequency by two absorbs a fixed loss at every
positive derivative order. -/
theorem iterate_positive_order_radius_double {l L : ℝ} {n : ℕ}
    (hl : 0 ≤ l) (hL : 2 * l ≤ L) (hn : 1 ≤ n) :
    2 * l ^ n ≤ L ^ n := by
  have h2 : (2 : ℝ) ≤ 2 ^ n := by
    simpa only [pow_one] using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hn
  calc
    _ ≤ (2 : ℝ) ^ n * l ^ n := mul_le_mul_of_nonneg_right h2 (pow_nonneg hl n)
    _ = (2 * l) ^ n := (mul_pow _ _ _).symm
    _ ≤ _ := pow_le_pow_left₀ (by positivity) hL n

/-- A larger fixed loss is absorbed in the radius at positive orders. -/
theorem iterate_positive_order_radius_four {l L : ℝ} {n : ℕ}
    (hl : 0 ≤ l) (hL : 4 * l ≤ L) (hn : 1 ≤ n) :
    4 * l ^ n ≤ L ^ n := by
  have h4 : (4 : ℝ) ≤ 4 ^ n := by
    simpa only [pow_one] using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) hn
  calc
    _ ≤ (4 : ℝ) ^ n * l ^ n := mul_le_mul_of_nonneg_right h4 (pow_nonneg hl n)
    _ = (4 * l) ^ n := (mul_pow _ _ _).symm
    _ ≤ _ := pow_le_pow_left₀ (by positivity) hL n

end AVenhance.Infra.Section4
