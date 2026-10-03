/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesPhysicalBudgetScales

/-! # Iterates Source Radius

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
namespace AVenhance.Infra.Section4

/-- The square of the source maximum retains its exact two regimes. -/
theorem iterate_source_max_square {x : ℝ} (hx : 0 ≤ x) :
    (max 1 x) ^ 2 = max 1 (x ^ 2) := by
  by_cases h : x ≤ 1
  · rw [max_eq_left h, max_eq_left]
    · norm_num
    · nlinarith only [hx, h]
  · have h1 : 1 ≤ x := le_of_not_ge h
    rw [max_eq_right h1, max_eq_right]
    nlinarith only [h1]

/-- The printed source radius and F are exactly reciprocal diffusive scales. -/
theorem iterate_source_radius_identity {e γ R C₀ : ℝ}
    (he : 0 < e) (_hR : 0 < R) (hC₀ : 0 ≤ C₀) :
    C₀ * max 1 (e ^ (1 + γ / 2) / R) =
      e ^ (1 + γ / 2) * max (C₀ * e ^ (-1 - γ / 2)) (C₀ / R) := by
  have hp : 0 < e ^ (1 + γ / 2) := Real.rpow_pos_of_pos he _
  have heq : e ^ (1 + γ / 2) * e ^ (-1 - γ / 2) = 1 := by
    rw [← Real.rpow_add he]
    rw [show (1 + γ / 2) + (-1 - γ / 2) = (0 : ℝ) by ring, Real.rpow_zero]
  rw [mul_max_of_nonneg _ _ hC₀, mul_max_of_nonneg _ _ hp.le]
  congr 1
  · calc
      _ = C₀ := by ring
      _ = C₀ * (e ^ (1 + γ / 2) * e ^ (-1 - γ / 2)) := by rw [heq, mul_one]
      _ = _ := by ring
  · ring

/-- The induction parameter is the printed C0-cubed smallness parameter. -/
theorem iterate_source_amplitude_parameter {e γ R C₀ ρ : ℝ}
    (he : 0 < e) (hR : 0 < R) :
    C₀ * (ρ * (C₀ * max 1 (e ^ (1 + γ / 2) / R)) ^ 2) =
      C₀ ^ 3 * ρ * max 1 (e ^ (2 + γ) * R ^ (-2 : ℤ)) := by
  have hp : 0 ≤ e ^ (1 + γ / 2) / R := by positivity
  have heq : (e ^ (1 + γ / 2)) ^ 2 = e ^ (2 + γ) := by
    rw [← Real.rpow_mul_natCast he.le]
    congr 1
    push_cast
    ring
  rw [mul_pow, iterate_source_max_square hp, div_pow, heq]
  rw [zpow_neg, zpow_ofNat]
  simp only [div_eq_mul_inv]
  ring

end AVenhance.Infra.Section4
