/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesRadiusInflation

/-! # Iterates Velocity Radius Extension

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
namespace AVenhance.Infra.Section4

/-- A positive-order analytic profile can use any larger frequency radius
while preserving the product of its prefactor and radius. -/
theorem iterate_positive_profile_radius_extension {B r₀ r f : ℝ} {n : ℕ}
    (hB : 0 ≤ B) (hr₀ : 0 < r₀) (hr : 0 < r) (hle : r₀ ≤ r) (hn : 1 ≤ n)
    (hf : |f| ≤ B * (n.factorial : ℝ) * r₀ ^ n) :
    |f| ≤ (B * r₀ / r) * (n.factorial : ℝ) * r ^ n := by
  have hratio : r₀ / r ≤ 1 := (div_le_one hr).mpr hle
  have hb := iterate_positive_profile_radius_inflation n hn hB hr₀.le
    (div_pos hr₀ hr) hratio hf
  have heq : r₀ / (r₀ / r) = r := by field_simp
  rw [heq] at hb
  simpa only [mul_div_assoc] using hb

end AVenhance.Infra.Section4
