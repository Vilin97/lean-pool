/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesTerminalCoercivity

/-! # Iterates Terminal Boundary Coercivity

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
namespace AVenhance.Infra.Section4

/-- The terminal primitive may consume half the current scalar energy.
Full dissipation is still controlled at time one before treating partial time. -/
theorem iterate_terminal_boundary_norm_sq_bound {e₁ e g gpart κ a R : ℝ}
    (he₁ : 0 ≤ e₁) (he : 0 ≤ e) (hg : 0 ≤ g) (hgp : 0 ≤ gpart) (hκ : 0 ≤ κ)
    (ha : a ≤ 1 / 2)
    (hfull : e₁ / 4 + κ * g ≤ a * κ * g + R)
    (hpartial : e / 4 + κ * gpart ≤ a * κ * g + R) :
    (Real.sqrt e + Real.sqrt κ * Real.sqrt g) ^ 2 ≤ 24 * R := by
  have hf : (e₁ / 2) / 2 + κ * g ≤ a * κ * g + R := by linarith only [hfull]
  have hp : (e / 2) / 2 + κ * gpart ≤ a * κ * g + R := by linarith only [hpartial]
  have hb := iterate_terminal_full_energy_bound (by positivity : 0 ≤ e₁ / 2)
    hg hgp hκ ha hf hp
  have hkg : 0 ≤ κ * g := mul_nonneg hκ hg
  have hs := iterate_norm_sum_sq_le_energy he hg hκ
  nlinarith only [hb, hkg, hs]

end AVenhance.Infra.Section4
