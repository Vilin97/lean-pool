/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesNormEnergy

/-! # Iterates Terminal Coercivity

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
namespace AVenhance.Infra.Section4

/-- Full dissipation is first controlled at terminal time one, then used
in each partial-time inequality. No partial dissipation is replaced by full
 dissipation on the left-hand side. -/
theorem iterate_terminal_full_energy_bound {e₁ e g gpart κ a R : ℝ}
    (he₁ : 0 ≤ e₁) (hg : 0 ≤ g) (hgp : 0 ≤ gpart) (hκ : 0 ≤ κ)
    (ha : a ≤ 1 / 2)
    (hfull : e₁ / 2 + κ * g ≤ a * κ * g + R)
    (hpartial : e / 2 + κ * gpart ≤ a * κ * g + R) :
    e + κ * g ≤ 6 * R := by
  have hk : 0 ≤ κ * g := mul_nonneg hκ hg
  have hkp : 0 ≤ κ * gpart := mul_nonneg hκ hgp
  have ham := mul_le_mul_of_nonneg_right ha hk
  have hG : κ * g ≤ 2 * R := by nlinarith only [hfull, he₁, ham]
  nlinarith only [hpartial, hkp, ham, hG]

end AVenhance.Infra.Section4
