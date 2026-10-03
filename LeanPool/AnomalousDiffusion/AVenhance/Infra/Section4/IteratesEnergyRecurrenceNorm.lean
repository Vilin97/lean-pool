/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesTerminalBoundaryCoercivity

/-! # Iterates Energy Recurrence Norm

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
namespace AVenhance.Infra.Section4

/-- A uniform differentiated energy remainder controls each terminal norm.
The partial dissipation remains on its original interval. -/
theorem iterate_energy_recurrence_norm_sq {e : ℝ → ℝ} {gpart : ℝ → ℝ}
    {g κ R : ℝ} (he : ∀ t, 0 ≤ e t) (hg : 0 ≤ g)
    (hgp : ∀ t, 0 ≤ gpart t) (hκ : 0 ≤ κ) (hg1 : gpart 1 = g)
    (henergy : ∀ t, 0 ≤ t → t ≤ 1 →
      e t / 2 + κ * gpart t ≤ e t / 4 + 3 * κ / 8 * g + R)
    {s : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    (Real.sqrt (e s) + Real.sqrt κ * Real.sqrt g) ^ 2 ≤ 24 * R := by
  have hfull := henergy 1 (by norm_num) (by norm_num)
  rw [hg1] at hfull
  have hpartial := henergy s hs hs1
  apply iterate_terminal_boundary_norm_sq_bound (he 1) (he s) hg (hgp s) hκ
    (a := 3 / 8) (by norm_num)
  · nlinarith only [hfull]
  · nlinarith only [hpartial]

end AVenhance.Infra.Section4
