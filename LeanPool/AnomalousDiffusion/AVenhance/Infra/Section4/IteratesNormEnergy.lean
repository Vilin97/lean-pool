/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesTime

/-! Conversion of actual quadratic energies to the norm used in l.V.
The differentiated PDE energy inequality must still be derived separately. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4
open AVenhance

/-- The sum of the two nonnegative norm components costs at most twice
its quadratic energy. This isolates square roots from energy bookkeeping. -/
theorem iterate_norm_sum_sq_le_energy {e g κ : ℝ}
    (he : 0 ≤ e) (hg : 0 ≤ g) (hκ : 0 ≤ κ) :
    (Real.sqrt e + Real.sqrt κ * Real.sqrt g) ^ 2 ≤ 2 * (e + κ * g) := by
  have hs₁ := Real.sq_sqrt he
  have hs₂ := Real.sq_sqrt hg
  have hs₃ := Real.sq_sqrt hκ
  have hprod : (Real.sqrt κ * Real.sqrt g) ^ 2 = κ * g := by
    rw [mul_pow, hs₃, hs₂]
  nlinarith only [sq_nonneg (Real.sqrt e - Real.sqrt κ * Real.sqrt g), hs₁, hprod]

end AVenhance.Infra.Section4
