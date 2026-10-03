/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.ZetaProd

/-! Statement file: `corrTime` (Section3).
This file contains exactly one declaration of the formalization's public statement surface. -/

@[expose] public section

open MeasureTheory Homogenization

noncomputable section

namespace AVenhance
namespace Ingredients
variable {β : ℝ} (I : Ingredients β)

/-- The time integral in `e.Chimk.formula` (label 2831):
`∫_{-∞}^t ζ̂_{m,l_k}(s) ζ_{m,k}(s) exp(4π²κ/ε_m² (s-t)) ds`. -/
def corrTime (κ : ℝ) (m : ℕ) (k : ℤ) (t : ℝ) : ℝ :=
  ∫ s in Set.Iic t, I.zetaProd m k s *
    Real.exp (4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2 * (s - t))

end Ingredients
end AVenhance
