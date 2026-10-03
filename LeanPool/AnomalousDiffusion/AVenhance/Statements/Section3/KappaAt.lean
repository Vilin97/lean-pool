/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.KhomScalar

/-! Statement file: `kappaAt` (Section3).
This file contains exactly one declaration of the formalization's public statement surface. -/

@[expose] public section

open MeasureTheory Homogenization

noncomputable section

namespace AVenhance
namespace Ingredients
variable {β : ℝ} (I : Ingredients β)

/-- `e.kappa.sequence` (label 3533). `kappaAt I κ m d` is `κ_m` for the chain topped at
`M = m + d` (so `κ_M = κ`, `κ_{m-1} = KBar_m^{κ_m}`): `κ_m = kappaAt I κ m (M - m)`, `m ≤ M`. -/
def kappaAt (κ : ℝ) : ℕ → ℕ → ℝ
  | _, 0 => κ
  | m, d + 1 => I.KhomScalar (kappaAt κ (m + 1) d) (m + 1)

end Ingredients
end AVenhance
