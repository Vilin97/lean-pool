/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.Khom

/-! Statement file: `KhomScalar` (Section3).
This file contains exactly one declaration of the formalization's public statement surface. -/

@[expose] public section

open MeasureTheory Homogenization

noncomputable section

namespace AVenhance
namespace Ingredients
variable {β : ℝ} (I : Ingredients β)

/-- The scalar `a` with `KBar^κ_m = a I` (line 2994): the `(1,1)` entry. That `KBar` is scalar and
`a > 0` is the theorem `Khom_eq_scalar`; the abuse of notation of the source is `KhomScalar`. -/
def KhomScalar (κ : ℝ) (m : ℕ) : ℝ := I.Khom κ m 0 0

end Ingredients
end AVenhance
