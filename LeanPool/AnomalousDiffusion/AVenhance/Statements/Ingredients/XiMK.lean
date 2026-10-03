/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Ingredients.ZetaMK

/-! Statement file: `xiMK` (Ingredients).
This file contains exactly one declaration of the formalization's public statement surface. -/

@[expose] public section

noncomputable section

namespace AVenhance

open Homogenization
namespace Ingredients
variable {β : ℝ} (I : Ingredients β)

/-- `ξ_{m,k}`, `e.xi.mk.def` (1283), defined here for all `k ∈ ℤ`. -/
def xiMK (m : ℕ) (k : ℤ) : ℝ → ℝ := scaledCutoff I.xi (tau β I.Λ m) k

end Ingredients
end AVenhance
