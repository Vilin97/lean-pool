/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Ingredients.XiMK

/-! Statement file: `hatZetaML` (Ingredients).
This file contains exactly one declaration of the formalization's public statement surface. -/

@[expose] public section

noncomputable section

namespace AVenhance

open Homogenization
namespace Ingredients
variable {β : ℝ} (I : Ingredients β)

/-- `ζ̂_{m,l} = ζ̂_{m,0}(· - l τ''_m)` (1319). -/
def hatZetaML (m : ℕ) (l : ℤ) : ℝ → ℝ := shiftCutoff (I.hatZeta m) (l * tauPP β I.Λ m)

end Ingredients
end AVenhance
