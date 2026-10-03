/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.ChiMK

/-! Statement file: `chiM` (Section3).
This file contains exactly one declaration of the formalization's public statement surface. -/

@[expose] public section

open MeasureTheory Homogenization

noncomputable section

namespace AVenhance
namespace Ingredients
variable {β : ℝ} (I : Ingredients β)

/-- `Χ^κ_m := ∑_{k ∈ ℤ} ξ_{m,k} Χ^κ_{m,k}`, `e.Chim` (label 2909). -/
def chiM (κ : ℝ) (m : ℕ) (t : ℝ) (x : Vec 2) : Vec 2 :=
  ∑' k : ℤ, I.xiMK m k t • I.chiMK κ m k t x

end Ingredients
end AVenhance
