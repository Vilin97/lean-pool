/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Ingredients.Epsilon

/-! Statement file: `a` (Ingredients).
This file contains exactly one declaration of the formalization's public statement surface. -/

@[expose] public section

noncomputable section

namespace AVenhance

open Homogenization

/-- `e.am.def` (1094): `a_m := ε_m^{β-2}`. -/
def a (β : ℝ) (Λ : ℕ) (m : ℕ) : ℝ := epsilon β Λ m ^ (β - 2)

end AVenhance
