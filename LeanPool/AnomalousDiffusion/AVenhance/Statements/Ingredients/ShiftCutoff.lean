/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Ingredients.ScaledCutoff

/-! Statement file: `shiftCutoff` (Ingredients).
This file contains exactly one declaration of the formalization's public statement surface. -/

@[expose] public section

noncomputable section

namespace AVenhance

open Homogenization

/-- Translation `f_{m,l} = f_{m,0}(· - l τ''_m)` (1319-1322). -/
def shiftCutoff (f : ℝ → ℝ) (c : ℝ) : ℝ → ℝ := fun t => f (t - c)

end AVenhance
