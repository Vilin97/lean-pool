/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Ingredients.Q

/-! Statement file: `delta` (Ingredients).
This file contains exactly one declaration of the formalization's public statement surface. -/

@[expose] public section

noncomputable section

namespace AVenhance

open Homogenization

/-- `e.delta` (1008): `δ := (1/4)(q-1)(1 - ((2q+1)/(2q+2)) β)`. -/
def delta (β : ℝ) : ℝ :=
  (1 / 4) * (q β - 1) * (1 - ((2 * q β + 1) / (2 * q β + 2)) * β)

end AVenhance
