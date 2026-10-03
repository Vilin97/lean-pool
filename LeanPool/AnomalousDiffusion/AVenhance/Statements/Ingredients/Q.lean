/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import Mathlib.Basic.Real.Basic
public import LeanPool.AnomalousDiffusion.Homogenization.Ambient.Basic

/-! Statement file: `q` (Ingredients).
This file contains exactly one declaration of the formalization's public statement surface. -/

@[expose] public section

noncomputable section

namespace AVenhance

/-- `e.q.def.0` (986-989): `q := (1/2) (1 + (2-β)/(2(β-1)))`. -/
def q (β : ℝ) : ℝ := (1 / 2) * (1 + (2 - β) / (2 * (β - 1)))

end AVenhance
