/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Ingredients.Psi

/-! Statement file: `indIcc` (Ingredients).
This file contains exactly one declaration of the formalization's public statement surface. -/

@[expose] public section

noncomputable section

namespace AVenhance

open Homogenization

/-- Indicator (as a real function) of the closed interval `[u, v]`. -/
def indIcc (u v : ℝ) (t : ℝ) : ℝ := Set.indicator (Set.Icc u v) (fun _ => (1 : ℝ)) t

end AVenhance
