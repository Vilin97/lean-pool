/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Ingredients.IndIcc

/-! Statement file: `scaledCutoff` (Ingredients).
This file contains exactly one declaration of the formalization's public statement surface. -/

@[expose] public section

noncomputable section

namespace AVenhance

open Homogenization

/-- `e.zeta.mk.def` (1246), `e.xi.mk.def` (1283): `f_{m,k}(t) = f((t - kτ)/τ)`. -/
def scaledCutoff (f : ℝ → ℝ) (τ : ℝ) (k : ℤ) : ℝ → ℝ := fun t => f ((t - k * τ) / τ)

end AVenhance
