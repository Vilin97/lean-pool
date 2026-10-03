/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.GradMatrix

/-! Statement file: `spaceLap` (Section3).
This file contains exactly one declaration of the formalization's public statement surface. -/

@[expose] public section

open MeasureTheory Homogenization

noncomputable section

namespace AVenhance

/-- Laplacian `Δf = ∑_i ∂_i ∂_i f`. -/
def spaceLap (f : Vec 2 → ℝ) (x : Vec 2) : ℝ :=
  ∑ i : Fin 2, spaceGrad (fun y => spaceGrad f y i) x i

end AVenhance
