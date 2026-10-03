/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.TimeAvgMat

/-! Statement file: `gradMatrix` (Section3).
This file contains exactly one declaration of the formalization's public statement surface. -/

@[expose] public section

open MeasureTheory Homogenization

noncomputable section

namespace AVenhance

/-- `∇Χ` for `Χ = (χ_{e₁}, χ_{e₂})` (`e.gradcorrmatrix`, label 2819): the entry `(i, j)` is
`∂_{x_i} χ_{e_j}`. -/
def gradMatrix (Χ : Vec 2 → Vec 2) (x : Vec 2) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun i j => spaceGrad (fun y => Χ y j) x i

end AVenhance
