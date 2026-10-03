/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.L2NormSq

/-! Statement file: `gradNormSq` (Roots).
This file contains exactly one declaration of the formalization's public statement surface. -/

@[expose] public section

open MeasureTheory Filter Topology Homogenization

namespace AVenhance

/-- `∫_{(0,1)²} |Du|²` (Euclidean length of the gradient). -/
noncomputable def gradNormSq (Du : Vec 2 → Vec 2) : ℝ := ∫ x in unitCube, vecNormSq (Du x)

end AVenhance
