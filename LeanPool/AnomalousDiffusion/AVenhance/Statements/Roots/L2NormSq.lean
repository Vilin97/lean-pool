/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.TimeCube

/-! Statement file: `l2NormSq` (Roots).
This file contains exactly one declaration of the formalization's public statement surface. -/

@[expose] public section

open MeasureTheory Filter Topology Homogenization

namespace AVenhance

/-- `∫_{(0,1)²} f²`. -/
noncomputable def l2NormSq (f : Vec 2 → ℝ) : ℝ := ∫ x in unitCube, f x ^ 2

end AVenhance
