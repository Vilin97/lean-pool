/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.SpaceGrad

/-! Statement file: `timeCube` (Roots).
This file contains exactly one declaration of the formalization's public statement surface. -/

@[expose] public section

open MeasureTheory Filter Topology Homogenization

namespace AVenhance

/-- Space-time cell `(0,1) × (0,1)²`. -/
def timeCube : Set (ℝ × Vec 2) := Set.Ioo (0 : ℝ) 1 ×ˢ unitCube

end AVenhance
