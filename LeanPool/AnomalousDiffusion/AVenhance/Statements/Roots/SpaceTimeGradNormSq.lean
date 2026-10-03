/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.GradNormSq

/-! Statement file: `spaceTimeGradNormSq` (Roots).
This file contains exactly one declaration of the formalization's public statement surface. -/

@[expose] public section

open MeasureTheory Filter Topology Homogenization

namespace AVenhance

/-- The squared space-time norm `‖∇θ‖²_{L²((0,1)×𝕋²)}` of a weak gradient `Dθ`. -/
noncomputable def spaceTimeGradNormSq (Dθ : ℝ → Vec 2 → Vec 2) : ℝ :=
  ∫ p in timeCube, vecNormSq (Dθ p.1 p.2)

end AVenhance
