/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Construction.StreamVel

/-! Spatially constant stream functions induce zero velocity. -/

@[expose] public section

open Homogenization

namespace AVenhance

/-- Spatial constancy makes the perpendicular gradient vanish, even when the stream
function varies in time. -/
theorem streamVel_spatialConstant (c : ℝ → ℝ) : streamVel (fun t _ => c t) = 0 := by
  funext t x i
  unfold streamVel spaceGrad
  simp only [fderiv_const_apply, zero_apply]
  change sigmaMat.mulVec (0 : Vec 2) i = 0
  rw [Matrix.mulVec_zero]
  rfl

end AVenhance
