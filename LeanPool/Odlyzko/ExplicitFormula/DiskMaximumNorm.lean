/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.Analysis.Complex.AbsMax

/-!
# Disk Maximum Norm

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/

@[expose] public section

noncomputable section

open Complex Metric Set

namespace NumberField.Odlyzko

theorem norm_le_on_closedBall_of_norm_le_on_sphere
    {f : ℂ → ℂ} {c : ℂ} {R M : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hbound : ∀ z ∈ sphere c R, ‖f z‖ ≤ M)
    {z : ℂ} (hz : z ∈ closedBall c R) :
    ‖f z‖ ≤ M := by
  apply norm_le_of_forall_mem_frontier_norm_le
    (U := ball c R) isBounded_ball
    (DifferentiableOn.diffContOnCl fun w hw ↦
      (hf w (closure_ball_subset_closedBall hw))
        |>.differentiableAt.differentiableWithinAt)
  · intro w hw
    exact hbound w (frontier_ball_subset_sphere hw)
  · rwa [closure_ball c hR.ne']

end NumberField.Odlyzko
