/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.StreamMixedSum

/-! Exact noncommuting material-power differences for the velocity induction. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory Set
namespace AVenhance.Infra.Section4

/-- The change of material operator is the actual fast advection, even for
Lean's total Fréchet derivative. -/
theorem amnr_material_operator_change (b c : AmnrSpace → Vec 2)
    (f : AmnrSpace → ℝ) (z : AmnrSpace) :
    amnrOp b none f z - amnrOp c none f z =
      ∑ p : Fin 2, (b z p - c z p) * amnrOp c (some p) f z := by
  have hdir : amnrDirection b none z = amnrDirection c none z + (0, b z - c z) := by
    ext p <;> simp [amnrDirection]
  unfold amnrOp
  rw [hdir, map_add, add_sub_cancel_left, amnrFDeriv_vertical]
  rfl

end AVenhance.Infra.Section4
