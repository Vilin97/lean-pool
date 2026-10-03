/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.FlowSpatialPeriodicity

/-! Spatial differentiation of the actual divergence forcing. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4

theorem amnrSpaceWord_coordinate_derivative {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (w : List (Fin 2)) (q : Fin 2) :
    amnrSpaceWord w (fun x => AVenhance.spaceGrad f x q) =
      fun x => AVenhance.spaceGrad (amnrSpaceWord w f) x q := by
  induction w with
  | nil => rfl
  | cons p w ih =>
    rw [amnrSpaceWord, ih]
    funext x
    exact amnr_energy_coordinate_derivatives_commute (amnrSpaceWord_smooth hf w) q p x

end AVenhance.Infra.Section4
