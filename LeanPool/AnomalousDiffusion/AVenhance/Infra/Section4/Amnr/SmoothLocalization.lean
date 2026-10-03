/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.TemperatureTimeEnergy
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-! Smooth localization on the actual positive-time domain. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory Set Filter
open scoped Topology
namespace AVenhance.Infra.Section4

/-- Ordered derivatives depend only on the local germ of their scalar field. -/
theorem amnrWord_eventuallyEq {f g : AmnrSpace → ℝ} {z : AmnrSpace}
    (hfg : f =ᶠ[nhds z] g) (b : AmnrSpace → Vec 2) (w : List (Option (Fin 2))) :
    amnrWord b w f =ᶠ[nhds z] amnrWord b w g := by
  induction w with
  | nil => exact hfg
  | cons d w ih =>
    have hh := ih.fderiv (𝕜 := ℝ)
    filter_upwards [hh] with y hy
    exact congrArg (fun L : AmnrSpace →L[ℝ] ℝ => L (amnrDirection b d y)) hy

end AVenhance.Infra.Section4
