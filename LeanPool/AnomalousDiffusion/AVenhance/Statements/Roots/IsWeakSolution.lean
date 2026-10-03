/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.IsWeakSolutionGrad

/-! Statement file: `IsWeakSolution` (Roots).
This file contains exactly one declaration of the formalization's public statement surface. -/

@[expose] public section

open MeasureTheory Filter Topology Homogenization

namespace AVenhance

/-- `θ` is a weak solution of the advection–diffusion equation with drift `b`, diffusivity `κ` and
initial datum `θ₀`, for some spatial weak gradient `Dθ`. -/
def IsWeakSolution (b : ℝ → Vec 2 → Vec 2) (κ : ℝ) (θ₀ : Vec 2 → ℝ)
    (θ : ℝ → Vec 2 → ℝ) : Prop :=
  ∃ Dθ : ℝ → Vec 2 → Vec 2, IsWeakSolutionGrad b κ θ₀ θ Dθ

end AVenhance
