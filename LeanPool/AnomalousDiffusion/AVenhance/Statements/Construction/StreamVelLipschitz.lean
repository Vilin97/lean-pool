/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.FlowDefs.FlowInv
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.SigmaMat
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Ingredients.HatZetaML
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Ingredients.ZetaMK
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Ingredients.Psi
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Ingredients.LIdx
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.IsHolderClass
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.IsDivFree
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.SmoothField
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ingredients.LIdxConsequences
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Construction.StreamVelContinuous

/-! Public statement. -/

@[expose] public section

open MeasureTheory Homogenization Filter Topology

noncomputable section

namespace AVenhance

/-- Uniform Lipschitz hypothesis of the `flow`, for the velocity of an admissible stream. -/
theorem IsAdmissibleStream.vel_lipschitz {φ : ℝ → Vec 2 → ℝ} (h : IsAdmissibleStream φ) :
    ∃ L : ℝ, ∀ t x y, ‖streamVel φ t x - streamVel φ t y‖ ≤ L * ‖x - y‖ := by
  obtain ⟨L, _, hL⟩ := Infra.Flow.exists_global_spatial_lipschitz
    (Infra.Construction.smoothPeriodic_streamVel h)
  exact ⟨L, hL⟩

end AVenhance
