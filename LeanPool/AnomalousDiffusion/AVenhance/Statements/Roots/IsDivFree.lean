/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.IsHolderClass

/-! Statement file: `IsDivFree` (Roots).
This file contains exactly one declaration of the formalization's public statement surface. -/

@[expose] public section

open MeasureTheory Filter Topology Homogenization

namespace AVenhance

/-- Distributional divergence-free on each time slice `t ∈ [0,1]`.
Meaningful only together with local integrability of `b t` (in the main theorem it is
conjoined with `IsHolderClass`, which gives continuity and boundedness). -/
def IsDivFree (b : ℝ → Vec 2 → Vec 2) : Prop :=
  ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ φ : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
    ∫ x, vecDot (b t x) (spaceGrad φ x) = 0

end AVenhance
