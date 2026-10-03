/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.SpaceTimeGradNormSq

/-! Statement file: `IsHolderClass` (Roots).
This file contains exactly one declaration of the formalization's public statement surface. -/

@[expose] public section

open MeasureTheory Filter Topology Homogenization

namespace AVenhance

/-- `b` is a bounded, continuous, `ℤ²`-periodic drift on `[0,1] × 𝕋²` that is Hölder continuous of
exponent `α` in space and in time. -/
def IsHolderClass (α : ℝ) (b : ℝ → Vec 2 → Vec 2) : Prop :=
  (∀ t ∈ Set.Icc (0 : ℝ) 1, IsZ2Periodic (b t)) ∧
  ContinuousOn (fun p : ℝ × Vec 2 => b p.1 p.2) (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ) ∧
  (∃ C : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x, ‖b t x‖ ≤ C) ∧
  (∃ C : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x y, ‖b t x - b t y‖ ≤ C * ‖x - y‖ ^ α) ∧
  (∃ C : ℝ, ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x,
    ‖b s x - b t x‖ ≤ C * |s - t| ^ α)

end AVenhance
