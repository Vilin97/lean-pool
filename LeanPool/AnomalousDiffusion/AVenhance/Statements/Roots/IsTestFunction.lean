/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.IsDivFree

/-! Statement file: `IsTestFunction` (Roots).
This file contains exactly one declaration of the formalization's public statement surface. -/

@[expose] public section

open MeasureTheory Filter Topology Homogenization

namespace AVenhance

/-- Smooth space-periodic test functions on `ℝ × ℝ²`, vanishing for `t ≥ 1`. -/
def IsTestFunction (φ : ℝ → Vec 2 → ℝ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => φ p.1 p.2) ∧
  (∀ t, IsZ2Periodic (φ t)) ∧ ∀ t, 1 ≤ t → ∀ x, φ t x = 0

end AVenhance
