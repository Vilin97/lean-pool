/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.UnitCube

/-! Statement file: `IsPeriodicH1With` (Roots).
This file contains exactly one declaration of the formalization's public statement surface. -/

@[expose] public section

open MeasureTheory Filter Topology Homogenization

namespace AVenhance

/-- Periodic `H¹` with an explicit gradient `Du`. -/
def IsPeriodicH1With (u : Vec 2 → ℝ) (Du : Vec 2 → Vec 2) : Prop :=
  IsZ2Periodic u ∧ IsZ2Periodic Du ∧ MemL2On unitCube u ∧ GradMemL2On unitCube Du ∧
    HasWeakGradientOn Set.univ u Du

end AVenhance
