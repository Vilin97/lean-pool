/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.Homogenization.Sobolev.H1.Definitions

/-! Statement file: `latticeShift` (Roots).
This file contains exactly one declaration of the formalization's public statement surface. -/

@[expose] public section

open MeasureTheory Filter Topology Homogenization

namespace AVenhance

/-- Integer translation `x ↦ x + n` on `Vec 2`. -/
def latticeShift (n : Fin 2 → ℤ) : Vec 2 := fun i => (n i : ℝ)

end AVenhance
