/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.IsZ2Periodic

/-! Statement file: `unitCube` (Roots).
This file contains exactly one declaration of the formalization's public statement surface. -/

@[expose] public section

open MeasureTheory Filter Topology Homogenization

namespace AVenhance

/-- The open unit cube `(0,1)²`, a full-measure representative of the fundamental cell of `𝕋²`. -/
def unitCube : Set (Vec 2) := Set.pi Set.univ fun _ => Set.Ioo (0 : ℝ) 1

end AVenhance
