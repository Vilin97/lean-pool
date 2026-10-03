/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.SigmaMat

/-! Statement file: `spaceAvg` (Section3).
This file contains exactly one declaration of the formalization's public statement surface. -/

@[expose] public section

open MeasureTheory Homogenization

noncomputable section

namespace AVenhance

/-- `⟨f⟩ = ⨍_{𝕋²} f dx` (line 921), as the integral over the open unit cube (`|𝕋²| = 1`). -/
def spaceAvg (f : Vec 2 → ℝ) : ℝ := ∫ x in unitCube, f x

end AVenhance
