/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.ExplicitFormula.SelectedHeightHorizontalVanishing

/-!
# Poitou Estimate

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/

@[expose] public section

noncomputable section

open NumberField

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]

theorem totallyComplexPoitouEstimate :
    TotallyComplexPoitouEstimate K := by
  apply totallyComplexPoitouEstimate_of_regularizedRightVerticalLowerBound
    K (σ := 2) (by norm_num)
  exact regularizedRightVerticalLowerBound_two K odlyzkoScale_pos.ne'

theorem odlyzkoBound
    (hdim : 18 ≤ Module.finrank ℚ K) :
    |(discr K : ℝ)| ≥ (8.25 : ℝ) ^ Module.finrank ℚ K :=
  odlyzkoBound_of_poitouEstimate K hdim (totallyComplexPoitouEstimate K)

end NumberField.Odlyzko
