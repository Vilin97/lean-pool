/-
Copyright (c) 2026 PFR contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PFR contributors
-/

module

public import Mathlib.MeasureTheory.Measure.Dirac

/-!
# LeanPool.ZhangYeungInequality.PFR.Mathlib.MeasureTheory.Measure.Dirac

Imported Lean Pool material for
`LeanPool.ZhangYeungInequality.PFR.Mathlib.MeasureTheory.Measure.Dirac`.
-/

public section

namespace MeasureTheory.Measure
variable {α : Type*} [MeasurableSpace α] {s : Set α} {a : α}

@[simp]
lemma dirac_real_apply' (a : α) (hs : MeasurableSet s) : (dirac a).real s = s.indicator 1 a := by
  by_cases ha : a ∈ s <;> simp [Measure.real, *]

end MeasureTheory.Measure
