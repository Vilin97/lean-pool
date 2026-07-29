/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.ExplicitFormula.RegularizedGaussKernelIntegral
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Regularized Gauss Fubini

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/

@[expose] public section

noncomputable section

open Complex MeasureTheory Real Set

namespace NumberField.Odlyzko

/-- A gauss digamma vertical majorant used in the Odlyzko-bound argument. -/
noncomputable def gaussDigammaVerticalMajorant (σ x : ℝ) : ℝ :=
  (Real.exp (-x) + Real.exp (-σ * x)) /
    (1 - Real.exp (-x))

end NumberField.Odlyzko
