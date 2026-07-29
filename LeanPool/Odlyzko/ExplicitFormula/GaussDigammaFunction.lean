/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.ExplicitFormula.GaussDigammaBounds

/-!
# Gauss Digamma Function

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/

@[expose] public section

noncomputable section

open Complex MeasureTheory Real Set

namespace NumberField.Odlyzko

/-- A gauss digamma used in the Odlyzko-bound argument. -/
noncomputable def gaussDigamma (s : ℂ) : ℂ :=
  -Real.eulerMascheroniConstant +
    ∫ x : ℝ in Ioi 0, gaussDigammaIntegrand s x

end NumberField.Odlyzko
