/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.ExplicitFormula.TartarPoitouTransform
public import Mathlib.Analysis.Complex.PhragmenLindelof

/-!
# Tartar Poitou Positivity

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/

@[expose] public section

noncomputable section

open Asymptotics Complex Filter MeasureTheory Set
open scoped Topology

namespace NumberField.Odlyzko

/-- A poitou critical strip used in the Odlyzko-bound argument. -/
def poitouCriticalStrip : Set ℂ := re ⁻¹' Ioo 0 1

/-- A poitou closed critical strip used in the Odlyzko-bound argument. -/
def poitouClosedCriticalStrip : Set ℂ := re ⁻¹' Icc 0 1

end NumberField.Odlyzko
