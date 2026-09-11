/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.NumberTheory.ModularForms.Bounds
public import LeanPool.LeanModularForms.ForMathlib.Petersson

import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Positivity.Finset

/-!
# Bounds for modular forms

All of the lemmas formerly defined here (`truncatedFundamentalDomain`, the family of
`exists_bound_*` lemmas, `ModularFormClass.exists_bound`, `CuspFormClass.exists_bound`,
`qExpansion_isBigO`, …) have been upstreamed into
`Mathlib.NumberTheory.ModularForms.Bounds`, phrased there for an arithmetic `Γ : Subgroup
(GL (Fin 2) ℝ)`.  This file is now a re-export to keep the historical import path working.
-/

@[expose] public section
