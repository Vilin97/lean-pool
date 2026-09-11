/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import LeanPool.LeanModularForms.GeneralizedResidueTheory.WindingNumber.Defs
public import LeanPool.LeanModularForms.GeneralizedResidueTheory.WindingNumber.CrossingAnalysis
public import LeanPool.LeanModularForms.GeneralizedResidueTheory.WindingNumber.Decomposition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.MeasureTheory.Covering.Besicovitch

/-!
# Winding Number Theory

Barrel file re-exporting the three submodules:

* `Defs` — angle definitions, crossing angle theorems, translation
* `CrossingAnalysis` — monotonicity, cutoff boundaries, direction convergence
* `Decomposition` — H-W Prop 2.2, main decomposition theorems
-/

@[expose] public section
