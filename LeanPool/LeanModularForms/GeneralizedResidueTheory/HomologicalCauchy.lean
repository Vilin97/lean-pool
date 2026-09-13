/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import LeanPool.LeanModularForms.GeneralizedResidueTheory.HomologicalCauchy.Basic
public import LeanPool.LeanModularForms.GeneralizedResidueTheory.HomologicalCauchy.DixonProof
public import LeanPool.LeanModularForms.GeneralizedResidueTheory.HomologicalCauchy.Meromorphic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.MeasureTheory.Covering.Besicovitch

/-!
# Null-Homologous Curves and the Cauchy Integral Theorem

Barrel file re-exporting the three submodules:

* `Basic` — `IsNullHomologous`, FTC for piecewise C¹ contours, convexity bridge
* `DixonProof` — Dixon's proof: h₁, h₂, Liouville, Cauchy integral formula
* `Meromorphic` — meromorphic contour integral vanishing, higher-order cancellation
-/

@[expose] public section
