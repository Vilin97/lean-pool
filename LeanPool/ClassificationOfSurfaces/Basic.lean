/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie, Jack McCarthy
-/
module

public import LeanPool.ClassificationOfSurfaces.EvalStatement
public import LeanPool.ClassificationOfSurfaces.Examples

import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.SimpleGraph.Init
import Mathlib.MeasureTheory.Covering.Besicovitch

/-!
# Classification of compact surfaces

This module re-exports the current project skeleton for the Lean Eval challenge
`topological_classification_of_surfaces`.
-/

@[expose] public section
