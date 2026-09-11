/-
Copyright (c) 2026 D.S. McNeil, Gábor P. Nagy, Attila Vajda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D.S. McNeil, Gábor P. Nagy, Attila Vajda
-/
module

import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic.Positivity.Finset

/-!
# Explicit Mathlib dependencies for the Kasami development

The source project used `import Mathlib` for convenience.  Lean Pool keeps the
dependency surface explicit so that the entry point does not pull in the whole
Mathlib umbrella.
-/

@[expose] public section
