/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

module

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.Tactic.Positivity.Finset

/-! # Uniformcts -/


@[expose] public section


/-!
# Products of one plus a complex number

We gather some results about the uniform convergence of the product of `1 + f n x` for a
sequence `f n x` or complex numbers.

-/

open Filter Function Complex Real

open scoped Interval Topology BigOperators Nat Complex

variable {α β ι : Type*}
