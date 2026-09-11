/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.IsBoundedAtImInfty

import Mathlib.Algebra.Order.Algebra
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Positivity.Finset

/-!
# Boundedness of Eisenstein series

All of the lemmas formerly defined here have been upstreamed into
`Mathlib.NumberTheory.ModularForms.EisensteinSeries.IsBoundedAtImInfty`; this file is now
a re-export.
-/

@[expose] public section
