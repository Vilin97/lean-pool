/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.ExplicitFormula.CompletedZetaRectangle
public import Mathlib.Order.Interval.Set.Infinite

/-!
# Zero Free Rectangles

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/

@[expose] public section

noncomputable section

open Complex NumberField Set

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]

theorem poleClearedCompletedDedekindZetaContinuation_ne_zero_of_re_lt_zero
    {s : ℂ} (hs : s.re < 0) :
    poleClearedCompletedDedekindZetaContinuation K s ≠ 0 := by
  rw [poleClearedCompletedDedekindZetaContinuation_functionalEquation K s]
  apply poleClearedCompletedDedekindZetaContinuation_ne_zero_of_one_lt_re K
  simp only [sub_re, one_re]
  linarith

end NumberField.Odlyzko
