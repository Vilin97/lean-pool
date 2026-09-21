/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex

/-!
# Measurability of complex powers with a real base

This file is a temporary home for a measurability result intended for the Mathlib theory of
complex powers.  It is independent of the multivariate Beta function.
-/

public noncomputable section

namespace Complex

/-- Raising a real number, regarded as a complex number, to a fixed complex power is measurable.
The possible discontinuity at zero does not affect measurability. -/
theorem measurable_ofReal_cpow_const (c : ℂ) :
    Measurable fun x : ℝ => (x : ℂ) ^ c :=
  measurable_of_continuousOn_compl_singleton (0 : ℝ) fun x hx =>
    (continuousAt_ofReal_cpow_const x c (Or.inr hx)).continuousWithinAt

end Complex

end
