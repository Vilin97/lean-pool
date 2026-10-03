/-
Copyright (c) 2026 Lean Pool contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Pool contributors
-/
module

public import LeanPool.NavierStokesAndEuler.ForMathlib.L2NormedShortcuts
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Shortcut instances for the Hilbert structure of `L²` spaces

The inner product space structure and completeness of `MeasureTheory.Lp E 2 μ`, registered on top
of the normed-space shortcuts of `L2NormedShortcuts`.
-/

public section

noncomputable section

namespace NavierStokesAndEuler

open MeasureTheory

variable {α E : Type*} {m : MeasurableSpace α} {μ : Measure α} [NormedAddCommGroup E]

/-- Shortcut for the completeness of an `L²` space. -/
instance L2Shortcut.instCompleteSpace [CompleteSpace E] : CompleteSpace (Lp E 2 μ) :=
  inferInstance

variable [InnerProductSpace ℝ E]

/-- Shortcut for the real inner product space structure of an `L²` space. -/
instance L2Shortcut.instInnerProductSpace : InnerProductSpace ℝ (Lp E 2 μ) := inferInstance

/-- Shortcut for the real inner product of an `L²` space. -/
instance L2Shortcut.instInner : Inner ℝ (Lp E 2 μ) := inferInstance

end NavierStokesAndEuler

end

end
