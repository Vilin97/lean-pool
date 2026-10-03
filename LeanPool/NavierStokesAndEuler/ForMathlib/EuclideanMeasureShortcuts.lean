/-
Copyright (c) 2026 Lean Pool contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Pool contributors
-/
module

public import LeanPool.NavierStokesAndEuler.ForMathlib.EuclideanSpaceShortcuts
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis

/-!
# Shortcut instances for Lebesgue measure on real Euclidean spaces

The volume of `EuclideanSpace ℝ (Fin n)` is the measure of a finite-dimensional inner product
space with its Borel structure, so each occurrence of `volume` re-derives the inner product, the
finite dimension and the Borel structure. The shortcuts below record the measurable and measure
space structures.
-/

public section

noncomputable section

namespace NavierStokesAndEuler

open MeasureTheory

variable {n : ℕ}

/-- Shortcut for the Borel measurable structure of a real Euclidean space. -/
instance EuclideanSpaceShortcut.instMeasurableSpace :
    MeasurableSpace (EuclideanSpace ℝ (Fin n)) := inferInstance

/-- Shortcut for the Borel property of a real Euclidean space. -/
instance EuclideanSpaceShortcut.instBorelSpace : BorelSpace (EuclideanSpace ℝ (Fin n)) :=
  inferInstance

/-- Shortcut for the Lebesgue measure space structure of a real Euclidean space. -/
instance EuclideanSpaceShortcut.instMeasureSpace : MeasureSpace (EuclideanSpace ℝ (Fin n)) :=
  inferInstance

end NavierStokesAndEuler

end

end
