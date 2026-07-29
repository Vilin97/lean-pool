/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.Analysis.Fourier.FourierTransform

/-! TODO: Add doc-string. -/

@[expose] public section

noncomputable section

open MeasureTheory

namespace NumberField.Odlyzko

/-- A cosine transform used in the Odlyzko-bound argument. -/
def Poitou.cosineTransform (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ x : ℝ, f x * Real.cos (t * x)

/-- Conditions on a test function used in Poitou's explicit formula. -/
structure Poitou.Admissible (f : ℝ → ℝ) : Prop where
  continuous : Continuous f
  even : ∀ x, f (-x) = f x
  value_zero : f 0 = 1
  nonnegative : ∀ x, 0 ≤ f x
  integrable : Integrable f
  cosineTransform_nonnegative : ∀ t, 0 ≤ Poitou.cosineTransform f t

end NumberField.Odlyzko
