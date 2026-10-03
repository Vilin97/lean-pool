/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.RadiusIteration

/-! # Radius Iteration -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch01

noncomputable section

/-!
# Standard radius iteration

This file exposes the proved radius-iteration backbone used by the
coarse-grained Caccioppoli argument.  The current proved surface is normalized
to the interval `[1/3, 1]`, which is the interval used later in the book.
-/

/-- Public name for the normalized radius-iteration constant. -/
noncomputable abbrev standardRadiusIterationConstant (β : ℝ) : ℝ :=
  Homogenization.coarseCaccioppoliRadiusIterationConst β

/-- The normalized radius-iteration constant is nonnegative. -/
theorem standardRadiusIterationConstant_nonneg (β : ℝ) :
    0 ≤ standardRadiusIterationConstant β := by
  simpa [standardRadiusIterationConstant] using
    Homogenization.coarseCaccioppoliRadiusIterationConst_nonneg β

/-- Public normalized standard radius iteration on `[1/3, 1]`. -/
theorem standardRadiusIteration
    {F : ℝ → ℝ} {A β : ℝ}
    (hβ : 0 ≤ β) (hA : 0 ≤ A)
    (hbounded : Homogenization.CoarseCaccioppoliRadiusBoundedAbove F)
    (hrec : Homogenization.CoarseCaccioppoliRadiusRecurrence F A β) :
    F (1 / 3 : ℝ) ≤ A * standardRadiusIterationConstant β := by
  simpa [standardRadiusIterationConstant] using
    Homogenization.coarseCaccioppoli_radius_iteration hβ hA hbounded hrec

/-- Public radius iteration for the deterministic radius sequence. -/
theorem standardRadiusIteration_of_sequenceRecurrence
    {F : ℝ → ℝ} {A β : ℝ}
    (hβ : 0 ≤ β) (hA : 0 ≤ A)
    (hbounded : Homogenization.CoarseCaccioppoliRadiusBoundedAbove F)
    (hrec : Homogenization.CoarseCaccioppoliRadiusSequenceRecurrence F A β) :
    F (1 / 3 : ℝ) ≤ A * standardRadiusIterationConstant β := by
  simpa [standardRadiusIterationConstant] using
    Homogenization.coarseCaccioppoli_radius_iteration_of_sequenceRecurrence
      hβ hA hbounded hrec

end

end Ch01
end Book
end Homogenization
