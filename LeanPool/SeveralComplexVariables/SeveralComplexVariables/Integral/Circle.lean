/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.MeasureTheory.Integral.CircleAverage
public import Mathlib.MeasureTheory.Integral.CircleIntegral

/-!
# Circle integrability of maxima and reflection invariance of circle averages

The maximum of two real-valued functions integrable on a circle is integrable there, and circle
averages are invariant under the antipodal reflection of the circle.

## Main results

* `CircleIntegrable.max`: Maxima of circle-integrable functions are circle integrable.
* `Real.circleAverage_reflect`: The circle average is invariant under the antipodal reflection of
  the circle.
-/

public section

open Complex MeasureTheory Real

/-- Maxima of circle-integrable functions are circle integrable. -/
theorem CircleIntegrable.max {u v : ℂ → ℝ} {c : ℂ} {R : ℝ} (hu : CircleIntegrable u c R)
    (hv : CircleIntegrable v c R) : CircleIntegrable (fun z => max (u z) (v z)) c R := by
  rw [circleIntegrable_def] at hu hv ⊢
  exact ⟨hu.1.sup hv.1, hu.2.sup hv.2⟩

/-- The circle average is invariant under the antipodal reflection of the circle. -/
theorem Real.circleAverage_reflect (u : ℂ → ℝ) (c : ℂ) (r : ℝ) :
    circleAverage (fun t => u (2 * c - t)) c r = circleAverage u c r := by
  rw [circleAverage_eq_integral_add (f := u) π, circleAverage_def]
  congr 1
  refine intervalIntegral.integral_congr fun θ _ => ?_
  simp only [circleMap]
  congr 1
  rw [Complex.ofReal_add, add_mul, Complex.exp_add, Complex.exp_pi_mul_I]
  ring

end

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
