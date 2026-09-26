/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
module


public import LeanPool.OperatorTheory.Operator.NumericalRange.Radius

/-!
# Set-theoretic characterization of numerical radius

The inequality `w(A) ≤ r` is equivalent to containment of the numerical
range, or its closure, in the closed disk of radius `r` about zero.
-/

@[expose] public section

open Set
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- A nonnegative real bounds the numerical radius exactly when it bounds the
modulus of every point in the numerical range. -/
theorem numericalRadius_le_iff
    (A : E →L[ℂ] E) {r : ℝ} (hr : 0 ≤ r) :
    numericalRadius A ≤ r ↔ ∀ z ∈ numericalRange A, ‖z‖ ≤ r := by
  constructor
  · exact fun h z hz => (norm_le_numericalRadius A hz).trans h
  · intro h
    unfold numericalRadius
    exact Real.iSup_le (fun z => Real.iSup_le (fun hz => h z hz) hr) hr

/-- Closed-disk form of `numericalRadius_le_iff`. -/
theorem numericalRadius_le_iff_numericalRange_subset_closedBall
    (A : E →L[ℂ] E) {r : ℝ} (hr : 0 ≤ r) :
    numericalRadius A ≤ r ↔
      numericalRange A ⊆ Metric.closedBall 0 r := by
  rw [numericalRadius_le_iff A hr]
  simp only [Set.subset_def, Metric.mem_closedBall, dist_zero_right]

/-- The same disk characterization holds for the closed numerical range. -/
theorem numericalRadius_le_iff_closure_numericalRange_subset_closedBall
    (A : E →L[ℂ] E) {r : ℝ} (hr : 0 ≤ r) :
    numericalRadius A ≤ r ↔
      closure (numericalRange A) ⊆ Metric.closedBall 0 r := by
  constructor
  · intro h
    apply closure_minimal
    · exact (numericalRadius_le_iff_numericalRange_subset_closedBall A hr).1 h
    · exact Metric.isClosed_closedBall
  · intro h
    apply (numericalRadius_le_iff_numericalRange_subset_closedBall A hr).2
    exact subset_closure.trans h

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
