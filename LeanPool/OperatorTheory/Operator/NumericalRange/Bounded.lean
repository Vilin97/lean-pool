/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
/-
# Boundedness of the numerical range (L1.2)

The numerical range of a continuous linear operator `A` on a complex inner product space is
contained in the closed disk of radius `‖A‖`: for a unit vector `x`, Cauchy–Schwarz gives
`‖⟪x, A x⟫_ℂ‖ ≤ ‖x‖ * ‖A x‖ ≤ ‖x‖ ^ 2 * ‖A‖ = ‖A‖`.

## Main declarations

* `norm_le_of_mem_numericalRange` — `‖z‖ ≤ ‖A‖` for every `z ∈ numericalRange A`.
* `numericalRange_subset_closedBall` and `isBounded_numericalRange` — the
  corresponding set-level forms.
* `numericalRadius` — the supremum of `‖z‖` over the numerical range, with
  its elementary nonnegativity and operator-norm bound.

No completeness assumption on `E` is needed. (Recreated in run-003; the original file was not
recovered after the accidental deletion.)
-/
import Mathlib.Analysis.Normed.Operator.Basic
import LeanPool.OperatorTheory.Operator.NumericalRange.Basic

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The numerical range lies in the closed disk of radius `‖A‖`: for a unit vector `x`,
Cauchy–Schwarz gives `‖⟪x, A x⟫_ℂ‖ ≤ ‖x‖ * ‖A x‖ ≤ ‖A‖`. -/
theorem norm_le_of_mem_numericalRange (A : E →L[ℂ] E)
    {z : ℂ} (hz : z ∈ numericalRange A) : ‖z‖ ≤ ‖A‖ := by
  obtain ⟨x, hx, rfl⟩ := hz
  calc ‖⟪x, A x⟫_ℂ‖ ≤ ‖x‖ * ‖A x‖ := norm_inner_le_norm x (A x)
    _ ≤ ‖x‖ * (‖A‖ * ‖x‖) := by gcongr; exact A.le_opNorm x
    _ = ‖A‖ := by rw [hx]; ring

/-- The numerical range is contained in the closed disk centered at zero
with radius the operator norm. -/
theorem numericalRange_subset_closedBall (A : E →L[ℂ] E) :
    numericalRange A ⊆ Metric.closedBall 0 ‖A‖ := by
  intro z hz
  rw [Metric.mem_closedBall, dist_zero_right]
  exact norm_le_of_mem_numericalRange A hz

/-- The numerical range of every bounded operator is a bounded set. -/
theorem isBounded_numericalRange (A : E →L[ℂ] E) :
    Bornology.IsBounded (numericalRange A) :=
  Metric.isBounded_closedBall.subset (numericalRange_subset_closedBall A)

/-- The numerical radius is the supremum of the moduli of points in the
numerical range.  This definition also gives zero on an empty numerical
range, as happens on a subsingleton space. -/
noncomputable def numericalRadius (A : E →L[ℂ] E) : ℝ :=
  ⨆ z ∈ numericalRange A, ‖z‖

/-- The numerical radius is nonnegative. -/
theorem numericalRadius_nonneg (A : E →L[ℂ] E) :
    0 ≤ numericalRadius A :=
  Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ => norm_nonneg _

/-- Every point in the numerical range has modulus at most the numerical
radius. -/
theorem norm_le_numericalRadius (A : E →L[ℂ] E)
    {z : ℂ} (hz : z ∈ numericalRange A) : ‖z‖ ≤ numericalRadius A := by
  unfold numericalRadius
  refine le_ciSup₂
    (f := fun z (_ : z ∈ numericalRange A) => ‖z‖) ⟨‖A‖, ?_⟩ z hz
  rintro y hy
  rw [Set.mem_iUnion] at hy
  obtain ⟨w, hw⟩ := hy
  rw [Set.mem_range] at hw
  obtain ⟨hwA, rfl⟩ := hw
  exact norm_le_of_mem_numericalRange A hwA

/-- The numerical radius is bounded above by the operator norm. -/
theorem numericalRadius_le_norm (A : E →L[ℂ] E) :
    numericalRadius A ≤ ‖A‖ := by
  unfold numericalRadius
  refine Real.iSup_le (fun z => ?_) (norm_nonneg A)
  exact Real.iSup_le
    (fun hz => norm_le_of_mem_numericalRange A hz) (norm_nonneg A)

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
