/-
Copyright (c) 2026 AleksandrovDifferentiability contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/

module

public import LeanPool.ViscositySolutionTheory.AleksandrovDifferentiability.Statements.Cube.Basic.Sets

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Measure assembly for source-cube bad sets

This file contains finite-union measure bookkeeping for the source upper-contact estimate. The
analytic estimates for individual coordinate slices live elsewhere; this module packages the
common finite-union step.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped MeasureTheory BigOperators

namespace AleksandrovDifferentiability

/-- The total source bad set is bounded by the non-differentiability bad set plus the sum of the
coordinate bad-set measures. -/
theorem volume_upperContactEstimateTotalBadSet_le_nonDifferentiable_add_sum_coordinate
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {sliceBad : CoordinateSliceBadPredicate n} {t : ℝ} :
    volume (upperContactEstimateTotalBadSet u sliceBad t) ≤
      volume (sourceOpenCube n 1 \ firstOrderDifferentiabilitySet u) +
        ∑ i : Fin n, volume (coordinateSliceBadSet sliceBad i t) := by
  have hmeasure_union :=
    measure_union_le (μ := volume)
      (sourceOpenCube n 1 \ firstOrderDifferentiabilitySet u)
      (⋃ i : Fin n, coordinateSliceBadSet sliceBad i t)
  have hmeasure_iUnion :
      volume (⋃ i : Fin n, coordinateSliceBadSet sliceBad i t) ≤
        ∑ i : Fin n, volume (coordinateSliceBadSet sliceBad i t) := by
    simpa using
      (measure_iUnion_fintype_le (μ := volume)
        (fun i : Fin n => coordinateSliceBadSet sliceBad i t))
  dsimp [upperContactEstimateTotalBadSet]
  exact hmeasure_union.trans (add_le_add_right hmeasure_iUnion _)

/-- If the non-differentiability bad set is null and each coordinate bad set has a prescribed
bound, then the total source bad set is bounded by the finite sum of those bounds. -/
theorem volume_upperContactEstimateTotalBadSet_le_sum_of_coordinate_bounds
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {sliceBad : CoordinateSliceBadPredicate n}
    {t : ℝ} {B : Fin n → ENNReal}
    (hdiff : volume (sourceOpenCube n 1 \ firstOrderDifferentiabilitySet u) = 0)
    (hcoord : ∀ i : Fin n, volume (coordinateSliceBadSet sliceBad i t) ≤ B i) :
    volume (upperContactEstimateTotalBadSet u sliceBad t) ≤ ∑ i : Fin n, B i := by
  calc
    volume (upperContactEstimateTotalBadSet u sliceBad t)
        ≤ volume (sourceOpenCube n 1 \ firstOrderDifferentiabilitySet u) +
            ∑ i : Fin n, volume (coordinateSliceBadSet sliceBad i t) :=
      volume_upperContactEstimateTotalBadSet_le_nonDifferentiable_add_sum_coordinate
    _ = ∑ i : Fin n, volume (coordinateSliceBadSet sliceBad i t) := by simp [hdiff]
    _ ≤ ∑ i : Fin n, B i := Finset.sum_le_sum fun i _ => hcoord i

/-- Constant-bound version of
`volume_upperContactEstimateTotalBadSet_le_sum_of_coordinate_bounds`. -/
theorem volume_upperContactEstimateTotalBadSet_le_card_mul_of_coordinate_bound
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {sliceBad : CoordinateSliceBadPredicate n}
    {t : ℝ} {B : ENNReal}
    (hdiff : volume (sourceOpenCube n 1 \ firstOrderDifferentiabilitySet u) = 0)
    (hcoord : ∀ i : Fin n, volume (coordinateSliceBadSet sliceBad i t) ≤ B) :
    volume (upperContactEstimateTotalBadSet u sliceBad t) ≤ (n : ENNReal) * B := by
  calc
    volume (upperContactEstimateTotalBadSet u sliceBad t)
        ≤ ∑ _i : Fin n, B :=
      volume_upperContactEstimateTotalBadSet_le_sum_of_coordinate_bounds hdiff hcoord
    _ = (n : ENNReal) * B := by
      simp [Finset.sum_const, nsmul_eq_mul]

end AleksandrovDifferentiability
