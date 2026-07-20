/-
Copyright (c) 2026 Wei Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wei Wang
-/
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import LeanPool.LeanStationaryHarmonicMaps.StationaryHarmonicMap.Basic

/-!
# Euclidean coordinate interface

This file is the local boundary between the project and mathlib's concrete
`EuclideanSpace` API.  The project still uses `Domain n = EuclideanSpace ℝ
(Fin n)`, but downstream files should prefer the wrappers here over direct
calls to `EuclideanSpace.*`.
-/

noncomputable section

open MeasureTheory Set
open scoped Topology BigOperators ENNReal

namespace LeanStationaryHarmonicMaps
namespace StationaryHarmonicMap

/-- The `i`-th coordinate vector in the project domain `ℝⁿ`. -/
def domainCoordUnit {n : ℕ} (i : Fin n) : Domain n :=
  EuclideanSpace.single i (1 : ℝ)

/-- Coordinate extraction via the Euclidean inner product. -/
theorem inner_domainCoordUnit_right {n : ℕ} (i : Fin n) (x : Domain n) :
    inner ℝ x (domainCoordUnit i) = x i := by
  simpa [domainCoordUnit] using
    (EuclideanSpace.inner_single_right (𝕜 := ℝ) i (1 : ℝ) x)

/-- Squared norm as the sum of squared coordinates. -/
theorem domain_norm_sq_eq_sum {n : ℕ} (x : Domain n) :
    ‖x‖ ^ 2 = ∑ i : Fin n, x i ^ 2 := by
  simpa using EuclideanSpace.real_norm_sq_eq x

/-- Sum of squared coordinates as the squared norm. -/
theorem domain_sum_sq_eq_norm_sq {n : ℕ} (x : Domain n) :
    (∑ i : Fin n, x i ^ 2) = ‖x‖ ^ 2 :=
  (domain_norm_sq_eq_sum x).symm

/-- Euclidean volume of a ball centered at the origin, exposed through the
project's `Domain` abbreviation. -/
theorem domain_volume_ball_zero (n : ℕ) [NeZero n] (r : ℝ) :
    volume (Metric.ball (0 : Domain n) r) =
      (ENNReal.ofReal r) ^ Fintype.card (Fin n) *
        ENNReal.ofReal
          (√Real.pi ^ Fintype.card (Fin n) /
            Real.Gamma (((Fintype.card (Fin n) : ℝ) / 2) + 1)) := by
  simpa [Domain] using EuclideanSpace.volume_ball (Fin n) (0 : Domain n) r

end StationaryHarmonicMap
end LeanStationaryHarmonicMaps

end
