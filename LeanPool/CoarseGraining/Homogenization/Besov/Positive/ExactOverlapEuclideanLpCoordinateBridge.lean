/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Besov.Positive.ExactOverlapEuclideanLp
import LeanPool.CoarseGraining.Homogenization.Besov.Positive.ExactOverlapScalarP
import LeanPool.CoarseGraining.Homogenization.Sobolev.FiniteLpCoordinate

/-!
# Coordinate bridge for the finite-`p` Euclidean overlap oscillation

The canonical finite-`p` Euclidean overlap seminorm is defined directly from
the Hilbert realization of its vector fluctuation.  This file records the
local, exact coordinate identification with the scalar overlap fluctuation and
the one-coordinate `L^p` bound.  It deliberately contains no aggregation over
coordinates, centers, or depths.
-/

namespace Homogenization

open MeasureTheory

noncomputable section

namespace ScalarOverlap

/-- A coordinate of the vector overlap average is exactly the scalar overlap
average of that coordinate. -/
theorem cubeAverageVec_apply_eq_cubeAverage {d : ℕ} (S : TriadicCube d)
    (F : Vec d → Vec d) (i : Fin d) :
    cubeAverageVec S F i = cubeAverage S (fun x => F x i) :=
  rfl

end ScalarOverlap

/-- The coordinate of the canonical Euclidean overlap residual is the scalar
overlap residual of the same coordinate. -/
theorem euclideanOverlapResidual_coordinate_eq_scalar {d : ℕ} (S : TriadicCube d)
    (F : Vec d → Vec d) (i : Fin d) :
    (fun x => (F x - ScalarOverlap.cubeAverageVec S F) i) =
      fun x => F x i - ScalarOverlap.cubeAverage S (fun y => F y i) := by
  funext x
  rw [Pi.sub_apply, ScalarOverlap.cubeAverageVec_apply_eq_cubeAverage]

/-- The scalar overlap oscillation written using its scalar average is exactly
the corresponding coordinate of the canonical Euclidean overlap residual. -/
theorem scalarOverlap_eLpNorm_eq_coordinate_euclideanOverlapResidual {d : ℕ}
    (S : TriadicCube d) (p : FiniteLpExponent) (F : Vec d → Vec d) (i : Fin d) :
    eLpNorm (fun x => F x i - ScalarOverlap.cubeAverage S (fun y => F y i))
        p.exponent (ScalarOverlap.normalizedCubeMeasure S) =
      eLpNorm (fun x => (F x - ScalarOverlap.cubeAverageVec S F) i)
        p.exponent (ScalarOverlap.normalizedCubeMeasure S) := by
  rw [euclideanOverlapResidual_coordinate_eq_scalar]

/-- The scalar overlap oscillation of a coordinate is the real value of the
corresponding coordinate of the canonical Euclidean residual. -/
theorem cubeBesovOverlapOscillation_coordinate_eq_residual_toReal {d : ℕ}
    (S : TriadicCube d) (p : FiniteLpExponent) (F : Vec d → Vec d) (i : Fin d) :
    cubeBesovOverlapOscillation S p.exponent (fun x => F x i) =
      (eLpNorm (fun x => (F x - ScalarOverlap.cubeAverageVec S F) i)
        p.exponent (ScalarOverlap.normalizedCubeMeasure S)).toReal := by
  unfold cubeBesovOverlapOscillation ScalarOverlap.cubeLpNorm
  rw [scalarOverlap_eLpNorm_eq_coordinate_euclideanOverlapResidual]

/-- One scalar coordinate of the overlap oscillation is bounded by the direct
Euclidean Hilbert overlap oscillation on the same cube. -/
theorem scalarOverlap_eLpNorm_le_euclideanOverlap {d : ℕ} (S : TriadicCube d)
    (p : FiniteLpExponent) (F : Vec d → Vec d) (i : Fin d) :
    eLpNorm (fun x => F x i - ScalarOverlap.cubeAverage S (fun y => F y i))
        p.exponent (ScalarOverlap.normalizedCubeMeasure S) ≤
      eLpNorm (fun x => HilbertVec.ofVec (F x - ScalarOverlap.cubeAverageVec S F))
        p.exponent (ScalarOverlap.normalizedCubeMeasure S) := by
  rw [scalarOverlap_eLpNorm_eq_coordinate_euclideanOverlapResidual]
  exact coordinate_eLpNorm_le_euclidean (ScalarOverlap.normalizedCubeMeasure S) p
    (fun x => F x - ScalarOverlap.cubeAverageVec S F) i

end

end Homogenization
