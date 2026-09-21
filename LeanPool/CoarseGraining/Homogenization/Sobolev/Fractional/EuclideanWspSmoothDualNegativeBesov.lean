/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch03.ABK26.NegativeBesov

/-!
# Scalar-coordinate envelopes for the source negative Besov seminorm

This module keeps the source-facing vector negative Besov seminorm distinct
from the scalar circ quantities used by the projection duality argument.  It
only records the elementary coordinate envelope: each scalar coordinate of a
vector field has no larger running-scale block-average envelope.
-/

namespace Homogenization
namespace Book
namespace Ch03
namespace ABK26

open scoped BigOperators ENNReal

noncomputable section

/-- The scalar running-scale depth energy of one coordinate of the represented
`L²` field.  This is deliberately an auxiliary envelope, not a redefinition of
the source-facing vector seminorm. -/
noncomputable def cubeEuclideanNegativeBesovScalarDepthEnergy {d : ℕ}
    (Q : TriadicCube d) (s : FractionalOrder) (p : FiniteLpExponent)
    (F : CubeEuclideanLpField Q FiniteLpExponent.two) (i : Fin d) (j : ℕ) : ℝ≥0∞ := by
  classical
  exact ENNReal.ofReal
      (Real.rpow 3
        (s.1 * p.exponent.toReal *
          (((Q.scale - (j : ℤ) : ℤ) : ℝ)))) *
    ((descendantsAtScale Q (Q.scale - (j : ℤ))).card : ℝ≥0∞)⁻¹ *
      (descendantsAtScale Q (Q.scale - (j : ℤ))).attach.sum (fun R =>
        (ENNReal.ofReal |cubeAverage R.1 (fun x => F.toField x i)|) ^
          p.exponent.toReal)

/-- Finite-depth scalar circ envelope, with the same running-scale weights as
the source negative Besov quantity. -/
noncomputable def cubeEuclideanNegativeBesovScalarPartialENorm {d : ℕ}
    (Q : TriadicCube d) (s : FractionalOrder) (p : FiniteLpExponent)
    (F : CubeEuclideanLpField Q FiniteLpExponent.two) (i : Fin d) (N : ℕ) : ℝ≥0∞ :=
  (∑ j ∈ Finset.range N, cubeEuclideanNegativeBesovScalarDepthEnergy Q s p F i j) ^
    (p.exponent.toReal)⁻¹

/-- The infinite scalar circ envelope of a coordinate, retained separately
from the vector source seminorm. -/
noncomputable def cubeEuclideanNegativeBesovScalarENorm {d : ℕ}
    (Q : TriadicCube d) (s : FractionalOrder) (p : FiniteLpExponent)
    (F : CubeEuclideanLpField Q FiniteLpExponent.two) (i : Fin d) : ℝ≥0∞ :=
  (∑' j, cubeEuclideanNegativeBesovScalarDepthEnergy Q s p F i j) ^
    (p.exponent.toReal)⁻¹

theorem cubeEuclideanNegativeBesovScalarDepthEnergy_le {d : ℕ}
    (Q : TriadicCube d) (s : FractionalOrder) (p : FiniteLpExponent)
    (F : CubeEuclideanLpField Q FiniteLpExponent.two) (i : Fin d) (j : ℕ) :
    cubeEuclideanNegativeBesovScalarDepthEnergy Q s p F i j ≤
      cubeEuclideanNegativeBesovDepthEnergy Q s p F j := by
  classical
  unfold cubeEuclideanNegativeBesovScalarDepthEnergy
    cubeEuclideanNegativeBesovDepthEnergy
  gcongr
  simpa [cubeAverageVec] using norm_le_pi_norm (cubeAverageVec _ F.toField) i

theorem cubeEuclideanNegativeBesovScalarPartialENorm_le {d : ℕ}
    (Q : TriadicCube d) (s : FractionalOrder) (p : FiniteLpExponent)
    (F : CubeEuclideanLpField Q FiniteLpExponent.two) (i : Fin d) (N : ℕ) :
    cubeEuclideanNegativeBesovScalarPartialENorm Q s p F i N ≤
      cubeEuclideanNegativeBesovESeminorm Q s p F := by
  unfold cubeEuclideanNegativeBesovScalarPartialENorm
  rw [cubeEuclideanNegativeBesovESeminorm_eq_tsum_depthEnergy]
  apply ENNReal.rpow_le_rpow
  · calc
      ∑ j ∈ Finset.range N, cubeEuclideanNegativeBesovScalarDepthEnergy Q s p F i j ≤
          ∑ j ∈ Finset.range N, cubeEuclideanNegativeBesovDepthEnergy Q s p F j := by
            gcongr with j hj
            exact cubeEuclideanNegativeBesovScalarDepthEnergy_le Q s p F i j
      _ ≤ ∑' j, cubeEuclideanNegativeBesovDepthEnergy Q s p F j :=
        ENNReal.sum_le_tsum (Finset.range N)
  · exact inv_nonneg.mpr (by positivity)

theorem cubeEuclideanNegativeBesovScalarENorm_le {d : ℕ}
    (Q : TriadicCube d) (s : FractionalOrder) (p : FiniteLpExponent)
    (F : CubeEuclideanLpField Q FiniteLpExponent.two) (i : Fin d) :
    cubeEuclideanNegativeBesovScalarENorm Q s p F i ≤
      cubeEuclideanNegativeBesovESeminorm Q s p F := by
  unfold cubeEuclideanNegativeBesovScalarENorm
  rw [cubeEuclideanNegativeBesovESeminorm_eq_tsum_depthEnergy]
  apply ENNReal.rpow_le_rpow
  · exact ENNReal.tsum_le_tsum
      (cubeEuclideanNegativeBesovScalarDepthEnergy_le Q s p F i)
  · exact inv_nonneg.mpr (by positivity)

end

end ABK26
end Ch03
end Book
end Homogenization
