/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Geometry.ConvexDomain
import LeanPool.CoarseGraining.Homogenization.Geometry.OriginCubeMeasureBridge
import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.UnitCubeEuclideanL2

/-!
# Geometry of the unit centered cube for continuous interpolation

This module gathers convention-neutral domain, measure, and metric facts for
the exact continuous interpolation theorem.  The analytic domain is the open
centered unit cube; the normalized measure retains the canonical half-open
cube carrier.
-/

namespace Homogenization

open scoped ENNReal

noncomputable section

/-- The source-facing open realization of the centered unit cube. -/
abbrev unitCenteredOpenCubeSet (d : ℕ) : Set (Vec d) :=
  openCubeSet (originCube d 0)

/-- The analytic unit cube is open, bounded, and convex in every dimension. -/
theorem isOpenBoundedConvexDomain_unitCenteredOpenCubeSet (d : ℕ) :
    IsOpenBoundedConvexDomain (unitCenteredOpenCubeSet d) :=
  isOpenBoundedConvexDomain_openCubeSet (originCube d 0)

/-- The centered unit triadic cube has literal volume one. -/
@[simp] theorem cubeVolume_originCube_zero (d : ℕ) :
    cubeVolume (originCube d 0) = 1 := by
  simp [cubeVolume]

/-- The half-open centered unit cube has Lebesgue volume one. -/
@[simp] theorem volume_cubeSet_originCube_zero (d : ℕ) :
    MeasureTheory.volume (cubeSet (originCube d 0)) = 1 := by
  exact (ENNReal.toReal_eq_one_iff _).mp (by
    simp only [volume_cubeSet_toReal, cubeVolume_originCube_zero])

/-- The source-facing open centered unit cube has Lebesgue volume one. -/
@[simp] theorem volume_openCubeSet_originCube_zero (d : ℕ) :
    MeasureTheory.volume (unitCenteredOpenCubeSet d) = 1 := by
  rw [volume_openCubeSet_eq_volume_cubeSet]
  exact volume_cubeSet_originCube_zero d

/-- The exact unit-cube domain's restricted volume is the canonical cube
measure. -/
theorem unitCenteredCubeDomain_restrictedVolume_eq_cubeMeasure (d : ℕ) :
    (unitCenteredCubeDomain d).restrictedVolume = cubeMeasure (originCube d 0) :=
  cubeBoundedMeasurableDomain_restrictedVolume_eq_cubeMeasure (originCube d 0)

/-- The exact unit-cube normalized volume is the canonical normalized cube
measure. -/
theorem unitCenteredCubeDomain_normalizedVolume_eq_normalizedCubeMeasure (d : ℕ) :
    (unitCenteredCubeDomain d).normalizedVolume =
      normalizedCubeMeasure (originCube d 0) :=
  cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure (originCube d 0)

/-- The exact unit-cube restricted volume can equivalently be read on the
source-facing open cube. -/
theorem unitCenteredCubeDomain_restrictedVolume_eq_restrict_openCubeSet (d : ℕ) :
    (unitCenteredCubeDomain d).restrictedVolume =
      MeasureTheory.volume.restrict (unitCenteredOpenCubeSet d) :=
  cubeBoundedMeasurableDomain_restrictedVolume_eq_restrict_openCubeSet (originCube d 0)

/-- The half-open and open centered unit cubes agree almost everywhere. -/
theorem cubeSet_originCube_zero_ae_eq_unitCenteredOpenCubeSet (d : ℕ) :
    cubeSet (originCube d 0) =ᵐ[MeasureTheory.volume] unitCenteredOpenCubeSet d :=
  cubeSet_originCube_ae_eq_openCubeSet 0

/-- The project ambient (sup) norm is bounded by the explicit Euclidean
magnitude. -/
theorem norm_le_euclideanNorm {d : ℕ} (x : Vec d) :
    ‖x‖ ≤ euclideanNorm x := by
  simpa only [euclideanNorm_eq_norm_ofVec] using HilbertVec.norm_le_norm_ofVec x

/-- The Euclidean magnitude is bounded by a dimension-only multiple of the
project ambient (sup) norm.  This formulation remains valid at `d = 0`. -/
theorem euclideanNorm_le_dimension_mul_norm {d : ℕ} (x : Vec d) :
    euclideanNorm x ≤ (d : ℝ) * ‖x‖ := by
  simpa only [euclideanNorm_eq_norm_ofVec] using HilbertVec.norm_ofVec_le_mul_norm x

/-- The project ambient distance is bounded by the explicit Euclidean
distance. -/
theorem dist_le_euclideanDist {d : ℕ} (x y : Vec d) :
    dist x y ≤ euclideanDist x y := by
  simpa only [dist_eq_norm, euclideanDist] using norm_le_euclideanNorm (x - y)

/-- The Euclidean distance is bounded by a dimension-only multiple of the
project ambient distance.  This formulation remains valid at `d = 0`. -/
theorem euclideanDist_le_dimension_mul_dist {d : ℕ} (x y : Vec d) :
    euclideanDist x y ≤ (d : ℝ) * dist x y := by
  simpa only [dist_eq_norm, euclideanDist] using
    euclideanNorm_le_dimension_mul_norm (x - y)

end

end Homogenization
