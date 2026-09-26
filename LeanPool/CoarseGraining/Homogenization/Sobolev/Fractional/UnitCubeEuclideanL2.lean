/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Multiscale.NormalizedDomainCube
public import LeanPool.CoarseGraining.Homogenization.Sobolev.NormalizedLp
public import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-!
# Euclidean `L²` fields on the unit centered cube

This common source-facing carrier is the Euclidean vector `L²` input used by
the Chapter 1 analytic kernels on the unit centered cube.
-/

@[expose] public section

namespace Homogenization

open scoped ENNReal

noncomputable section

/-- The bounded measurable realization of the unit centered cube. -/
noncomputable def unitCenteredCubeDomain (d : ℕ) : BoundedMeasurableDomain d :=
  cubeBoundedMeasurableDomain (originCube d 0)

/-- The common fractional-order carrier `0 < s < 1`. -/
abbrev FractionalOrder := Set.Ioo (0 : ℝ) 1

theorem FractionalOrder.pos (s : FractionalOrder) : 0 < s.1 := s.2.1

theorem FractionalOrder.lt_one (s : FractionalOrder) : s.1 < 1 := s.2.2

/-- A Euclidean `L²` vector field on the unit centered cube.  The witness uses
the Euclidean Hilbert realization, so it supplies the explicit `euclideanNorm`
`L²` fact without a finite-real fallback. -/
structure UnitCubeEuclideanL2Field (d : ℕ) where
  /-- The represented vector field. -/
  toField : Vec d → Vec d
  euclideanMemL2 :
    MeasureTheory.MemLp (fun x => HilbertVec.ofVec (toField x)) (2 : ℝ≥0∞)
      (unitCenteredCubeDomain d).normalizedVolume

namespace UnitCubeEuclideanL2Field

instance {d : ℕ} : CoeFun (UnitCubeEuclideanL2Field d) (fun _ => Vec d → Vec d) where
  coe F := F.toField

/-- The explicit Euclidean-magnitude form of the stored `L²` fact. -/
theorem euclideanMagnitudeMemL2 {d : ℕ} (F : UnitCubeEuclideanL2Field d) :
    MeasureTheory.MemLp (fun x => euclideanNorm (F x)) (2 : ℝ≥0∞)
      (unitCenteredCubeDomain d).normalizedVolume := by
  simpa only [euclideanNorm_eq_norm_ofVec] using F.euclideanMemL2.norm

end UnitCubeEuclideanL2Field

end

end Homogenization
