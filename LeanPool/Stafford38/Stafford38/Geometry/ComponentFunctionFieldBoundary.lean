/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.AlgebraicAnalysis.FieldTheory.FunctionField
import LeanPool.Stafford38.Stafford38.Geometry.AffineComponentCoordinateSplit
import LeanPool.Stafford38.Stafford38.Geometry.ProjectiveValuationNormalization
import LeanPool.Stafford38.Stafford38.Geometry.RelativeFractionFieldTransport
import LeanPool.Stafford38.Stafford38.Geometry.RelativeRetainedBoundaryPlace

/-!
# Discrete boundary places for affine components

An affine component function field is finitely generated over the ground
field.  Therefore every transcendental component coordinate admits the
discrete boundary refinement constructed by the relative divisorial tower.
-/

namespace Stafford38.Geometry.ComponentFunctionFieldBoundary

open IsLocalRing
open AlgebraicAnalysis.FunctionField
open Stafford38.Geometry.AffineComponentCoordinateSplit
open Stafford38.Geometry.AsymptoticDivisorExistence
open Stafford38.Geometry.ProjectiveValuationNormalization
open Stafford38.Geometry.RelativeFractionFieldTransport
open Stafford38.Geometry.RelativeCoefficientDVR
open Stafford38.Geometry.RelativeRetainedBoundaryPlace

noncomputable section


universe u

variable {k : Type u} [Field k] {m : ℕ}

/-- The function field of a prime affine component is finitely generated as a
field extension of the ground field. -/
theorem componentFunctionField_fg
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) :
    (⊤ : IntermediateField k
      (FractionRing (MvPolynomial (Fin m) k ⧸ P.asIdeal))).FG := by
  exact top_fg_of_finiteType_fractionRing k
    (MvPolynomial (Fin m) k ⧸ P.asIdeal)
    (FractionRing (MvPolynomial (Fin m) k ⧸ P.asIdeal))

/-- The affine component point in homogeneous coordinates. -/
def componentProjectivePoint
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) :
    Fin (m + 1) → FractionRing (MvPolynomial (Fin m) k ⧸ P.asIdeal) :=
  Fin.cases 1 fun i ↦ componentCoordinate P i

/-- The stronger retained form preserves the actual coordinate-local algebra
map required by the completed-DVR machinery. -/
theorem exists_relativeRetainedBoundaryPlace_componentCoordinate
    [CharZero k]
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) (i : Fin m)
    (hi : Transcendental k (componentCoordinate P i)) :
    Nonempty
      (Data k (FractionRing (MvPolynomial (Fin m) k ⧸ P.asIdeal))
        (componentCoordinate P i)) := by
  exact exists_data_of_fg_charZero k (componentFunctionField_fg P)
    (componentCoordinate P i) hi

/-- The complete affine coordinate family can be scaled into the retained
valuation ring with one projective coordinate equal to one. The selected
coordinate remains the retained parameter times the homogeneous zeroth
coordinate. -/
theorem exists_normalizedProjectivePoint_relativeRetainedBoundaryPlace
    [CharZero k]
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) (i : Fin m)
    (hi : Transcendental k (componentCoordinate P i)) :
    ∃ W : Data k (FractionRing (MvPolynomial (Fin m) k ⧸ P.asIdeal))
        (componentCoordinate P i),
      letI : Algebra (CoordinateZeroLocalRing W.coefficientField)
          (FractionRing (MvPolynomial (Fin m) k ⧸ P.asIdeal)) :=
        W.ambientAlgebra
      ∃ (chart : Fin (m + 1))
        (q : Fin (m + 1) → W.place.valuation.toSubring)
        (scale : FractionRing (MvPolynomial (Fin m) k ⧸ P.asIdeal)),
        scale ≠ 0 ∧ q chart = 1 ∧ q 0 ≠ 0 ∧
        (∀ a, (q a : FractionRing
            (MvPolynomial (Fin m) k ⧸ P.asIdeal)) =
          scale * componentProjectivePoint P a) ∧
        q (Fin.succ i) = q 0 * W.place.parameter := by
  obtain ⟨W⟩ :=
    exists_relativeRetainedBoundaryPlace_componentCoordinate P i hi
  letI : Algebra (CoordinateZeroLocalRing W.coefficientField)
      (FractionRing (MvPolynomial (Fin m) k ⧸ P.asIdeal)) :=
    W.ambientAlgebra
  obtain ⟨chart, q, scale, hscale, hchart, hq⟩ :=
    exists_normalized_projective_lift W.place.valuation
      (componentProjectivePoint P) ⟨0, by simp [componentProjectivePoint]⟩
  have hqzero : q 0 ≠ 0 := by
    intro hzero
    apply hscale
    have h := hq 0
    rw [hzero] at h
    simpa [componentProjectivePoint] using h.symm
  refine ⟨W, chart, q, scale, hscale, hchart, hqzero, hq, ?_⟩
  apply Subtype.ext
  change (q (Fin.succ i) : FractionRing
      (MvPolynomial (Fin m) k ⧸ P.asIdeal)) =
    (q 0 : FractionRing (MvPolynomial (Fin m) k ⧸ P.asIdeal)) *
      (W.place.parameter : FractionRing
        (MvPolynomial (Fin m) k ⧸ P.asIdeal))
  rw [hq, hq, W.parameter_eq_coordinate]
  simp [componentProjectivePoint]

/-- A transcendental coordinate on a prime affine component has a genuine
discrete valuation place centred at coordinate zero.  It is the forgetful
image of the retained relative place above. -/
theorem exists_discreteBoundaryRefinement_componentCoordinate
    [CharZero k]
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) (i : Fin m)
    (hi : Transcendental k (componentCoordinate P i)) :
    Nonempty (DiscreteBoundaryRefinement k (componentCoordinate P i)) := by
  obtain ⟨W⟩ :=
    exists_relativeRetainedBoundaryPlace_componentCoordinate P i hi
  letI : Algebra (CoordinateZeroLocalRing W.coefficientField)
      (FractionRing (MvPolynomial (Fin m) k ⧸ P.asIdeal)) :=
    W.ambientAlgebra
  exact ⟨W.toDiscreteBoundaryRefinement⟩


end


end Stafford38.Geometry.ComponentFunctionFieldBoundary
