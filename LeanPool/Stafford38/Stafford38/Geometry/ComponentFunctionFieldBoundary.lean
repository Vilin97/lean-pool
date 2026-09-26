/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import LeanPool.Stafford38.AlgebraicAnalysis.FieldTheory.FunctionField
public import LeanPool.Stafford38.Stafford38.Geometry.AffineComponentCoordinateSplit
public import LeanPool.Stafford38.Stafford38.Geometry.ProjectiveValuationNormalization
public import LeanPool.Stafford38.Stafford38.Geometry.RelativeFractionFieldTransport
public import LeanPool.Stafford38.Stafford38.Geometry.RelativeRetainedBoundaryPlace


/-!
# Discrete boundary places for affine components

An affine component function field is finitely generated over the ground
field.  Therefore every transcendental component coordinate admits the
discrete boundary refinement constructed by the relative divisorial tower.
-/

@[expose] public section

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

local instance coordinateDomain (E : Type u) [Field E] :
    IsDomain (CoordinateZeroLocalRing E) := inferInstance

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

private theorem normalized_with_parameter
    {K : Type u} [Field K] (V : ValuationSubring K) (r : V.toSubring)
    (p : Fin (m + 1) → K) (hpzero : p 0 = 1) (i : Fin m)
    (hpi : p i.succ = (r : K)) :
    ∃ (chart : Fin (m + 1)) (q : Fin (m + 1) → V.toSubring) (scale : K),
      scale ≠ 0 ∧ q chart = 1 ∧ q 0 ≠ 0 ∧
      (∀ a, (q a : K) = scale * p a) ∧ q i.succ = q 0 * r := by
  obtain ⟨chart, q, scale, hscale, hchart, hq⟩ :=
    exists_normalized_projective_lift V p ⟨0, by simp [hpzero]⟩
  have hqzero : q 0 ≠ 0 := by
    intro hzero
    apply hscale
    have h := hq 0
    rw [hzero] at h
    simpa [hpzero] using h.symm
  refine ⟨chart, q, scale, hscale, hchart, hqzero, hq, ?_⟩
  apply Subtype.ext
  change (q i.succ : K) = (q 0 : K) * (r : K)
  rw [hq, hq, hpzero, hpi, mul_one]

private theorem normalized_relative_place
    {K : Type u} [Field K] [Algebra k K] (x : K) (W : Data k K x)
    (p : Fin (m + 1) → K) (hpzero : p 0 = 1) (i : Fin m) (hpi : p i.succ = x) :
    letI : Algebra (CoordinateZeroLocalRing W.coefficientField) K := W.ambientAlgebra
    ∃ (chart : Fin (m + 1)) (q : Fin (m + 1) → W.place.valuation.toSubring) (scale : K),
      scale ≠ 0 ∧ q chart = 1 ∧ q 0 ≠ 0 ∧
      (∀ a, (q a : K) = scale * p a) ∧ q i.succ = q 0 * W.place.parameter := by
  let : Algebra (CoordinateZeroLocalRing W.coefficientField) K := W.ambientAlgebra
  exact normalized_with_parameter W.place.valuation W.place.parameter
    p hpzero i (hpi.trans W.parameter_eq_coordinate.symm)

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
  let W := (exists_relativeRetainedBoundaryPlace_componentCoordinate P i hi).some
  refine ⟨W, ?_⟩
  exact normalized_relative_place (componentCoordinate P i) W
    (componentProjectivePoint P) rfl i rfl

/-- A transcendental coordinate on a prime affine component has a genuine
discrete valuation place centred at coordinate zero.  It is the forgetful
image of the retained relative place above. -/
theorem exists_discreteBoundaryRefinement_componentCoordinate
    [CharZero k]
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) (i : Fin m)
    (hi : Transcendental k (componentCoordinate P i)) :
    Nonempty (DiscreteBoundaryRefinement k (componentCoordinate P i)) := by
  let W := (exists_relativeRetainedBoundaryPlace_componentCoordinate P i hi).some
  let : Algebra (CoordinateZeroLocalRing W.coefficientField)
      (FractionRing (MvPolynomial (Fin m) k ⧸ P.asIdeal)) :=
    W.ambientAlgebra
  exact ⟨W.toDiscreteBoundaryRefinement⟩


end


end Stafford38.Geometry.ComponentFunctionFieldBoundary
