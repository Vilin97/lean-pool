/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.Stafford38.Geometry.CompletedDVRPowerSeriesEquiv

/-!
# Relative retained boundary places

The divisorial construction for a transcendental element can retain the
actual local map from the coordinate DVR `E[X]_(X)`.  This is stronger than
the bare `DiscreteBoundaryRefinement`: it preserves the coefficient field and
the algebra structure needed by the completed-DVR coefficient section.

No projective normalization, completed projective coordinates, or tangent
frame is constructed here.
-/

namespace Stafford38.Geometry.RelativeRetainedBoundaryPlace

open IsLocalRing
open Stafford38.Geometry.AsymptoticDivisorExistence
open Stafford38.Geometry.CompletedDVRPowerSeries
open Stafford38.Geometry.RelativeCoefficientDVR
open Stafford38.Geometry.RelativeDivisorialTower
open Stafford38.Geometry.RelativeFractionFieldTransport
open Stafford38.Geometry.RetainedDVR

noncomputable section


universe u


private abbrev SourceDVR (E : Type u) [Field E] :=
  CoordinateZeroLocalRing E

/-- A retained boundary place for `x`, including the relative coefficient
field and the exact ambient algebra structure under which the local
coordinate maps to `x`. -/
structure Data
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    (x : K) where
  /-- The coefficient subfield over which the selected coordinate is transcendental. -/
  coefficientField : IntermediateField k K
  coordinate_transcendental : Transcendental coefficientField x
  /-- The source DVR action on the ambient function field. -/
  ambientAlgebra : Algebra (SourceDVR coefficientField) K
  coefficientTower :
    letI : Algebra (SourceDVR coefficientField) K := ambientAlgebra
    IsScalarTower coefficientField (SourceDVR coefficientField) K
  coordinate_eq :
    letI : Algebra (SourceDVR coefficientField) K := ambientAlgebra
    algebraMap (SourceDVR coefficientField) K
        (algebraMap (Polynomial coefficientField)
          (SourceDVR coefficientField) Polynomial.X) = x
  /-- A retained DVR place identifying its parameter with the selected coordinate. -/
  place :
    letI : Algebra (SourceDVR coefficientField) K := ambientAlgebra
    RetainedDVRPlace (SourceDVR coefficientField) (L := K)
      (algebraMap (Polynomial coefficientField)
        (SourceDVR coefficientField) Polynomial.X)

/-- The retained parameter is the selected function-field coordinate. -/
theorem Data.parameter_eq_coordinate
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    {x : K} (W : Data k K x) :
    letI : Algebra (SourceDVR W.coefficientField) K := W.ambientAlgebra
    (W.place.parameter : K) = x := by
  let : Algebra (SourceDVR W.coefficientField) K := W.ambientAlgebra
  exact W.place.parameter_eq.trans W.coordinate_eq

/-- Forgetting the retained source map recovers the earlier discrete boundary
refinement, with the same valuation ring and parameter. -/
def Data.toDiscreteBoundaryRefinement
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    {x : K} (W : Data k K x) :
    letI : Algebra (SourceDVR W.coefficientField) K := W.ambientAlgebra
    DiscreteBoundaryRefinement k x := by
  letI : Algebra (SourceDVR W.coefficientField) K := W.ambientAlgebra
  exact {
    valuation := W.place.valuation
    isDiscrete := W.place.isDiscrete
    coordinate := W.place.parameter
    coordinate_eq := W.parameter_eq_coordinate
    coordinate_ne := W.place.parameter_ne
    coordinate_nonunit := W.place.parameter_nonunit
  }

/-- The completion of the retained component DVR is literally a power-series
ring over its residue field.  This is the completion, not the original DVR. -/
def Data.completedPowerSeriesEquiv
    {k K : Type u} [Field k] [CharZero k]
    [Field K] [Algebra k K]
    {x : K} (W : Data k K x) :
    letI : Algebra (SourceDVR W.coefficientField) K := W.ambientAlgebra
    let V := W.place.valuation.toSubring
    letI : IsDiscreteValuationRing V := W.place.isDiscrete
    letI : Algebra W.coefficientField V :=
      (relativeCoefficientMap W.coefficientField W.place).toAlgebra
    PowerSeries (ResidueField V) ≃+*
      AdicCompletion (IsLocalRing.maximalIdeal V) V := by
  letI : Algebra (SourceDVR W.coefficientField) K := W.ambientAlgebra
  let V := W.place.valuation.toSubring
  letI : IsDiscreteValuationRing V := W.place.isDiscrete
  letI : Algebra W.coefficientField V :=
    (relativeCoefficientMap W.coefficientField W.place).toAlgebra
  exact completedDVRPowerSeriesEquivOfSurjective W.coefficientField
    V
    (relativeResidue_isSeparable W.coefficientField W.place)
    (completedDVRPowerSeriesMap_surjective W.coefficientField
      V
      (relativeResidue_isSeparable W.coefficientField W.place))

private theorem exists_retained_over_adjoin
    (E : Type u) [Field E] {K : Type u} [Field K] [Algebra E K]
    (x : K) (hxE : Transcendental E x)
    (hfin : FiniteDimensional (IntermediateField.adjoin E ({x} : Set K)) K)
    (hsep : Algebra.IsSeparable (IntermediateField.adjoin E ({x} : Set K)) K) :
    ∃ algRK : Algebra (SourceDVR E) K,
      letI : Algebra (SourceDVR E) K := algRK
      IsScalarTower E (SourceDVR E) K ∧
      algebraMap (SourceDVR E) K
        (algebraMap (Polynomial E) (SourceDVR E) Polynomial.X) = x ∧
      Nonempty (RetainedDVRPlace (SourceDVR E) (L := K)
        (algebraMap (Polynomial E) (SourceDVR E) Polynomial.X)) := by
  let R := SourceDVR E
  let L := FractionRing R
  let F := IntermediateField.adjoin E ({x} : Set K)
  let e : L ≃ₐ[E] F := coordinateLocalFractionEquivAdjoin E x hxE
  let : SMul E L := Algebra.toSMul
  let : IsScalarTower E R L :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let algRF : Algebra R F :=
    (e.toRingEquiv.toRingHom.comp (algebraMap R L)).toAlgebra
  let : Algebra R F := algRF
  let towerERF : IsScalarTower E R F :=
    IsScalarTower.of_algebraMap_eq fun a => by
      change algebraMap E F a = e (algebraMap R L (algebraMap E R a))
      rw [← IsScalarTower.algebraMap_apply E R L]
      exact (e.commutes a).symm
  let : IsScalarTower E R F := towerERF
  let eR : L ≃ₐ[R] F :=
    { e.toRingEquiv with
      commutes' := fun _ => rfl }
  let : IsFractionRing R F :=
    IsLocalization.isLocalization_of_algEquiv (nonZeroDivisors R) eR
  let algRK : Algebra R K :=
    ((algebraMap F K).comp (algebraMap R F)).toAlgebra
  let : Algebra R K := algRK
  let coefficientTower : IsScalarTower E R K :=
    IsScalarTower.of_algebraMap_eq fun a => by
      change algebraMap E K a =
        algebraMap F K (algebraMap R F (algebraMap E R a))
      rw [← IsScalarTower.algebraMap_apply E R F]
      exact IsScalarTower.algebraMap_apply E F K a
  let : IsScalarTower E R K := coefficientTower
  let : IsScalarTower R F K :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : FiniteDimensional F K := hfin
  let : Algebra.IsSeparable F K := hsep
  let q : R := algebraMap (Polynomial E) R Polynomial.X
  have hq_ne : q ≠ 0 := by
    intro hq
    apply Polynomial.X_ne_zero (R := E)
    apply IsLocalization.injective R
      (coordinateZeroPrime E).primeCompl_le_nonZeroDivisors
    simpa only [q, map_zero] using hq
  have hq_nonunit : ¬IsUnit q := by
    rw [← mem_nonunits_iff, ← mem_maximalIdeal]
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff
      R (coordinateZeroPrime E) Polynomial.X).2
        (Ideal.mem_span_singleton_self Polynomial.X)
  have hcoordinate : algebraMap R K q = x := by
    change (((e (algebraMap R L q) : F) : K)) = x
    exact coordinateLocalFractionEquivAdjoin_X E x hxE
  obtain ⟨D⟩ :=
    exists_retainedDVRPlace (A := R) (F := F) (L := K)
      q hq_ne hq_nonunit
  exact ⟨algRK, coefficientTower, hcoordinate, ⟨D⟩⟩


/-- A finitely generated characteristic-zero function field and a selected
transcendental element admit a retained relative boundary place. -/
theorem exists_data_of_fg_charZero
    (k : Type u) [Field k] [CharZero k]
    {K : Type u} [Field K] [Algebra k K]
    (hfg : (⊤ : IntermediateField k K).FG)
    (x : K) (hx : Transcendental k x) :
    Nonempty (Data k K x) := by
  obtain ⟨s, E, F, hxs, hs, hE, hF, hrestrict, hxE, hxF,
      hfin, hsep⟩ :=
    exists_relative_finite_separable_tower_of_charZero k hfg x hx
  subst F
  obtain ⟨algRK, tower, coordinate, D⟩ := exists_retained_over_adjoin E x hxE hfin hsep
  exact ⟨{
    coefficientField := E
    coordinate_transcendental := hxE
    ambientAlgebra := algRK
    coefficientTower := tower
    coordinate_eq := coordinate
    place := D.some
  }⟩



end

end Stafford38.Geometry.RelativeRetainedBoundaryPlace
