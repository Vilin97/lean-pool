/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.Stafford38.Geometry.ComponentProjectiveClosureNormalization
import LeanPool.Stafford38.Stafford38.Geometry.LaurentConormalResidueExtension
import LeanPool.Stafford38.Stafford38.Geometry.RetainedComponentEquationPackage

/-!
# Ground coefficients in the retained completed chart

The retained DVR construction carries a canonical ground-field map into its
residue field.  With that map chosen as the `Algebra` structure, the explicit
coefficient map obtained by passing through the valuation ring, its completion,
and Laurent series is exactly the ground map used by the terminal geometric
consumer.

The choice of `Algebra` structure is part of the statement.  No equality with
an unrelated ground-field embedding of the residue field is asserted.
-/

namespace Stafford38.Geometry.RetainedGroundMapIdentification

open IsLocalRing
open Stafford38.Geometry.AffineComponentCoordinateSplit
open Stafford38.Geometry.AsymptoticDivisorExistence
open Stafford38.Geometry.ComponentFunctionFieldBoundary
open Stafford38.Geometry.ComponentProjectiveClosure
open Stafford38.Geometry.ComponentProjectiveClosureNormalization
open Stafford38.Geometry.CompletedDVRCoefficientSection
open Stafford38.Geometry.CompletedDVRPowerSeries
open Stafford38.Geometry.LaurentConormalResidueExtension
open Stafford38.Geometry.RelativeCoefficientDVR
open Stafford38.Geometry.RelativeRetainedBoundaryPlace
open Stafford38.Geometry.RetainedComponentEquationPackage
open Stafford38.Geometry.RetainedProjectiveCompletion

noncomputable section


universe u

variable {k : Type u} [Field k] {m : ℕ}

/-- The ground-field structure on the retained residue field induced by the
actual coefficient map through the valuation ring. -/
def retainedResidueGroundAlgebra
    [CharZero k]
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) (i : Fin m)
    (W : Data k (ComponentFractionField P) (componentCoordinate P i)) :
    letI : Algebra (CoordinateZeroLocalRing W.coefficientField)
        (ComponentFractionField P) := W.ambientAlgebra
    let V := W.place.valuation.toSubring
    letI : IsDiscreteValuationRing V := W.place.isDiscrete
    letI : Algebra W.coefficientField V :=
      (relativeCoefficientMap W.coefficientField W.place).toAlgebra
    Algebra k (ResidueField V) := by
  letI : Algebra (CoordinateZeroLocalRing W.coefficientField)
      (ComponentFractionField P) := W.ambientAlgebra
  let V := W.place.valuation.toSubring
  letI : IsDiscreteValuationRing V := W.place.isDiscrete
  letI : Algebra W.coefficientField V :=
    (relativeCoefficientMap W.coefficientField W.place).toAlgebra
  exact ((residue V).comp (retainedComponentCoefficientMap P i W)).toAlgebra

private theorem completedDVRPowerSeriesMap_ground
    (E V : Type u) [Field E] [CommRing V] [IsDomain V] [IsLocalRing V]
    [IsDiscreteValuationRing V] [Algebra E V]
    (hsep : Algebra.IsSeparable E (ResidueField V)) (c : E) :
    algebraMap V (AdicCompletion (maximalIdeal V) V) (algebraMap E V c) =
      completedDVRPowerSeriesMap E V hsep
        (PowerSeries.C (algebraMap E (ResidueField V) c)) := by
  rw [completedDVRPowerSeriesMap_C]
  exact (IsScalarTower.algebraMap_apply E V (AdicCompletion (maximalIdeal V) V) c).trans
    ((completedCoefficientSection E V hsep).commutes c).symm

/-- Ground coefficients transported through the retained valuation ring become
the corresponding constant power series for the induced residue-field map. -/
theorem retainedToCompletedPowerSeries_ground
    [CharZero k]
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) (i : Fin m)
    (W : Data k (ComponentFractionField P) (componentCoordinate P i)) :
    letI : Algebra (CoordinateZeroLocalRing W.coefficientField)
        (ComponentFractionField P) := W.ambientAlgebra
    let V := W.place.valuation.toSubring
    letI : IsDiscreteValuationRing V := W.place.isDiscrete
    letI : Algebra W.coefficientField V :=
      (relativeCoefficientMap W.coefficientField W.place).toAlgebra
    letI : Algebra k (ResidueField V) :=
      retainedResidueGroundAlgebra P i W
    ∀ c : k,
      retainedToCompletedPowerSeries W
          (retainedComponentCoefficientMap P i W c) =
        PowerSeries.C (R := ResidueField V)
          (algebraMap k (ResidueField V) c) := by
  let : Algebra (CoordinateZeroLocalRing W.coefficientField)
      (ComponentFractionField P) := W.ambientAlgebra
  let V := W.place.valuation.toSubring
  let : IsDiscreteValuationRing V := W.place.isDiscrete
  let : Algebra W.coefficientField V :=
    (relativeCoefficientMap W.coefficientField W.place).toAlgebra
  let : Algebra k (ResidueField V) :=
    retainedResidueGroundAlgebra P i W
  dsimp only
  intro c
  change W.completedPowerSeriesEquiv.symm
      (algebraMap V (AdicCompletion (maximalIdeal V) V)
        (relativeCoefficientMap W.coefficientField W.place
          (algebraMap k W.coefficientField c))) = _
  apply W.completedPowerSeriesEquiv.toEquiv.symm_apply_eq.mpr
  change algebraMap V (AdicCompletion (maximalIdeal V) V)
      (relativeCoefficientMap W.coefficientField W.place
        (algebraMap k W.coefficientField c)) =
    completedDVRPowerSeriesMap W.coefficientField V
        (relativeResidue_isSeparable W.coefficientField W.place)
      (PowerSeries.C (R := ResidueField V)
        (residue V
          (relativeCoefficientMap W.coefficientField W.place
            (algebraMap k W.coefficientField c))))
  have h := completedDVRPowerSeriesMap_ground W.coefficientField V
    (relativeResidue_isSeparable W.coefficientField W.place) (algebraMap k W.coefficientField c)
  exact h

/-- With the residue-induced `Algebra` structure, the explicit retained
Laurent coefficient map is definitionally the terminal consumer's ground map. -/
theorem retainedLaurentCoefficientMap_eq_groundLaurentMap
    [CharZero k]
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) (i : Fin m)
    (W : Data k (ComponentFractionField P) (componentCoordinate P i)) :
    letI : Algebra (CoordinateZeroLocalRing W.coefficientField)
        (ComponentFractionField P) := W.ambientAlgebra
    let V := W.place.valuation.toSubring
    letI : IsDiscreteValuationRing V := W.place.isDiscrete
    letI : Algebra W.coefficientField V :=
      (relativeCoefficientMap W.coefficientField W.place).toAlgebra
    letI : Algebra k (ResidueField V) :=
      retainedResidueGroundAlgebra P i W
    retainedLaurentCoefficientMap P i W =
      groundLaurentMap (k := k) (K := ResidueField V) := by
  let : Algebra (CoordinateZeroLocalRing W.coefficientField)
      (ComponentFractionField P) := W.ambientAlgebra
  let V := W.place.valuation.toSubring
  let : IsDiscreteValuationRing V := W.place.isDiscrete
  let : Algebra W.coefficientField V :=
    (relativeCoefficientMap W.coefficientField W.place).toAlgebra
  let : Algebra k (ResidueField V) :=
    retainedResidueGroundAlgebra P i W
  apply RingHom.ext
  intro c
  change algebraMap (PowerSeries (ResidueField V))
      (LaurentSeries (ResidueField V))
      (retainedToCompletedPowerSeries W
        (retainedComponentCoefficientMap P i W c)) =
    algebraMap (ResidueField V) (LaurentSeries (ResidueField V))
      (algebraMap k (ResidueField V) c)
  rw [retainedToCompletedPowerSeries_ground P i W]
  rfl

/-- The finite retained equation package therefore has exactly the coefficient
map required by the terminal residue-extension chart consumer. -/
theorem retainedComponentGroundEquationPackage
    [CharZero k]
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (I : Ideal (MvPolynomial (Fin m) k)) (hIP : I ≤ P.asIdeal)
    (i : Fin m)
    (W : Data k (ComponentFractionField P) (componentCoordinate P i)) :
    letI : Algebra (CoordinateZeroLocalRing W.coefficientField)
        (ComponentFractionField P) := W.ambientAlgebra
    let V := W.place.valuation.toSubring
    letI : IsDiscreteValuationRing V := W.place.isDiscrete
    letI : Algebra W.coefficientField V :=
      (relativeCoefficientMap W.coefficientField W.place).toAlgebra
    letI : Algebra k (ResidueField V) :=
      retainedResidueGroundAlgebra P i W
    ∀ (q : Fin (m + 1) → V) (scale : ComponentFractionField P),
      (∀ a, (q a : ComponentFractionField P) =
        scale * componentProjectivePoint P a) →
      Nonempty (EquationPackage I
        (groundLaurentMap (k := k) (K := ResidueField V))
        (fun a ↦ algebraMap (PowerSeries (ResidueField V))
          (LaurentSeries (ResidueField V))
            (retainedToCompletedPowerSeries W (q a)))) := by
  let : Algebra (CoordinateZeroLocalRing W.coefficientField)
      (ComponentFractionField P) := W.ambientAlgebra
  let V := W.place.valuation.toSubring
  let : IsDiscreteValuationRing V := W.place.isDiscrete
  let : Algebra W.coefficientField V :=
    (relativeCoefficientMap W.coefficientField W.place).toAlgebra
  let : Algebra k (ResidueField V) :=
    retainedResidueGroundAlgebra P i W
  dsimp only
  intro q scale hq
  simpa only [retainedLaurentCoefficientMap_eq_groundLaurentMap P i W] using
    (retainedComponentEquationPackage P I hIP i W q scale hq)


end

end Stafford38.Geometry.RetainedGroundMapIdentification
