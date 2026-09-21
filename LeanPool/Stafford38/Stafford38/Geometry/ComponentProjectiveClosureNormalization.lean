/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.Stafford38.Geometry.ComponentFunctionFieldBoundary
import LeanPool.Stafford38.Stafford38.Geometry.ComponentProjectiveClosure
import LeanPool.Stafford38.Stafford38.Geometry.RetainedProjectiveCompletion
import Mathlib.RingTheory.LaurentSeries

/-!
# Projective-component equations under retained normalization

A homogeneous equation of the generic projective cone continues to vanish
after a common rescaling of all projective coordinates into a subring of the
component function field.  The proof first checks the equality in the function
field and then reflects it through the injective subring map.  Consequently the
equality is preserved by every subsequent ring homomorphism, including the
retained completion and its Laurent-series embedding.

This is only a homogeneous projective statement.  It does not assert that an
arbitrary affine chart point satisfies the original affine component ideal.
-/

namespace Stafford38.Geometry.ComponentProjectiveClosureNormalization

open IsLocalRing
open Stafford38.Geometry.AffineComponentCoordinateSplit
open Stafford38.Geometry.AsymptoticDivisorExistence
open Stafford38.Geometry.ComponentFunctionFieldBoundary
open Stafford38.Geometry.ComponentProjectiveClosure
open Stafford38.Geometry.ProjectiveValuationNormalization
open Stafford38.Geometry.RelativeCoefficientDVR
open Stafford38.Geometry.RelativeRetainedBoundaryPlace
open Stafford38.Geometry.RetainedProjectiveCompletion

noncomputable section


universe u

variable {k : Type u} [Field k] {m : ℕ}

/-- A homogeneous projective-cone equation vanishes after any common-scale
lift through an injective coefficient ring.  The explicit coefficient
compatibility prevents an implicit change of the ground-field embedding. -/
theorem eval₂_eq_zero_of_commonScale_componentProjectivePoint
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    {V : Type u} [CommRing V]
    (coeff : k →+* V) (ι : V →+* ComponentFractionField P)
    (hι : Function.Injective ι)
    (hcoeff : ι.comp coeff = algebraMap k (ComponentFractionField P))
    {H : MvPolynomial (Fin (m + 1)) k} {d : ℕ}
    (hhomogeneous : H.IsHomogeneous d)
    (hH : H ∈ componentProjectiveClosureIdeal P)
    (q : Fin (m + 1) → V) (scale : ComponentFractionField P)
    (hq : ∀ a, ι (q a) = scale * componentProjectivePoint P a) :
    MvPolynomial.eval₂ coeff q H = 0 := by
  have hgeneric :
      MvPolynomial.eval₂ (algebraMap k (ComponentFractionField P))
        (componentProjectivePoint P) H = 0 := by
    have hcone : componentProjectiveConeMap P H = 0 := hH
    have hformula :=
      componentProjectiveConeMap_eq_eval₂_mul_X_pow_of_isHomogeneous
        P hhomogeneous
    rw [hcone] at hformula
    have hone := congrArg (Polynomial.eval 1) hformula
    have hpt : componentProjectivePoint P =
        Fin.cases 1 fun i ↦ componentCoordinate P i := rfl
    simpa [hpt] using hone.symm
  apply hι
  rw [map_zero]
  calc
    ι (MvPolynomial.eval₂ coeff q H) =
        MvPolynomial.eval₂ (ι.comp coeff) (fun a ↦ ι (q a)) H :=
      MvPolynomial.map_eval₂Hom coeff q ι H
    _ = MvPolynomial.eval₂ (algebraMap k (ComponentFractionField P))
        (fun a ↦ componentProjectivePoint P a * scale) H := by
      apply MvPolynomial.eval₂Hom_congr hcoeff
      · funext a
        rw [hq a, mul_comm]
      · rfl
    _ = MvPolynomial.eval₂ (algebraMap k (ComponentFractionField P))
          (componentProjectivePoint P) H * scale ^ d :=
      eval₂_mul_common_of_isHomogeneous hhomogeneous
        (algebraMap k (ComponentFractionField P))
        (componentProjectivePoint P) scale
    _ = 0 := by rw [hgeneric, zero_mul]

/-- Evaluation is natural under every ring homomorphism out of a common-scale
lift: the target coefficient map and every target coordinate are the displayed
composites, and the resulting target-ring evaluation is zero. -/
theorem map_eval₂_eq_zero_of_commonScale_componentProjectivePoint
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    {V S : Type u} [CommRing V] [CommRing S]
    (coeff : k →+* V) (ι : V →+* ComponentFractionField P)
    (hι : Function.Injective ι)
    (hcoeff : ι.comp coeff = algebraMap k (ComponentFractionField P))
    (ψ : V →+* S)
    {H : MvPolynomial (Fin (m + 1)) k} {d : ℕ}
    (hhomogeneous : H.IsHomogeneous d)
    (hH : H ∈ componentProjectiveClosureIdeal P)
    (q : Fin (m + 1) → V) (scale : ComponentFractionField P)
    (hq : ∀ a, ι (q a) = scale * componentProjectivePoint P a) :
    MvPolynomial.eval₂ (ψ.comp coeff) (fun a ↦ ψ (q a)) H = 0 := by
  calc
    MvPolynomial.eval₂ (ψ.comp coeff) (fun a ↦ ψ (q a)) H =
        ψ (MvPolynomial.eval₂ coeff q H) := by
      simpa only [Function.comp_apply, Function.comp_def] using
        (MvPolynomial.eval₂_comp_left ψ coeff q H).symm
    _ = 0 := by
      rw [eval₂_eq_zero_of_commonScale_componentProjectivePoint P coeff ι hι
        hcoeff hhomogeneous hH q scale hq, map_zero]

/-- The coefficient map from the ground field into a retained component
valuation ring. -/
def retainedComponentCoefficientMap
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) (i : Fin m)
    (W : Data k (ComponentFractionField P) (componentCoordinate P i)) :
    letI : Algebra (CoordinateZeroLocalRing W.coefficientField)
        (ComponentFractionField P) := W.ambientAlgebra
    k →+* W.place.valuation.toSubring := by
  letI : Algebra (CoordinateZeroLocalRing W.coefficientField)
      (ComponentFractionField P) := W.ambientAlgebra
  exact (relativeCoefficientMap W.coefficientField W.place).comp
    (algebraMap k W.coefficientField)

/-- Every homogeneous equation of the projective component vanishes on a
common-scale lift in the retained valuation subring. -/
theorem retained_eval₂_eq_zero_of_commonScale
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) (i : Fin m)
    (W : Data k (ComponentFractionField P) (componentCoordinate P i)) :
    letI : Algebra (CoordinateZeroLocalRing W.coefficientField)
        (ComponentFractionField P) := W.ambientAlgebra
    ∀ {H : MvPolynomial (Fin (m + 1)) k} {d : ℕ},
      H.IsHomogeneous d → H ∈ componentProjectiveClosureIdeal P →
      ∀ (q : Fin (m + 1) → W.place.valuation.toSubring)
        (scale : ComponentFractionField P),
        (∀ a, (q a : ComponentFractionField P) =
          scale * componentProjectivePoint P a) →
        MvPolynomial.eval₂ (retainedComponentCoefficientMap P i W) q H = 0 := by
  letI : Algebra (CoordinateZeroLocalRing W.coefficientField)
      (ComponentFractionField P) := W.ambientAlgebra
  letI : IsScalarTower W.coefficientField
      (CoordinateZeroLocalRing W.coefficientField)
      (ComponentFractionField P) := W.coefficientTower
  intro H d hhomogeneous hH q scale hq
  let V := W.place.valuation.toSubring
  let coeff : k →+* V := retainedComponentCoefficientMap P i W
  have hcoeff : W.place.valuation.toSubring.subtype.comp coeff =
      algebraMap k (ComponentFractionField P) := by
    ext c
    change ((relativeCoefficientMap W.coefficientField W.place
      (algebraMap k W.coefficientField c) : V) : ComponentFractionField P) =
        algebraMap k (ComponentFractionField P) c
    calc
      ((relativeCoefficientMap W.coefficientField W.place
          (algebraMap k W.coefficientField c) : V) :
          ComponentFractionField P) =
          algebraMap W.coefficientField (ComponentFractionField P)
            (algebraMap k W.coefficientField c) :=
        DFunLike.congr_fun
          (relativeCoefficientMap_commutes W.coefficientField W.place)
          (algebraMap k W.coefficientField c)
      _ = algebraMap k (ComponentFractionField P) c :=
        IsScalarTower.algebraMap_apply k W.coefficientField
          (ComponentFractionField P) c
  exact eval₂_eq_zero_of_commonScale_componentProjectivePoint
    P coeff W.place.valuation.toSubring.subtype
      Subtype.val_injective hcoeff hhomogeneous hH q scale hq

/-- The explicit ground-field coefficient map in the completed power-series
chart.  No ambient `Algebra k` instance is selected implicitly. -/
def retainedCompletedCoefficientMap
    [CharZero k]
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) (i : Fin m)
    (W : Data k (ComponentFractionField P) (componentCoordinate P i)) :
    letI : Algebra (CoordinateZeroLocalRing W.coefficientField)
        (ComponentFractionField P) := W.ambientAlgebra
    let V := W.place.valuation.toSubring
    letI : IsDiscreteValuationRing V := W.place.isDiscrete
    letI : Algebra W.coefficientField V :=
      (relativeCoefficientMap W.coefficientField W.place).toAlgebra
    k →+* PowerSeries (ResidueField V) := by
  letI : Algebra (CoordinateZeroLocalRing W.coefficientField)
      (ComponentFractionField P) := W.ambientAlgebra
  let V := W.place.valuation.toSubring
  letI : IsDiscreteValuationRing V := W.place.isDiscrete
  letI : Algebra W.coefficientField V :=
    (relativeCoefficientMap W.coefficientField W.place).toAlgebra
  exact (retainedToCompletedPowerSeries W).comp
    (retainedComponentCoefficientMap P i W)

/-- The same equation vanishes when evaluated at the transported completed
coordinates with the explicit transported coefficient map. -/
theorem retainedCompleted_eval₂_eq_zero_of_commonScale
    [CharZero k]
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) (i : Fin m)
    (W : Data k (ComponentFractionField P) (componentCoordinate P i)) :
    letI : Algebra (CoordinateZeroLocalRing W.coefficientField)
        (ComponentFractionField P) := W.ambientAlgebra
    let V := W.place.valuation.toSubring
    letI : IsDiscreteValuationRing V := W.place.isDiscrete
    letI : Algebra W.coefficientField V :=
      (relativeCoefficientMap W.coefficientField W.place).toAlgebra
    ∀ {H : MvPolynomial (Fin (m + 1)) k} {d : ℕ},
      H.IsHomogeneous d → H ∈ componentProjectiveClosureIdeal P →
      ∀ (q : Fin (m + 1) → V) (scale : ComponentFractionField P),
        (∀ a, (q a : ComponentFractionField P) =
          scale * componentProjectivePoint P a) →
        MvPolynomial.eval₂ (retainedCompletedCoefficientMap P i W)
          (fun a ↦ retainedToCompletedPowerSeries W (q a)) H = 0 := by
  letI : Algebra (CoordinateZeroLocalRing W.coefficientField)
      (ComponentFractionField P) := W.ambientAlgebra
  let V := W.place.valuation.toSubring
  letI : IsDiscreteValuationRing V := W.place.isDiscrete
  letI : Algebra W.coefficientField V :=
    (relativeCoefficientMap W.coefficientField W.place).toAlgebra
  dsimp only
  intro H d hhomogeneous hH q scale hq
  change MvPolynomial.eval₂
      ((retainedToCompletedPowerSeries W).comp
        (retainedComponentCoefficientMap P i W))
      (fun a ↦ retainedToCompletedPowerSeries W (q a)) H = 0
  calc
    _ = retainedToCompletedPowerSeries W
        (MvPolynomial.eval₂ (retainedComponentCoefficientMap P i W) q H) := by
      simpa only [Function.comp_apply, Function.comp_def] using
        (MvPolynomial.eval₂_comp_left (retainedToCompletedPowerSeries W)
          (retainedComponentCoefficientMap P i W) q H).symm
    _ = 0 := by
      rw [retained_eval₂_eq_zero_of_commonScale P i W
        hhomogeneous hH q scale hq, map_zero]

/-- The explicit ground-field coefficient map after the retained completion
and canonical Laurent-series embedding. -/
def retainedLaurentCoefficientMap
    [CharZero k]
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) (i : Fin m)
    (W : Data k (ComponentFractionField P) (componentCoordinate P i)) :
    letI : Algebra (CoordinateZeroLocalRing W.coefficientField)
        (ComponentFractionField P) := W.ambientAlgebra
    let V := W.place.valuation.toSubring
    letI : IsDiscreteValuationRing V := W.place.isDiscrete
    letI : Algebra W.coefficientField V :=
      (relativeCoefficientMap W.coefficientField W.place).toAlgebra
    k →+* LaurentSeries (ResidueField V) := by
  letI : Algebra (CoordinateZeroLocalRing W.coefficientField)
      (ComponentFractionField P) := W.ambientAlgebra
  let V := W.place.valuation.toSubring
  letI : IsDiscreteValuationRing V := W.place.isDiscrete
  letI : Algebra W.coefficientField V :=
    (relativeCoefficientMap W.coefficientField W.place).toAlgebra
  exact (algebraMap (PowerSeries (ResidueField V))
      (LaurentSeries (ResidueField V))).comp
    (retainedCompletedCoefficientMap P i W)

/-- The completed equation remains zero when evaluated at the corresponding
Laurent coordinates. -/
theorem retainedLaurent_eval₂_eq_zero_of_commonScale
    [CharZero k]
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) (i : Fin m)
    (W : Data k (ComponentFractionField P) (componentCoordinate P i)) :
    letI : Algebra (CoordinateZeroLocalRing W.coefficientField)
        (ComponentFractionField P) := W.ambientAlgebra
    let V := W.place.valuation.toSubring
    letI : IsDiscreteValuationRing V := W.place.isDiscrete
    letI : Algebra W.coefficientField V :=
      (relativeCoefficientMap W.coefficientField W.place).toAlgebra
    ∀ {H : MvPolynomial (Fin (m + 1)) k} {d : ℕ},
      H.IsHomogeneous d → H ∈ componentProjectiveClosureIdeal P →
      ∀ (q : Fin (m + 1) → V) (scale : ComponentFractionField P),
        (∀ a, (q a : ComponentFractionField P) =
          scale * componentProjectivePoint P a) →
        MvPolynomial.eval₂ (retainedLaurentCoefficientMap P i W)
          (fun a ↦ algebraMap (PowerSeries (ResidueField V))
            (LaurentSeries (ResidueField V))
              (retainedToCompletedPowerSeries W (q a))) H = 0 := by
  letI : Algebra (CoordinateZeroLocalRing W.coefficientField)
      (ComponentFractionField P) := W.ambientAlgebra
  let V := W.place.valuation.toSubring
  letI : IsDiscreteValuationRing V := W.place.isDiscrete
  letI : Algebra W.coefficientField V :=
    (relativeCoefficientMap W.coefficientField W.place).toAlgebra
  dsimp only
  intro H d hhomogeneous hH q scale hq
  let ψ : PowerSeries (ResidueField V) →+* LaurentSeries (ResidueField V) :=
    algebraMap (PowerSeries (ResidueField V)) (LaurentSeries (ResidueField V))
  change MvPolynomial.eval₂
      (ψ.comp (retainedCompletedCoefficientMap P i W))
      (fun a ↦ ψ (retainedToCompletedPowerSeries W (q a))) H = 0
  calc
    _ = ψ (MvPolynomial.eval₂ (retainedCompletedCoefficientMap P i W)
        (fun a ↦ retainedToCompletedPowerSeries W (q a)) H) := by
      simpa only [Function.comp_apply, Function.comp_def] using
        (MvPolynomial.eval₂_comp_left ψ
          (retainedCompletedCoefficientMap P i W)
          (fun a ↦ retainedToCompletedPowerSeries W (q a)) H).symm
    _ = 0 := by
      rw [retainedCompleted_eval₂_eq_zero_of_commonScale P i W
        hhomogeneous hH q scale hq, map_zero]


end

end Stafford38.Geometry.ComponentProjectiveClosureNormalization
