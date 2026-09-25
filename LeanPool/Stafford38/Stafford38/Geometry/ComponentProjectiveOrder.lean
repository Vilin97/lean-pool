/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import LeanPool.Stafford38.Stafford38.Characteristic.CanonicalBaseVariety
public import LeanPool.Stafford38.Stafford38.Geometry.ComponentFunctionFieldBoundary
public import LeanPool.Stafford38.Stafford38.Geometry.RetainedProjectiveCompletion
public import Mathlib.RingTheory.Nullstellensatz


/-!
# Vanishing of the normalized projective denominator

Axis avoidance makes the distinguished affine coordinate a unit on every
component of the reduced base variety.  At the retained boundary place that
coordinate is a nonunit.  Consequently, a common projective normalization of
all affine coordinates cannot have unit homogeneous denominator.
-/

@[expose] public section

namespace Stafford38.Geometry.ComponentProjectiveOrder

open IsLocalRing
open Stafford38
open Stafford38.Characteristic
open Stafford38.Characteristic.CanonicalBaseVariety
open Stafford38.Characteristic.ReducedSupportIdeal
open Stafford38.CharacteristicInitialIdeal
open Stafford38.EulerSurjectivity
open Stafford38.Geometry.AffineComponentCoordinateSplit
open Stafford38.Geometry.AsymptoticDivisorExistence
open Stafford38.Geometry.ComponentFunctionFieldBoundary
open Stafford38.Geometry.ProjectiveValuationNormalization
open Stafford38.Geometry.RelativeCoefficientDVR
open Stafford38.Geometry.RelativeRetainedBoundaryPlace
open Stafford38.Geometry.RetainedProjectiveCompletion
open Stafford38.WeylIteratedEquivalence

noncomputable section


universe u v

/-- Support avoidance forces the contracted reduced base ideal and the
distinguished coordinate to generate the unit ideal. -/
theorem reducedOrderBaseIdeal_sup_coordinate_eq_top_of_support_disjoint
    {k : Type u} [Field k] [IsAlgClosed k] {n : ℕ}
    (I : RightIdeal (PresentedWeyl k n)) (i : Fin n)
    (hdisjoint : Disjoint
      (orderCharacteristicSupport k I)
      (PrimeSpectrum.zeroLocus
        ({MvPolynomial.X (.inl i)} : Set (SymbolRing k n)))) :
    reducedOrderBaseIdeal k I ⊔
        Ideal.span ({MvPolynomial.X i} : Set (MvPolynomial (Fin n) k)) = ⊤ := by
  classical
  let B := reducedOrderBaseIdeal k I
  let J := B ⊔ Ideal.span
    ({MvPolynomial.X i} : Set (MvPolynomial (Fin n) k))
  by_contra hJ
  obtain ⟨M, hMmax, hJM⟩ := Ideal.exists_le_maximal J hJ
  obtain ⟨y, hMy⟩ :=
    MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton.mp hMmax
  have hyB : ∀ f ∈ B, MvPolynomial.eval y f = 0 := by
    intro f hf
    have hfM : f ∈ M := hJM (Ideal.mem_sup_left hf)
    rw [hMy, MvPolynomial.mem_vanishingIdeal_singleton_iff] at hfM
    exact hfM
  have hyi : y i = 0 := by
    have hXM : MvPolynomial.X i ∈ M := by
      apply hJM
      exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
    rw [hMy, MvPolynomial.mem_vanishingIdeal_singleton_iff] at hXM
    simpa using hXM
  exact (coordinate_ne_zero_of_baseZero_of_support_disjoint
    I i hdisjoint y hyB) hyi

/-- On every component above the contracted base ideal, axis avoidance gives
an explicit polynomial inverse for the distinguished coordinate. -/
theorem exists_componentCoordinate_polynomial_inverse
    {k : Type u} [Field k] [IsAlgClosed k] {n : ℕ}
    (I : RightIdeal (PresentedWeyl k n)) (i : Fin n)
    (hdisjoint : Disjoint
      (orderCharacteristicSupport k I)
      (PrimeSpectrum.zeroLocus
        ({MvPolynomial.X (.inl i)} : Set (SymbolRing k n))))
    (P : PrimeSpectrum (MvPolynomial (Fin n) k))
    (hBP : reducedOrderBaseIdeal k I ≤ P.asIdeal) :
    ∃ g : MvPolynomial (Fin n) k,
      MvPolynomial.X i * g - 1 ∈ P.asIdeal := by
  classical
  let B := reducedOrderBaseIdeal k I
  have htop := reducedOrderBaseIdeal_sup_coordinate_eq_top_of_support_disjoint
    I i hdisjoint
  have hone : (1 : MvPolynomial (Fin n) k) ∈
      B ⊔ Ideal.span ({MvPolynomial.X i} : Set (MvPolynomial (Fin n) k)) := by
    rw [htop]
    exact Submodule.mem_top
  obtain ⟨b, hb, z, hz, hbz⟩ := Submodule.mem_sup.mp hone
  obtain ⟨g, hg⟩ := Ideal.mem_span_singleton.mp hz
  refine ⟨g, ?_⟩
  have hbP : b ∈ P.asIdeal := hBP hb
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  rw [map_sub, map_mul, map_one]
  have hsum := congrArg (Ideal.Quotient.mk P.asIdeal) hbz
  rw [map_add, map_one, Ideal.Quotient.eq_zero_iff_mem.mpr hbP] at hsum
  have hzq : Ideal.Quotient.mk P.asIdeal z =
      Ideal.Quotient.mk P.asIdeal (MvPolynomial.X i * g) := by
    rw [hg]
  rw [← map_mul, ← hzq]
  apply sub_eq_zero.mpr
  simpa using hsum

/-- If a nonunit parameter has a polynomial inverse in affine coordinates,
then the common denominator of an integral projective normalization of those
coordinates is a nonunit. -/
theorem normalized_denominator_nonunit_of_polynomial_inverse
    {k : Type u} [Field k] {K : Type v} [Field K] [Algebra k K]
    (V : ValuationSubring K) {n : ℕ}
    (coeff : k →+* V)
    (hcoeff : V.toSubring.subtype.comp coeff = algebraMap k K)
    (x : Fin n → K) (qzero : V) (q : Fin n → V) (scale : K)
    (hqzero : (qzero : K) = scale)
    (hq : ∀ j, (q j : K) = scale * x j)
    (i : Fin n) (parameter : V)
    (hparameter : (parameter : K) = x i)
    (hparameter_nonunit : ¬IsUnit parameter)
    (g : MvPolynomial (Fin n) k)
    (hinverse : x i * MvPolynomial.eval₂ (algebraMap k K) x g = 1) :
    ¬IsUnit qzero := by
  intro hqzero_unit
  obtain ⟨u, hu⟩ := hqzero_unit
  let xV : Fin n → V := fun j ↦ q j * (↑(u⁻¹) : V)
  have hxV : ∀ j, (xV j : K) = x j := by
    intro j
    have huK : ((u : V) : K) = scale :=
      (congrArg (fun z : V ↦ (z : K)) hu).trans hqzero
    have huinvK : ((u : V) : K) * (((↑(u⁻¹) : V) : K)) = 1 := by
      have huinvV : (u : V) * (↑(u⁻¹) : V) = 1 :=
        (Units.mul_inv_eq_one).2 rfl
      change ((((u : V) * (↑(u⁻¹) : V) : V) : K)) = 1
      rw [huinvV]
      exact map_one V.toSubring.subtype
    change ((q j : V) : K) * (((↑(u⁻¹) : V) : K)) = x j
    calc
      ((q j : V) : K) * (((↑(u⁻¹) : V) : K)) =
          (scale * x j) * (((↑(u⁻¹) : V) : K)) := by rw [hq j]
      _ = x j * (((u : V) : K) * (((↑(u⁻¹) : V) : K))) := by
        rw [huK]
        ring
      _ = x j := by rw [huinvK, mul_one]
  let gV : V := MvPolynomial.eval₂Hom coeff xV g
  have hgV : (gV : K) = MvPolynomial.eval₂ (algebraMap k K) x g := by
    calc
      (gV : K) = MvPolynomial.eval₂Hom
          (V.toSubring.subtype.comp coeff) (fun j ↦ (xV j : K)) g :=
        MvPolynomial.map_eval₂Hom coeff xV V.toSubring.subtype g
      _ = MvPolynomial.eval₂Hom (algebraMap k K) x g := by
        apply MvPolynomial.eval₂Hom_congr hcoeff
        · funext j
          exact hxV j
        · rfl
      _ = MvPolynomial.eval₂ (algebraMap k K) x g := rfl
  apply hparameter_nonunit
  rw [isUnit_iff_exists_inv]
  refine ⟨gV, ?_⟩
  apply Subtype.ext
  change (parameter : K) * (gV : K) = (1 : V)
  simpa [hparameter, hgV] using hinverse

/-- The denominator in the retained normalization of a component point is a
nonunit whenever the ambient support avoids the selected coordinate axis. -/
theorem normalizedComponentProjectivePoint_zero_nonunit
    {k : Type u} [Field k] [IsAlgClosed k] {n : ℕ}
    (I : RightIdeal (PresentedWeyl k n)) (i : Fin n)
    (hdisjoint : Disjoint
      (orderCharacteristicSupport k I)
      (PrimeSpectrum.zeroLocus
        ({MvPolynomial.X (.inl i)} : Set (SymbolRing k n))))
    (P : PrimeSpectrum (MvPolynomial (Fin n) k))
    (hBP : reducedOrderBaseIdeal k I ≤ P.asIdeal)
    (W : Data k (FractionRing (MvPolynomial (Fin n) k ⧸ P.asIdeal))
      (componentCoordinate P i)) :
    letI : Algebra (CoordinateZeroLocalRing W.coefficientField)
        (FractionRing (MvPolynomial (Fin n) k ⧸ P.asIdeal)) :=
      W.ambientAlgebra
    ∀ (q : Fin (n + 1) → W.place.valuation.toSubring)
      (scale : FractionRing (MvPolynomial (Fin n) k ⧸ P.asIdeal)),
      (∀ a, (q a : FractionRing
          (MvPolynomial (Fin n) k ⧸ P.asIdeal)) =
        scale * componentProjectivePoint P a) →
      ¬IsUnit (q 0) := by
  let F := FractionRing (MvPolynomial (Fin n) k ⧸ P.asIdeal)
  let : Algebra (CoordinateZeroLocalRing W.coefficientField) F :=
    W.ambientAlgebra
  intro q scale hq
  let : SMul W.coefficientField (CoordinateZeroLocalRing W.coefficientField) := Algebra.toSMul
  let : SMul (CoordinateZeroLocalRing W.coefficientField) F := Algebra.toSMul
  let : SMul W.coefficientField F := Algebra.toSMul
  let : IsScalarTower W.coefficientField
      (CoordinateZeroLocalRing W.coefficientField) F := W.coefficientTower
  let V := W.place.valuation.toSubring
  obtain ⟨g, hg⟩ := exists_componentCoordinate_polynomial_inverse
    I i hdisjoint P hBP
  let phi : MvPolynomial (Fin n) k →+* F :=
    (algebraMap (MvPolynomial (Fin n) k ⧸ P.asIdeal) F).comp
      (Ideal.Quotient.mk P.asIdeal)
  have hphiC : phi.comp MvPolynomial.C = algebraMap k F := by
    ext c
    exact IsScalarTower.algebraMap_apply k
      (MvPolynomial (Fin n) k ⧸ P.asIdeal) F c
  have hphiX : ∀ j, phi (MvPolynomial.X j) = componentCoordinate P j := by
    intro j
    rfl
  have hpoly : phi g = MvPolynomial.eval₂ (algebraMap k F)
      (fun j ↦ componentCoordinate P j) g := by
    rw [MvPolynomial.map_mvPolynomial_eq_eval₂ phi g]
    change MvPolynomial.eval₂Hom (phi.comp MvPolynomial.C)
        (fun j ↦ phi (MvPolynomial.X j)) g =
      MvPolynomial.eval₂Hom (algebraMap k F)
        (fun j ↦ componentCoordinate P j) g
    apply MvPolynomial.eval₂Hom_congr hphiC
    · funext j
      exact hphiX j
    · rfl
  have hinverse : componentCoordinate P i *
      MvPolynomial.eval₂ (algebraMap k F)
        (fun j ↦ componentCoordinate P j) g = 1 := by
    have hzero : phi (MvPolynomial.X i * g - 1) = 0 := by
      have hmk : Ideal.Quotient.mk P.asIdeal
          (MvPolynomial.X i * g - 1) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr hg
      simpa [phi] using (congrArg
        (algebraMap (MvPolynomial (Fin n) k ⧸ P.asIdeal) F) hmk)
    rw [map_sub, map_mul, map_one, sub_eq_zero, hphiX, hpoly] at hzero
    exact hzero
  let coeff : k →+* V :=
    (relativeCoefficientMap W.coefficientField W.place).comp
      (algebraMap k W.coefficientField)
  have hcoeff : W.place.valuation.toSubring.subtype.comp coeff =
      algebraMap k F := by
    ext c
    change ((relativeCoefficientMap W.coefficientField W.place
      (algebraMap k W.coefficientField c) : V) : F) = algebraMap k F c
    calc
      ((relativeCoefficientMap W.coefficientField W.place
          (algebraMap k W.coefficientField c) : V) : F) =
          algebraMap W.coefficientField F
            (algebraMap k W.coefficientField c) :=
        DFunLike.congr_fun
          (relativeCoefficientMap_commutes W.coefficientField W.place)
          (algebraMap k W.coefficientField c)
      _ = algebraMap k F c :=
        IsScalarTower.algebraMap_apply k W.coefficientField F c
  apply normalized_denominator_nonunit_of_polynomial_inverse
    (V := W.place.valuation) (coeff := coeff) hcoeff
    (x := fun j ↦ componentCoordinate P j)
    (qzero := q 0) (q := fun j ↦ q (Fin.succ j)) (scale := scale)
    (i := i) (parameter := W.place.parameter) (g := g)
  · simpa [componentProjectivePoint] using hq 0
  · intro j
    simpa [componentProjectivePoint] using hq (Fin.succ j)
  · exact W.parameter_eq_coordinate
  · exact W.place.parameter_nonunit
  · exact hinverse

/-- The normalized homogeneous zeroth coordinate therefore vanishes in the
completed residue chart. -/
theorem normalizedComponentProjectivePoint_zero_vanish
    {k : Type u} [Field k] [CharZero k] [IsAlgClosed k] {n : ℕ}
    (I : RightIdeal (PresentedWeyl k n)) (i : Fin n)
    (hdisjoint : Disjoint
      (orderCharacteristicSupport k I)
      (PrimeSpectrum.zeroLocus
        ({MvPolynomial.X (.inl i)} : Set (SymbolRing k n))))
    (P : PrimeSpectrum (MvPolynomial (Fin n) k))
    (hBP : reducedOrderBaseIdeal k I ≤ P.asIdeal)
    (W : Data k (FractionRing (MvPolynomial (Fin n) k ⧸ P.asIdeal))
      (componentCoordinate P i)) :
    letI : Algebra (CoordinateZeroLocalRing W.coefficientField)
        (FractionRing (MvPolynomial (Fin n) k ⧸ P.asIdeal)) :=
      W.ambientAlgebra
    let V := W.place.valuation.toSubring
    letI : IsDiscreteValuationRing V := W.place.isDiscrete
    letI : Algebra W.coefficientField V :=
      (relativeCoefficientMap W.coefficientField W.place).toAlgebra
    ∀ (q : Fin (n + 1) → W.place.valuation.toSubring)
      (scale : FractionRing (MvPolynomial (Fin n) k ⧸ P.asIdeal)),
      (∀ a, (q a : FractionRing
          (MvPolynomial (Fin n) k ⧸ P.asIdeal)) =
        scale * componentProjectivePoint P a) →
      PowerSeries.constantCoeff
        (retainedToCompletedPowerSeries W (q 0)) = 0 := by
  let : Algebra (CoordinateZeroLocalRing W.coefficientField)
      (FractionRing (MvPolynomial (Fin n) k ⧸ P.asIdeal)) :=
    W.ambientAlgebra
  let V := W.place.valuation.toSubring
  let : IsDiscreteValuationRing V := W.place.isDiscrete
  let : Algebra W.coefficientField V :=
    (relativeCoefficientMap W.coefficientField W.place).toAlgebra
  dsimp only
  intro q scale hq
  have hnonunit : ¬IsUnit (q 0) :=
    normalizedComponentProjectivePoint_zero_nonunit
      I i hdisjoint P hBP W q scale hq
  exact retainedToCompletedPowerSeries_constantCoeff_eq_zero_of_nonunit W
    (q 0) hnonunit


end

end Stafford38.Geometry.ComponentProjectiveOrder
