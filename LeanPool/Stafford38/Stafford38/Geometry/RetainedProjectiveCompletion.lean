/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import LeanPool.Stafford38.Stafford38.Geometry.ProjectiveValuationNormalization
public import LeanPool.Stafford38.Stafford38.Geometry.RelativeRetainedBoundaryPlace
public import Mathlib.RingTheory.PowerSeries.Inverse


/-!
# Transport from a retained valuation ring to its power-series completion

The completed-DVR equivalence turns every valuation-ring coordinate into a
power series over the actual residue field.  Krull intersection makes this
coordinate map injective, so projective nonvanishing is preserved.
-/

@[expose] public section

namespace Stafford38.Geometry.RetainedProjectiveCompletion

open IsLocalRing
open Stafford38.Geometry.AsymptoticDivisorExistence
open Stafford38.Geometry.ProjectiveValuationNormalization
open Stafford38.Geometry.RelativeCoefficientDVR
open Stafford38.Geometry.RelativeRetainedBoundaryPlace

noncomputable section


universe u v

/-- Map retained valuation-ring coordinates into the corresponding
power-series ring via the actual adic completion. -/
def retainedToCompletedPowerSeries
    {k K : Type u} [Field k] [CharZero k]
    [Field K] [Algebra k K] {x : K} (W : Data k K x) :
    letI : Algebra (CoordinateZeroLocalRing W.coefficientField) K :=
      W.ambientAlgebra
    let V := W.place.valuation.toSubring
    letI : IsDiscreteValuationRing V := W.place.isDiscrete
    letI : Algebra W.coefficientField V :=
      (relativeCoefficientMap W.coefficientField W.place).toAlgebra
    V →+* PowerSeries (ResidueField V) := by
  letI : Algebra (CoordinateZeroLocalRing W.coefficientField) K :=
    W.ambientAlgebra
  let V := W.place.valuation.toSubring
  letI : IsDiscreteValuationRing V := W.place.isDiscrete
  letI : Algebra W.coefficientField V :=
    (relativeCoefficientMap W.coefficientField W.place).toAlgebra
  exact W.completedPowerSeriesEquiv.symm.toRingHom.comp
    (algebraMap V (AdicCompletion (maximalIdeal V) V))

/-- Completion transport does not collapse a retained coordinate. -/
theorem retainedToCompletedPowerSeries_injective
    {k K : Type u} [Field k] [CharZero k]
    [Field K] [Algebra k K] {x : K} (W : Data k K x) :
    letI : Algebra (CoordinateZeroLocalRing W.coefficientField) K :=
      W.ambientAlgebra
    let V := W.place.valuation.toSubring
    letI : IsDiscreteValuationRing V := W.place.isDiscrete
    letI : Algebra W.coefficientField V :=
      (relativeCoefficientMap W.coefficientField W.place).toAlgebra
    Function.Injective (retainedToCompletedPowerSeries W) := by
  let : Algebra (CoordinateZeroLocalRing W.coefficientField) K :=
    W.ambientAlgebra
  let V := W.place.valuation.toSubring
  let : IsDiscreteValuationRing V := W.place.isDiscrete
  let : Algebra W.coefficientField V :=
    (relativeCoefficientMap W.coefficientField W.place).toAlgebra
  exact W.completedPowerSeriesEquiv.symm.injective.comp
    (adicCompletion_algebraMap_injective (maximalIdeal V)
      (maximalIdeal.isMaximal V).ne_top)

/-- A retained nonunit has zero constant coefficient in the completed
power-series chart. -/
theorem retainedToCompletedPowerSeries_constantCoeff_eq_zero_of_nonunit
    {k K : Type u} [Field k] [CharZero k]
    [Field K] [Algebra k K] {x : K} (W : Data k K x) :
    letI : Algebra (CoordinateZeroLocalRing W.coefficientField) K :=
      W.ambientAlgebra
    let V := W.place.valuation.toSubring
    letI : IsDiscreteValuationRing V := W.place.isDiscrete
    letI : Algebra W.coefficientField V :=
      (relativeCoefficientMap W.coefficientField W.place).toAlgebra
    ∀ v : ↥V, ¬IsUnit v →
      PowerSeries.constantCoeff (R := ResidueField V)
        (retainedToCompletedPowerSeries W v) = 0 := by
  let : Algebra (CoordinateZeroLocalRing W.coefficientField) K :=
    W.ambientAlgebra
  let V := W.place.valuation.toSubring
  let : IsDiscreteValuationRing V := W.place.isDiscrete
  let : Algebra W.coefficientField V :=
    (relativeCoefficientMap W.coefficientField W.place).toAlgebra
  dsimp only
  intro v hv
  by_contra hconstant
  have hseries : IsUnit (retainedToCompletedPowerSeries W v) :=
    PowerSeries.isUnit_iff_constantCoeff.mpr
      (isUnit_iff_ne_zero.mpr hconstant)
  have hcompletion : IsUnit
      (algebraMap V (AdicCompletion (maximalIdeal V) V) v) := by
    have hmap := hseries.map W.completedPowerSeriesEquiv.toMonoidHom
    simpa [retainedToCompletedPowerSeries] using hmap
  have hlevel := hcompletion.map
    (AdicCompletion.evalₐ (maximalIdeal V) 1).toRingHom.toMonoidHom
  have heval : AdicCompletion.evalₐ (maximalIdeal V) 1
      (algebraMap V (AdicCompletion (maximalIdeal V) V) v) =
      Ideal.Quotient.mk ((maximalIdeal V) ^ 1) v := by
    exact (AdicCompletion.evalₐ (maximalIdeal V) 1).commutes v
  change IsUnit (AdicCompletion.evalₐ (maximalIdeal V) 1
    (algebraMap V (AdicCompletion (maximalIdeal V) V) v)) at hlevel
  rw [heval] at hlevel
  have hvmax : v ∈ maximalIdeal V := by
    rw [mem_maximalIdeal, mem_nonunits_iff]
    exact hv
  have hvpow : v ∈ (maximalIdeal V) ^ 1 := by simpa only [pow_one] using hvmax
  have hzero : Ideal.Quotient.mk ((maximalIdeal V) ^ 1) v = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hvpow
  rw [hzero] at hlevel
  let : Nontrivial (V ⧸ (maximalIdeal V) ^ 1) :=
    Ideal.Quotient.nontrivial_iff.mpr (by
      simpa only [pow_one] using (maximalIdeal.isMaximal V).ne_top)
  exact not_isUnit_zero hlevel

/-- A normalized valuation-ring projective family remains normalized and
nonzero after transport to the power-series completion. -/
theorem retainedCompleted_family_properties
    {k K : Type u} [Field k] [CharZero k]
    [Field K] [Algebra k K] {x : K} (W : Data k K x) :
    letI : Algebra (CoordinateZeroLocalRing W.coefficientField) K :=
      W.ambientAlgebra
    let V := W.place.valuation.toSubring
    letI : IsDiscreteValuationRing V := W.place.isDiscrete
    letI : Algebra W.coefficientField V :=
      (relativeCoefficientMap W.coefficientField W.place).toAlgebra
    ∀ {ι : Type v}
      (q : ι → V) (chart zero axis : ι),
      q chart = 1 → q zero ≠ 0 →
      q axis = q zero * W.place.parameter →
      let qhat := fun i ↦ retainedToCompletedPowerSeries W (q i)
      qhat chart = 1 ∧ qhat zero ≠ 0 ∧
        qhat axis = qhat zero *
          retainedToCompletedPowerSeries W W.place.parameter := by
  let : Algebra (CoordinateZeroLocalRing W.coefficientField) K :=
    W.ambientAlgebra
  let V := W.place.valuation.toSubring
  let : IsDiscreteValuationRing V := W.place.isDiscrete
  let : Algebra W.coefficientField V :=
    (relativeCoefficientMap W.coefficientField W.place).toAlgebra
  dsimp only
  intro ι q chart zero axis hchart hzero haxis
  dsimp
  refine ⟨by rw [hchart, map_one], ?_, ?_⟩
  · simpa using (retainedToCompletedPowerSeries_injective W).ne hzero
  · rw [haxis, map_mul]

/-- The retained parameter and a nonunit projective denominator supply all
nonvanishing and residue-vanishing fields needed by the projective order-gap
consumer after completion. -/
theorem retainedCompleted_projective_order_properties
    {k K : Type u} [Field k] [CharZero k]
    [Field K] [Algebra k K] {x : K} (W : Data k K x) :
    letI : Algebra (CoordinateZeroLocalRing W.coefficientField) K :=
      W.ambientAlgebra
    let V := W.place.valuation.toSubring
    letI : IsDiscreteValuationRing V := W.place.isDiscrete
    letI : Algebra W.coefficientField V :=
      (relativeCoefficientMap W.coefficientField W.place).toAlgebra
    ∀ {ι : Type v}
      (q : ι → V) (chart zero axis : ι),
      q chart = 1 → q zero ≠ 0 → ¬IsUnit (q zero) →
      q axis = q zero * W.place.parameter →
      let qhat := fun i ↦ retainedToCompletedPowerSeries W (q i)
      let ratio := retainedToCompletedPowerSeries W W.place.parameter
      qhat chart = 1 ∧ qhat zero ≠ 0 ∧ ratio ≠ 0 ∧
        PowerSeries.constantCoeff (R := ResidueField V) (qhat zero) = 0 ∧
        PowerSeries.constantCoeff (R := ResidueField V) ratio = 0 ∧
        qhat axis = qhat zero * ratio := by
  let : Algebra (CoordinateZeroLocalRing W.coefficientField) K :=
    W.ambientAlgebra
  let V := W.place.valuation.toSubring
  let : IsDiscreteValuationRing V := W.place.isDiscrete
  let : Algebra W.coefficientField V :=
    (relativeCoefficientMap W.coefficientField W.place).toAlgebra
  dsimp only
  intro ι q chart zero axis hchart hzero hzero_nonunit haxis
  obtain ⟨hqchart, hqzero, hqaxis⟩ :=
    retainedCompleted_family_properties W q chart zero axis
      hchart hzero haxis
  refine ⟨hqchart, hqzero,
    (by simpa using
      (retainedToCompletedPowerSeries_injective W).ne W.place.parameter_ne),
    retainedToCompletedPowerSeries_constantCoeff_eq_zero_of_nonunit W
      (q zero) hzero_nonunit,
    retainedToCompletedPowerSeries_constantCoeff_eq_zero_of_nonunit W
      W.place.parameter W.place.parameter_nonunit,
    hqaxis⟩


end

end Stafford38.Geometry.RetainedProjectiveCompletion
