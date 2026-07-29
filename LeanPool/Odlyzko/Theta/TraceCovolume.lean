/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.Theta.PoissonSummation
public import LeanPool.Odlyzko.Theta.TraceDualLattice
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! TODO: Add doc-string. -/

@[expose] public section

noncomputable section

open Complex Module NumberField NumberField.InfinitePlace
open scoped nonZeroDivisors

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K]

open Classical in
/-- A trace to euclidean used in the Odlyzko-bound argument. -/
noncomputable def traceToEuclidean :
    mixedEmbedding.euclidean.mixedSpace K ≃L[ℝ]
      mixedEmbedding.euclidean.mixedSpace K :=
  (traceToMixed K).trans (mixedEmbedding.euclidean.toMixed K).symm

open Classical in
theorem traceIdealLattice_eq_comap_euclideanIdealLattice
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    traceIdealLattice K I =
      ZLattice.comap ℝ (euclideanIdealLattice K I)
        (traceToEuclidean K).toLinearMap := by
  rfl

open Classical in
private theorem divideBySqrtTwo_toLinearMap :
    (divideBySqrtTwo : ℂ ≃L[ℝ] ℂ).toLinearMap =
      (Real.sqrt 2)⁻¹ • LinearMap.id := by
  rfl

open Classical in
private theorem det_divideBySqrtTwo :
    LinearMap.det (divideBySqrtTwo : ℂ ≃L[ℝ] ℂ).toLinearMap = 2⁻¹ := by
  rw [divideBySqrtTwo_toLinearMap, LinearMap.det_smul]
  simp

omit [NumberField K] in
open Classical in
private theorem unscaleComplexCoordinates_toLinearMap :
    (unscaleComplexCoordinates K).toLinearMap =
      LinearMap.pi (fun w ↦
        (divideBySqrtTwo : ℂ ≃L[ℝ] ℂ).toLinearMap.comp
          (LinearMap.proj w)) := by
  apply LinearMap.ext
  intro z
  funext w
  simp [unscaleComplexCoordinates]

open Classical in
private theorem det_unscaleComplexCoordinates :
    LinearMap.det (unscaleComplexCoordinates K).toLinearMap =
      (2⁻¹) ^ nrComplexPlaces K := by
  rw [unscaleComplexCoordinates_toLinearMap, LinearMap.det_pi]
  simp [det_divideBySqrtTwo]

open Classical in
private theorem det_traceToEuclidean :
    LinearMap.det (traceToEuclidean K).toLinearMap =
      (2⁻¹) ^ nrComplexPlaces K := by
  let u :=
    (ContinuousLinearEquiv.refl ℝ
      ({w : InfinitePlace K // IsReal w} → ℝ)).prodCongr
        (unscaleComplexCoordinates K)
  have hmap :
      (traceToEuclidean K).toLinearMap =
        (mixedEmbedding.euclidean.toMixed K).symm.toLinearMap.comp
          (u.toLinearMap.comp
            (mixedEmbedding.euclidean.toMixed K).toLinearMap) := by
    rfl
  rw [hmap]
  rw [show LinearMap.det
      ((mixedEmbedding.euclidean.toMixed K).symm.toLinearMap.comp
        (u.toLinearMap.comp
          (mixedEmbedding.euclidean.toMixed K).toLinearMap)) =
      LinearMap.det u.toLinearMap by
        exact LinearMap.det_conj u.toLinearMap
          (mixedEmbedding.euclidean.toMixed K).symm.toLinearEquiv]
  change LinearMap.det
      (LinearMap.prodMap
        (LinearMap.id (R := ℝ)
          (M := {w : InfinitePlace K // IsReal w} → ℝ))
        (unscaleComplexCoordinates K).toLinearMap) = _
  rw [LinearMap.det_prodMap, LinearMap.det_id, one_mul,
    det_unscaleComplexCoordinates]

open Classical in
theorem covolume_comap_continuousLinearEquiv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (μ : MeasureTheory.Measure E) [MeasureTheory.Measure.IsAddHaarMeasure μ]
    (e : E ≃L[ℝ] E) :
    ZLattice.covolume
        (ZLattice.comap ℝ L e.toLinearMap) μ =
      |LinearMap.det e.toLinearMap|⁻¹ *
        ZLattice.covolume L μ := by
  let b := Free.chooseBasis ℤ L
  have hfund :
      ZSpan.fundamentalDomain
          ((b.ofZLatticeComap ℝ L e.toLinearEquiv).ofZLatticeBasis
            ℝ (ZLattice.comap ℝ L e.toLinearMap)) =
        e ⁻¹'
          ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ L) := by
    rw [← e.image_symm_eq_preimage, ← e.symm.coe_toLinearEquiv,
      ZSpan.map_fundamentalDomain]
    congr 1
    ext
    simp
  have hmeasure :
      μ (e ⁻¹' ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ L)) =
        ENNReal.ofReal |(LinearMap.det e.toLinearMap)⁻¹| *
          μ (ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ L)) := by
    exact MeasureTheory.Measure.addHaar_preimage_linearMap
      μ (LinearEquiv.isUnit_det' e.toLinearEquiv).ne_zero _
  rw [ZLattice.covolume_eq_measure_fundamentalDomain _
      μ
      (ZLattice.isAddFundamentalDomain
        (b.ofZLatticeComap ℝ L e.toLinearEquiv)
        μ),
    ZLattice.covolume_eq_measure_fundamentalDomain L
      μ (ZLattice.isAddFundamentalDomain b μ),
    hfund, MeasureTheory.measureReal_def,
    MeasureTheory.measureReal_def,
    hmeasure,
    ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (abs_nonneg _)]
  simp

open Classical in
theorem covolume_traceIdealLattice
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ZLattice.covolume (traceIdealLattice K I) =
      FractionalIdeal.absNorm
          (I : FractionalIdeal (𝓞 K)⁰ K) *
        √|discr K| := by
  rw [traceIdealLattice_eq_comap_euclideanIdealLattice K I,
    covolume_comap_continuousLinearEquiv
      (euclideanIdealLattice K I) MeasureTheory.volume
      (traceToEuclidean K),
    det_traceToEuclidean,
    covolume_euclideanIdealLattice]
  have hpos : 0 < (2⁻¹ : ℝ) ^ nrComplexPlaces K := by positivity
  grind

end NumberField.Odlyzko
