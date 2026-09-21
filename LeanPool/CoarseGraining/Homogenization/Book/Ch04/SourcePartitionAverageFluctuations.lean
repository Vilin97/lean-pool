/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch04.SourceDescendantAverages
import LeanPool.CoarseGraining.Homogenization.Book.Ch04.SourcePartitionAverageDefinitions
import LeanPool.CoarseGraining.Homogenization.Book.Ch04.SourceStationaryExpectations

/-!
# One-origin source partition-average fluctuations

These estimates transport a single source-local observable from the origin
cube to every descendant using source stationarity and unit-range dependence.
-/

namespace Homogenization.Book.Ch04

open MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

private theorem isBigO_gammaSigma_iff_of_map_eq_map
    {d : ℕ} {P : SourceCoeffLaw d} {σ A : ℝ}
    {f g : Source.Coarse.Carrier d → ℝ}
    (hf : Measurable f) (hg : Measurable g)
    (hmap : Measure.map f P = Measure.map g P) :
    IsBigO P (gammaSigma σ) f A ↔ IsBigO P (gammaSigma σ) g A := by
  rw [isBigO_gammaSigma_iff, isBigO_gammaSigma_iff]
  constructor
  · intro h t ht
    let s : Set ℝ := {x | A * t < |x|}
    have hs : MeasurableSet s := by
      dsimp [s]
      exact measurableSet_lt measurable_const continuous_abs.measurable
    have hmass := congrArg (fun μ : Measure ℝ => μ s) hmap
    have hmass_real := congrArg ENNReal.toReal hmass
    have hfg :
        P.real (absTailEvent f (A * t)) = P.real (absTailEvent g (A * t)) := by
      simpa [s, absTailEvent, Measure.map_apply hf hs, Measure.map_apply hg hs]
        using! hmass_real
    rw [← hfg]
    exact h ht
  · intro h t ht
    let s : Set ℝ := {x | A * t < |x|}
    have hs : MeasurableSet s := by
      dsimp [s]
      exact measurableSet_lt measurable_const continuous_abs.measurable
    have hmass := congrArg (fun μ : Measure ℝ => μ s) hmap
    have hmass_real := congrArg ENNReal.toReal hmass
    have hgf :
        P.real (absTailEvent g (A * t)) = P.real (absTailEvent f (A * t)) := by
      simpa [s, absTailEvent, Measure.map_apply hf hs, Measure.map_apply hg hs]
        using! hmass_real.symm
    rw [← hgf]
    exact h ht

private theorem isBigO_psiSigma_iff_of_map_eq_map
    {d : ℕ} {P : SourceCoeffLaw d} {σ A : ℝ}
    {f g : Source.Coarse.Carrier d → ℝ}
    (hf : Measurable f) (hg : Measurable g)
    (hmap : Measure.map f P = Measure.map g P) :
    IsBigO P (psiSigma σ) f A ↔ IsBigO P (psiSigma σ) g A := by
  rw [isBigO_psiSigma_iff, isBigO_psiSigma_iff]
  constructor
  · intro h t ht
    let s : Set ℝ := {x | A * t < |x|}
    have hs : MeasurableSet s := by
      dsimp [s]
      exact measurableSet_lt measurable_const continuous_abs.measurable
    have hmass := congrArg (fun μ : Measure ℝ => μ s) hmap
    have hmass_real := congrArg ENNReal.toReal hmass
    have hfg :
        P.real (absTailEvent f (A * t)) = P.real (absTailEvent g (A * t)) := by
      simpa [s, absTailEvent, Measure.map_apply hf hs, Measure.map_apply hg hs]
        using! hmass_real
    rw [← hfg]
    exact h ht
  · intro h t ht
    let s : Set ℝ := {x | A * t < |x|}
    have hs : MeasurableSet s := by
      dsimp [s]
      exact measurableSet_lt measurable_const continuous_abs.measurable
    have hmass := congrArg (fun μ : Measure ℝ => μ s) hmap
    have hmass_real := congrArg ENNReal.toReal hmass
    have hgf :
        P.real (absTailEvent g (A * t)) = P.real (absTailEvent f (A * t)) := by
      simpa [s, absTailEvent, Measure.map_apply hf hs, Measure.map_apply hg hs]
        using! hmass_real.symm
    rw [← hgf]
    exact h ht

/-- Source P1 makes the expectation of a translated one-origin observable
equal to its origin expectation. -/
theorem integral_sourceTranslatedObservable_eq_origin_of_sourceStationaryLaw
    {d : ℕ} {P : SourceCoeffLaw d} (hP : SourceStationaryLaw P)
    (z : Fin d → ℤ) (X : Source.Coarse.Carrier d → ℝ)
    (hX : Measurable X) :
    ∫ a, sourceTranslatedObservable z X a ∂P = ∫ a, X a ∂P := by
  simpa [sourceTranslatedObservable] using
    (integral_comp_sourceCarrier_translate_eq_of_sourceStationaryLaw
      (P := P) hP z X hX)

/-- Centered `Gamma_sigma` concentration for the source partition average
formed by translating one origin-cube observable to every descendant. -/
theorem isBigO_gammaSigma_sourceCenteredTranslatedDescendantAverage_of_sourceUnitRangeDependentLaw
    {d : ℕ} {n m : ℤ} {P : SourceCoeffLaw d} [IsProbabilityMeasure P]
    {σ K : ℝ}
    (hn : 0 ≤ n) (hnm : n ≤ m)
    (hPstat : SourceStationaryLaw P) (hPdep : SourceUnitRangeDependentLaw P)
    (X : Source.Coarse.Carrier d → ℝ)
    (hX_local :
      IsSourceLocalRandomVariable (cubeSet (originCube d n))
        (measurableSet_cubeSet (originCube d n)) X)
    (hX_int : Integrable X P)
    (hσ₀ : 0 < σ) (hσ₂ : σ ≤ 2) (hK : 0 < K)
    (hX0 : IsBigO P (gammaSigma σ) (sourceCenteredObservable P X hX_int) K) :
    IsBigO P (gammaSigma σ)
      (sourceCenteredTranslatedDescendantAverage P n m hn hnm X hX_int)
      (gammaSigmaDescendantsAtScaleConst d n σ *
        partitionCardinalityScale (d := d) n m * K) := by
  let μ0 : ℝ := ∫ a, X a ∂P
  let Y : TriadicCube d → Source.Coarse.Carrier d → ℝ :=
    fun R => sourceTranslatedObservable (scaleTranslationShift n R) X
  let Z : TriadicCube d → Source.Coarse.Carrier d → ℝ := fun R a => Y R a - μ0
  have hX_meas : Measurable X := hX_local.measurable
  have hY_local :
      ∀ R ∈ descendantsAtScale (originCube d m) n,
        IsSourceLocalRandomVariable (cubeSet R) (measurableSet_cubeSet R) (Y R) := by
    intro R hR
    have hshift :=
      cubeSet_eq_translateSet_originCube_of_mem_descendantsAtScale_originCube
        (d := d) hn hnm hR
    simpa only [Y, sourceTranslatedObservable, hshift] using
      (hX_local.comp_translate (scaleTranslationShift n R))
  have hY_meas : ∀ R ∈ descendantsAtScale (originCube d m) n, Measurable (Y R) := by
    intro R hR
    exact (hY_local R hR).measurable
  have hY_int : ∀ R ∈ descendantsAtScale (originCube d m) n, Integrable (Y R) P := by
    intro R _hR
    simpa [Y, sourceTranslatedObservable] using
      (integrable_comp_sourceCarrier_translate_of_sourceStationaryLaw
        (P := P) hPstat (scaleTranslationShift n R) X hX_int)
  have hZ_local :
      ∀ R ∈ descendantsAtScale (originCube d m) n,
        IsSourceLocalRandomVariable (cubeSet R) (measurableSet_cubeSet R) (Z R) := by
    intro R hR
    simpa [Z] using (hY_local R hR).sub
      (IsSourceLocalRandomVariable.const (cubeSet R) (measurableSet_cubeSet R) μ0)
  have hZ_tail :
      ∀ R ∈ descendantsAtScale (originCube d m) n,
        IsBigO P (gammaSigma σ) (Z R) K := by
    intro R hR
    have hZ_meas : Measurable (Z R) := (hZ_local R hR).measurable
    have hX0_meas : Measurable (sourceCenteredObservable P X hX_int) :=
      hX_meas.sub measurable_const
    have hmap : Measure.map (Z R) P = Measure.map (sourceCenteredObservable P X hX_int) P := by
      simpa [Z, Y, μ0, sourceCenteredObservable, sourceTranslatedObservable,
        Function.comp_def] using
        (map_comp_sourceCarrier_translate_eq_of_sourceStationaryLaw
          (P := P) hPstat (sourceCenteredObservable P X hX_int) hX0_meas
          (scaleTranslationShift n R))
    exact (isBigO_gammaSigma_iff_of_map_eq_map hZ_meas hX0_meas hmap).2 hX0
  have hZ_mean : ∀ R ∈ descendantsAtScale (originCube d m) n, ∫ a, Z R a ∂P = 0 := by
    intro R hR
    have hY_expect : ∫ a, Y R a ∂P = μ0 := by
      simpa [Y, μ0] using
        (integral_sourceTranslatedObservable_eq_origin_of_sourceStationaryLaw
          (P := P) hPstat (scaleTranslationShift n R) X hX_meas)
    calc
      ∫ a, Z R a ∂P = ∫ a, Y R a ∂P - ∫ _a, μ0 ∂P := by
        simpa [Z] using integral_sub (hY_int R hR) (integrable_const μ0)
      _ = μ0 - μ0 := by rw [hY_expect]; simp
      _ = 0 := sub_self _
  have havg :=
    isBigO_gammaSigma_descendantAverage_of_sourceUnitRangeDependentLaw
      (Q := originCube d m) (k := n) (P := P)
      hnm hPdep hσ₀ hσ₂ hK Z hZ_local hZ_tail hZ_mean
  have havg_fun_eq :
      (fun a => ((descendantsAtScale (originCube d m) n).card : ℝ)⁻¹ *
        ∑ R ∈ descendantsAtScale (originCube d m) n, Z R a) =
        sourceCenteredTranslatedDescendantAverage P n m hn hnm X hX_int := by
    rfl
  simpa only [havg_fun_eq, partitionCardinalityScale, div_eq_mul_inv,
    mul_assoc, mul_left_comm, mul_comm] using havg

/-- Centered `Psi_sigma` concentration for the source partition average
formed by translating one origin-cube observable to every descendant. -/
theorem isBigO_psiSigma_sourceCenteredTranslatedDescendantAverage_of_sourceUnitRangeDependentLaw
    {d : ℕ} {n m : ℤ} {P : SourceCoeffLaw d} [IsProbabilityMeasure P]
    {σ K : ℝ}
    (hn : 0 ≤ n) (hnm : n ≤ m)
    (hPstat : SourceStationaryLaw P) (hPdep : SourceUnitRangeDependentLaw P)
    (X : Source.Coarse.Carrier d → ℝ)
    (hX_local :
      IsSourceLocalRandomVariable (cubeSet (originCube d n))
        (measurableSet_cubeSet (originCube d n)) X)
    (hX_int : Integrable X P)
    (hσ : 1 ≤ σ) (hK : 0 < K)
    (hX0 : IsBigO P (psiSigma σ) (sourceCenteredObservable P X hX_int) K) :
    IsBigO P (psiSigma σ)
      (sourceCenteredTranslatedDescendantAverage P n m hn hnm X hX_int)
      (psiSigmaDescendantsAtScaleConst d n σ *
        partitionCardinalityScale (d := d) n m * K) := by
  let μ0 : ℝ := ∫ a, X a ∂P
  let Y : TriadicCube d → Source.Coarse.Carrier d → ℝ :=
    fun R => sourceTranslatedObservable (scaleTranslationShift n R) X
  let Z : TriadicCube d → Source.Coarse.Carrier d → ℝ := fun R a => Y R a - μ0
  have hX_meas : Measurable X := hX_local.measurable
  have hY_local :
      ∀ R ∈ descendantsAtScale (originCube d m) n,
        IsSourceLocalRandomVariable (cubeSet R) (measurableSet_cubeSet R) (Y R) := by
    intro R hR
    have hshift :=
      cubeSet_eq_translateSet_originCube_of_mem_descendantsAtScale_originCube
        (d := d) hn hnm hR
    simpa only [Y, sourceTranslatedObservable, hshift] using
      (hX_local.comp_translate (scaleTranslationShift n R))
  have hY_int : ∀ R ∈ descendantsAtScale (originCube d m) n, Integrable (Y R) P := by
    intro R _hR
    simpa [Y, sourceTranslatedObservable] using
      (integrable_comp_sourceCarrier_translate_of_sourceStationaryLaw
        (P := P) hPstat (scaleTranslationShift n R) X hX_int)
  have hZ_local :
      ∀ R ∈ descendantsAtScale (originCube d m) n,
        IsSourceLocalRandomVariable (cubeSet R) (measurableSet_cubeSet R) (Z R) := by
    intro R hR
    simpa [Z] using (hY_local R hR).sub
      (IsSourceLocalRandomVariable.const (cubeSet R) (measurableSet_cubeSet R) μ0)
  have hZ_int : ∀ R ∈ descendantsAtScale (originCube d m) n, Integrable (Z R) P := by
    intro R hR
    simpa [Z] using! (hY_int R hR).sub (integrable_const μ0)
  have hZ_tail :
      ∀ R ∈ descendantsAtScale (originCube d m) n,
        IsBigO P (psiSigma σ) (Z R) K := by
    intro R hR
    have hZ_meas : Measurable (Z R) := (hZ_local R hR).measurable
    have hX0_meas : Measurable (sourceCenteredObservable P X hX_int) :=
      hX_meas.sub measurable_const
    have hmap : Measure.map (Z R) P = Measure.map (sourceCenteredObservable P X hX_int) P := by
      simpa [Z, Y, μ0, sourceCenteredObservable, sourceTranslatedObservable,
        Function.comp_def] using
        (map_comp_sourceCarrier_translate_eq_of_sourceStationaryLaw
          (P := P) hPstat (sourceCenteredObservable P X hX_int) hX0_meas
          (scaleTranslationShift n R))
    exact (isBigO_psiSigma_iff_of_map_eq_map hZ_meas hX0_meas hmap).2 hX0
  have hZ_mean : ∀ R ∈ descendantsAtScale (originCube d m) n, ∫ a, Z R a ∂P = 0 := by
    intro R hR
    have hY_expect : ∫ a, Y R a ∂P = μ0 := by
      simpa [Y, μ0] using
        (integral_sourceTranslatedObservable_eq_origin_of_sourceStationaryLaw
          (P := P) hPstat (scaleTranslationShift n R) X hX_meas)
    calc
      ∫ a, Z R a ∂P = ∫ a, Y R a ∂P - ∫ _a, μ0 ∂P := by
        simpa [Z] using integral_sub (hY_int R hR) (integrable_const μ0)
      _ = μ0 - μ0 := by rw [hY_expect]; simp
      _ = 0 := sub_self _
  have havg :=
    isBigO_psiSigma_descendantAverage_of_sourceUnitRangeDependentLaw
      (Q := originCube d m) (k := n) (P := P)
      hnm hPdep hσ hK Z hZ_local hZ_int hZ_tail hZ_mean
  have havg_fun_eq :
      (fun a => ((descendantsAtScale (originCube d m) n).card : ℝ)⁻¹ *
        ∑ R ∈ descendantsAtScale (originCube d m) n, Z R a) =
        sourceCenteredTranslatedDescendantAverage P n m hn hnm X hX_int := by
    rfl
  simpa only [havg_fun_eq, partitionCardinalityScale, div_eq_mul_inv,
    mul_assoc, mul_left_comm, mul_comm] using havg

end

end Homogenization.Book.Ch04
