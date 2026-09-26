/-
Copyright (c) 2026 The lean-malliavin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-malliavin contributors
-/
module

public import LeanPool.Malliavin.Malliavin.PredictableKernel
public import LeanPool.Malliavin.Malliavin.TimewiseCondExp
public import LeanPool.Malliavin.Malliavin.NaturalFiltrationLeftContinuous
public import Mathlib.MeasureTheory.Function.Floor

/-!
# Identification of the predictable-section kernel with the fixed-time kernels

`PredictableKernel.lean` represents the product predictable projection by the sample-space
marginal `predictableSectionKernel` of the finite-horizon product conditional kernel.
`PointwiseCondExp.lean` and `NaturalFiltrationLeftContinuous.lean` identify the time sections
of the projection with the fixed-time conditional expectations `E[U (t, ·) | 𝓕 t]`, which are
in turn integrals against `condExpKernel P (𝓕 t)`.  This file combines the two: for the
natural Brownian filtration, for almost every time `t ∈ [0, T]` and almost every sample `w`,

  `∫ y, U (t, y) ∂predictableSectionKernel (finiteHorizonProductMeasure P T) 𝓕 (t, w)
     = ∫ y, U (t, y) ∂condExpKernel P (𝓕 t) w`.

Equality with the raw fixed-time kernel family is quantified as almost-every-time,
almost-every-sample: that independently chosen family is not known to be jointly measurable.
The ceiling-selected global kernel constructed below is itself jointly predictable, so its
integral representation of the predictable projection is stated almost everywhere for the full
product measure.

Beyond the integral form, the file proves the identification per measurable set
(`predictableSectionKernel_ae_eq_condExpKernel_apply`) and as an equality of measures
(`predictableSectionKernel_ae_eq_condExpKernel`, via the countable family of rational sub-level
sets of a measurable embedding `W ↪ ℝ`), shows horizon consistency, and selects the
ceiling-indexed horizon to define one jointly predictable Markov kernel
`globalPredictableSectionKernel` on all of
`ℝ≥0 × W`.  For the full product measure, the predictable projection of every process is the
integral of its time sections against this one kernel
(`predictableProjection_ae_eq_integral_globalPredictableSectionKernel`, and as `L²` classes
`toLp_integral_globalPredictableSectionKernel`), and the Clark--Ocone integrand of any family is
the corresponding kernel integral of the Malliavin time derivative
(`ClarkOconeFamily.predictableDerivative_ae_eq_integral_globalPredictableSectionKernel`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal InnerProductSpace

namespace Malliavin

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}

/-- **Sections of the predictable projection are fixed-time kernel integrals** for the natural
Brownian filtration: for almost every `t > 0`,

  `(Π U) (t, ·) =ᵐ[P] fun w ↦ ∫ y, U (t, y) ∂condExpKernel P (𝓕 t) w`. -/
theorem timeSection_predictableProjection_ae_eq_integral_condExpKernel_natural
    (hB : IsPreBrownianReal B P) (hm : ∀ s, StronglyMeasurable (B s))
    (hgen : IsWienerGenerated B) (U : TimeProcessL2 P) :
    ∀ᵐ t ∂nonnegativeLebesgueMeasure, 0 < t →
      (fun w ↦ (predictableProjection (Filtration.natural B hm) U : ℝ≥0 × W → ℝ) (t, w))
        =ᵐ[P] fun w ↦ ∫ y, U (t, y) ∂condExpKernel P (Filtration.natural B hm t) w := by
  have _i : SecondCountableTopology (RandomL2 P) :=
    secondCountableTopology_randomL2_of_isWienerGenerated hB hgen
  set 𝓕 := Filtration.natural B hm with h𝓕
  have hmeas : AEStronglyMeasurable[𝓕.predictable]
      ((predictableProjection 𝓕 U : TimeProcessL2 P) : (ℝ≥0 × W) → ℝ)
      (nonnegativeLebesgueMeasure.prod P) := lpMeas.aestronglyMeasurable _
  have hlit := timeSection_predictableProjection_ae_eq_condExp 𝓕 U
    hmeas.stronglyMeasurable_mk hmeas.ae_eq_mk
  have hsec := Measure.ae_ae_of_ae_prod hmeas.ae_eq_mk
  filter_upwards [hlit, hsec, memLp_timeSection_ae U,
    condExp_timeSection_ae_eq_integral_condExpKernel 𝓕 U] with t hlt hst hUt hker hat
  have hint : Integrable (fun w ↦ U (t, w)) P := hUt.integrable one_le_two
  calc (fun w ↦ (predictableProjection 𝓕 U : ℝ≥0 × W → ℝ) (t, w))
      =ᵐ[P] fun w ↦ hmeas.mk _ (t, w) := hst
    _ =ᵐ[P] P[(fun w ↦ U (t, w)) | filtrationPred 𝓕 t] := hlt hat
    _ =ᵐ[P] P[(fun w ↦ U (t, w)) | 𝓕 t] :=
        condExp_natural_filtrationPred_ae_eq hB hm t hat _ hint
    _ =ᵐ[P] fun w ↦ ∫ y, U (t, y) ∂condExpKernel P (𝓕 t) w := hker

/-- **The predictable-section kernel is the fixed-time conditional kernel**, in integral form:
for the natural Brownian filtration, for almost every `t ∈ [0, T]` with `t > 0` and almost every
`w`, integrating the time section of `U` against the sample-space marginal of the product
predictable kernel is the same as integrating it against `condExpKernel P (𝓕 t)`. -/
theorem integral_predictableSectionKernel_ae_eq_integral_condExpKernel
    (hB : IsPreBrownianReal B P) (hm : ∀ s, StronglyMeasurable (B s))
    (hgen : IsWienerGenerated B) (U : TimeProcessL2 P) (T : ℝ≥0) :
    ∀ᵐ t ∂finiteHorizonTimeMeasure T, 0 < t →
      ∀ᵐ w ∂P,
        ∫ y, U (t, y)
            ∂predictableSectionKernel (finiteHorizonProductMeasure P T)
              (Filtration.natural B hm) (t, w)
          = ∫ y, U (t, y) ∂condExpKernel P (Filtration.natural B hm t) w := by
  set 𝓕 := Filtration.natural B hm with h𝓕
  have hpsk := predictableProjection_ae_eq_integral_predictableSectionKernel_Iic 𝓕 U T
  have hpsk' : ∀ᵐ t ∂finiteHorizonTimeMeasure T, ∀ᵐ w ∂P,
      (predictableProjection 𝓕 U : ℝ≥0 × W → ℝ) (t, w)
        = ∫ y, U (t, y)
            ∂predictableSectionKernel (finiteHorizonProductMeasure P T) 𝓕 (t, w) :=
    Measure.ae_ae_of_ae_prod hpsk
  have hker :=
    timeSection_predictableProjection_ae_eq_integral_condExpKernel_natural hB hm hgen U
  have hker' : ∀ᵐ t ∂finiteHorizonTimeMeasure T, 0 < t →
      (fun w ↦ (predictableProjection 𝓕 U : ℝ≥0 × W → ℝ) (t, w))
        =ᵐ[P] fun w ↦ ∫ y, U (t, y) ∂condExpKernel P (𝓕 t) w :=
    ae_restrict_of_ae hker
  filter_upwards [hpsk', hker'] with t hpt hkt hat
  filter_upwards [hpt, hkt hat] with w hw1 hw2
  rw [← hw1]
  exact hw2

/-! ### Null sets and the conditional kernel -/

section KernelNull

variable {Ω : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {μ : Measure Ω} [IsFiniteMeasure μ]

/-- Null sets remain null under the conditional-expectation kernel, almost everywhere. -/
theorem condExpKernel_ae_null (hm : m ≤ mΩ) {N : Set Ω} (hN : MeasurableSet N)
    (h0 : μ N = 0) :
    ∀ᵐ ω ∂μ, condExpKernel μ m ω N = 0 := by
  have h := condExpKernel_ae_eq_condExp (μ := μ) hm hN
  have hind : (Set.indicator N (fun _ ↦ (1 : ℝ))) =ᵐ[μ] 0 := by
    have hmem : ∀ᵐ ω ∂μ, ω ∉ N := by
      rw [ae_iff]
      simpa using h0
    filter_upwards [hmem] with ω hω
    simp only [Set.indicator_of_notMem hω, Pi.zero_apply]
  have hzero : μ⟦N | m⟧ =ᵐ[μ] 0 := by
    refine (condExp_congr_ae hind).trans ?_
    rw [condExp_zero]
  filter_upwards [h, hzero] with ω h1 h2
  have hreal : (condExpKernel μ m ω).real N = 0 := by
    rw [h1, h2]
    rfl
  have hne : condExpKernel μ m ω N ≠ ∞ := measure_ne_top _ _
  rw [Measure.real] at hreal
  exact (ENNReal.toReal_eq_zero_iff _).mp hreal |>.resolve_right hne

/-- Almost everywhere equal functions have equal integrals against the conditional kernel,
almost everywhere. -/
theorem integral_condExpKernel_congr_ae (hm : m ≤ mΩ) {f g : Ω → ℝ} (hfg : f =ᵐ[μ] g) :
    ∀ᵐ ω ∂μ, ∫ y, f y ∂condExpKernel μ m ω = ∫ y, g y ∂condExpKernel μ m ω := by
  have h0 : μ {x | f x ≠ g x} = 0 := hfg
  obtain ⟨N, hsub, hNmeas, hN0⟩ := exists_measurable_superset_of_null h0
  filter_upwards [condExpKernel_ae_null hm hNmeas hN0] with ω hω
  apply integral_congr_ae
  have : condExpKernel μ m ω {x | f x ≠ g x} = 0 :=
    measure_mono_null hsub hω
  exact this

end KernelNull

/-! ### Set-level identification -/

/-- **Per-set identification of the two kernels**: for every measurable `A ⊆ W`, for almost
every `t ∈ [0, T]` with `t > 0` and almost every `w`, the predictable-section kernel and the
fixed-time conditional kernel assign `A` the same mass. -/
theorem predictableSectionKernel_ae_eq_condExpKernel_apply
    (hB : IsPreBrownianReal B P) (hm : ∀ s, StronglyMeasurable (B s))
    (hgen : IsWienerGenerated B) (T : ℝ≥0) {A : Set W} (hA : MeasurableSet A) :
    ∀ᵐ t ∂finiteHorizonTimeMeasure T, 0 < t →
      ∀ᵐ w ∂P,
        predictableSectionKernel (finiteHorizonProductMeasure P T)
            (Filtration.natural B hm) (t, w) A
          = condExpKernel P (Filtration.natural B hm t) w A := by
  set 𝓕 := Filtration.natural B hm with h𝓕
  set μT := finiteHorizonProductMeasure P T with hμT
  -- the elementary test process `1_{Iic T × A}`
  have hR : MeasurableSet (Set.Iic T ×ˢ A) := measurableSet_Iic.prod hA
  have hRne : (nonnegativeLebesgueMeasure.prod P) (Set.Iic T ×ˢ A) ≠ ∞ := by
    rw [Measure.prod_prod]
    exact ENNReal.mul_ne_top (nonnegativeLebesgueMeasure_Iic_ne_top T) (measure_ne_top P A)
  set UA : TimeProcessL2 P := indicatorConstLp 2 hR hRne (1 : ℝ) with hUA
  have hcoe : (UA : ℝ≥0 × W → ℝ)
      =ᵐ[nonnegativeLebesgueMeasure.prod P]
        (Set.Iic T ×ˢ A).indicator (fun _ ↦ (1 : ℝ)) := indicatorConstLp_coeFn
  -- a fixed measurable product-null discrepancy set
  have h0 : (nonnegativeLebesgueMeasure.prod P)
      {p | (UA : ℝ≥0 × W → ℝ) p ≠ (Set.Iic T ×ˢ A).indicator (fun _ ↦ (1 : ℝ)) p} = 0 := hcoe
  obtain ⟨N, hNsub, hNmeas, hN0⟩ := exists_measurable_superset_of_null h0
  have hμTN : μT N = 0 := by
    refine le_antisymm ?_ bot_le
    calc μT N ≤ (nonnegativeLebesgueMeasure.prod P) N := by
          rw [hμT, finiteHorizonProductMeasure_eq_restrict]
          exact Measure.restrict_le_self N
      _ = 0 := hN0
  -- main integral identification for `UA`
  have hmain := integral_predictableSectionKernel_ae_eq_integral_condExpKernel hB hm hgen UA T
  -- sections of the coefficient
  have hsec : ∀ᵐ t ∂finiteHorizonTimeMeasure T,
      (fun y ↦ (UA : ℝ≥0 × W → ℝ) (t, y)) =ᵐ[P]
        fun y ↦ (Set.Iic T ×ˢ A).indicator (fun _ ↦ (1 : ℝ)) (t, y) :=
    ae_restrict_of_ae (Measure.ae_ae_of_ae_prod hcoe)
  -- null and same-time facts for the product kernel
  have hnull := condExpKernel_ae_null (μ := μT) (predictable_le_prod 𝓕) hNmeas hμTN
  have hnull' : ∀ᵐ t ∂finiteHorizonTimeMeasure T, ∀ᵐ w ∂P,
      condExpKernel μT 𝓕.predictable (t, w) N = 0 :=
    Measure.ae_ae_of_ae_prod hnull
  have hsame := condExpKernel_predictable_ae_same_time μT 𝓕
  have hsame' : ∀ᵐ t ∂finiteHorizonTimeMeasure T, ∀ᵐ w ∂P,
      ∀ᵐ q ∂condExpKernel μT 𝓕.predictable (t, w), q.1 = t :=
    Measure.ae_ae_of_ae_prod hsame
  filter_upwards [hmain, hsec, hnull', hsame', ae_restrict_mem measurableSet_Iic]
    with t hmt hst hnt hsamet htT hat
  -- fixed-time side: the kernel integral of the section is the kernel mass of `A`
  have hsecA : (fun y ↦ (UA : ℝ≥0 × W → ℝ) (t, y)) =ᵐ[P]
      fun y ↦ A.indicator (1 : W → ℝ) y := by
    refine hst.trans (Filter.Eventually.of_forall fun y ↦ ?_)
    by_cases hy : y ∈ A <;> simp [Set.indicator, hy, htT]
  have hker := integral_condExpKernel_congr_ae (μ := P) (𝓕.le t) hsecA
  filter_upwards [hmt hat, hnt, hsamet, hker] with w hw1 hw2 hw3 hw4
  -- convert the fixed-time side
  have hRHS : ∫ y, (UA : ℝ≥0 × W → ℝ) (t, y) ∂condExpKernel P (𝓕 t) w
      = (condExpKernel P (𝓕 t) w).real A := by
    rw [hw4, integral_indicator_one hA]
  -- convert the predictable side
  have hLHS : ∫ y, (UA : ℝ≥0 × W → ℝ) (t, y)
      ∂predictableSectionKernel μT 𝓕 (t, w)
      = (predictableSectionKernel μT 𝓕 (t, w)).real A := by
    have hstep1 : ∫ y, (UA : ℝ≥0 × W → ℝ) (t, y)
        ∂predictableSectionKernel μT 𝓕 (t, w)
        = ∫ q, (UA : ℝ≥0 × W → ℝ) (t, q.2) ∂condExpKernel μT 𝓕.predictable (t, w) := by
      rw [predictableSectionKernel, Kernel.map_apply _ measurable_snd]
      exact integral_map measurable_snd.aemeasurable
        ((Lp.stronglyMeasurable UA).comp_measurable
          (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    rw [hstep1]
    have hcongr : ∫ q, (UA : ℝ≥0 × W → ℝ) (t, q.2)
        ∂condExpKernel μT 𝓕.predictable (t, w)
        = ∫ q, A.indicator (fun _ ↦ (1 : ℝ)) q.2
          ∂condExpKernel μT 𝓕.predictable (t, w) := by
      apply integral_congr_ae
      have hNzero : condExpKernel μT 𝓕.predictable (t, w) {q | q ∈ N} = 0 := hw2
      have hNae : ∀ᵐ q ∂condExpKernel μT 𝓕.predictable (t, w), q ∉ N := by
        rw [ae_iff]
        simpa using hNzero
      filter_upwards [hw3, hNae] with q hq1 hq2
      have hqval : (UA : ℝ≥0 × W → ℝ) q
          = (Set.Iic T ×ˢ A).indicator (fun _ ↦ (1 : ℝ)) q := by
        by_contra hne
        exact hq2 (hNsub hne)
      have : (UA : ℝ≥0 × W → ℝ) (t, q.2) = (UA : ℝ≥0 × W → ℝ) q := by
        congr 1
        exact Prod.ext hq1.symm rfl
      rw [this, hqval]
      by_cases hy : q.2 ∈ A
      · have hqmem : q ∈ Set.Iic T ×ˢ A := ⟨hq1 ▸ htT, hy⟩
        simp only [Set.indicator_of_mem hqmem, Set.indicator_of_mem hy]
      · have hqmem : q ∉ Set.Iic T ×ˢ A := fun hmem ↦ hy hmem.2
        simp only [Set.indicator_of_notMem hqmem, Set.indicator_of_notMem hy]
    rw [hcongr]
    have hint : ∫ q, A.indicator (fun _ ↦ (1 : ℝ)) q.2
        ∂condExpKernel μT 𝓕.predictable (t, w)
        = (condExpKernel μT 𝓕.predictable (t, w)).real (Prod.snd ⁻¹' A) := by
      have hfun : (fun q : ℝ≥0 × W ↦ A.indicator (fun _ ↦ (1 : ℝ)) q.2)
          = fun q ↦ (Prod.snd ⁻¹' A).indicator (1 : ℝ≥0 × W → ℝ) q := by
        funext q
        by_cases hy : q.2 ∈ A <;> simp [Set.indicator, hy]
      rw [hfun, integral_indicator_one (measurable_snd hA)]
    rw [hint, predictableSectionKernel, Kernel.map_apply _ measurable_snd]
    unfold Measure.real
    rw [Measure.map_apply measurable_snd hA]
  -- conclude: equal real masses of finite measures
  have hreal : (predictableSectionKernel μT 𝓕 (t, w)).real A
      = (condExpKernel P (𝓕 t) w).real A := by
    rw [← hLHS, ← hRHS, hw1]
  have hne1 : predictableSectionKernel μT 𝓕 (t, w) A ≠ ∞ := by
    rw [predictableSectionKernel, Kernel.map_apply' _ measurable_snd _ hA]
    exact measure_ne_top _ _
  have hne2 : condExpKernel P (𝓕 t) w A ≠ ∞ := measure_ne_top _ _
  unfold Measure.real at hreal
  exact (ENNReal.toReal_eq_toReal_iff' hne1 hne2).mp hreal

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
  [SecondCountableTopology W] in
/-- A finite measure and another measure on `W` agreeing on the rational sub-level sets of a
measurable embedding into `ℝ`, and on `univ`, are equal. -/
theorem measure_ext_of_measurableEmbedding_Iic_rat {μ₁ μ₂ : Measure W} {f : W → ℝ}
    (hf : MeasurableEmbedding f) [IsFiniteMeasure μ₁]
    (h : ∀ q : ℚ, μ₁ (f ⁻¹' Set.Iic (q : ℝ)) = μ₂ (f ⁻¹' Set.Iic (q : ℝ)))
    (huniv : μ₁ Set.univ = μ₂ Set.univ) : μ₁ = μ₂ := by
  have hmap : μ₁.map f = μ₂.map f := by
    have h1 : IsFiniteMeasure (μ₁.map f) := by
      refine ⟨?_⟩
      rw [Measure.map_apply hf.measurable MeasurableSet.univ]
      exact measure_lt_top _ _
    refine ext_of_generate_finite _ Real.borel_eq_generateFrom_Iic_rat
      Real.isPiSystem_Iic_rat ?_ ?_
    · intro s hs
      simp only [Set.mem_iUnion, Set.mem_singleton_iff] at hs
      obtain ⟨q, rfl⟩ := hs
      rw [Measure.map_apply hf.measurable measurableSet_Iic,
        Measure.map_apply hf.measurable measurableSet_Iic]
      exact h q
    · rw [Measure.map_apply hf.measurable MeasurableSet.univ,
        Measure.map_apply hf.measurable MeasurableSet.univ]
      simpa using huniv
  ext A hA
  have h1 : μ₁ A = (μ₁.map f) (f '' A) := by
    rw [Measure.map_apply hf.measurable (hf.measurableSet_image' hA),
      hf.injective.preimage_image]
  have h2 : μ₂ A = (μ₂.map f) (f '' A) := by
    rw [Measure.map_apply hf.measurable (hf.measurableSet_image' hA),
      hf.injective.preimage_image]
  rw [h1, h2, hmap]

/-- **The predictable-section kernel IS the fixed-time conditional kernel**: for the natural
Brownian filtration, for almost every `t ∈ [0, T]` with `t > 0` and almost every `w`, the two
kernels agree as measures:

  `predictableSectionKernel (finiteHorizonProductMeasure P T) 𝓕 (t, w)
     = condExpKernel P (𝓕 t) w`. -/
theorem predictableSectionKernel_ae_eq_condExpKernel
    (hB : IsPreBrownianReal B P) (hm : ∀ s, StronglyMeasurable (B s))
    (hgen : IsWienerGenerated B) (T : ℝ≥0) :
    ∀ᵐ t ∂finiteHorizonTimeMeasure T, 0 < t →
      ∀ᵐ w ∂P,
        predictableSectionKernel (finiteHorizonProductMeasure P T)
            (Filtration.natural B hm) (t, w)
          = condExpKernel P (Filtration.natural B hm t) w := by
  set 𝓕 := Filtration.natural B hm with h𝓕
  obtain ⟨f, hf⟩ := exists_measurableEmbedding_real (α := W)
  have hall : ∀ q : ℚ, ∀ᵐ t ∂finiteHorizonTimeMeasure T, 0 < t → ∀ᵐ w ∂P,
      predictableSectionKernel (finiteHorizonProductMeasure P T) 𝓕 (t, w)
          (f ⁻¹' Set.Iic (q : ℝ))
        = condExpKernel P (𝓕 t) w (f ⁻¹' Set.Iic (q : ℝ)) := fun q ↦
    predictableSectionKernel_ae_eq_condExpKernel_apply hB hm hgen T
      (hf.measurable measurableSet_Iic)
  have huniv := predictableSectionKernel_ae_eq_condExpKernel_apply hB hm hgen T
    (MeasurableSet.univ (α := W))
  have hall' := ae_all_iff.mpr hall
  filter_upwards [hall', huniv] with t ht hu hat
  have hq : ∀ᵐ w ∂P, ∀ q : ℚ,
      predictableSectionKernel (finiteHorizonProductMeasure P T) 𝓕 (t, w)
          (f ⁻¹' Set.Iic (q : ℝ))
        = condExpKernel P (𝓕 t) w (f ⁻¹' Set.Iic (q : ℝ)) :=
    ae_all_iff.mpr fun q ↦ ht q hat
  filter_upwards [hq, hu hat] with w hwq hwu
  have hfin1 : IsFiniteMeasure
      (predictableSectionKernel (finiteHorizonProductMeasure P T) 𝓕 (t, w)) := by
    refine ⟨?_⟩
    rw [hwu]
    exact measure_lt_top _ _
  exact measure_ext_of_measurableEmbedding_Iic_rat hf hwq hwu

/-- **Horizon consistency**: the predictable-section kernels for two horizons agree on the
smaller one, almost every time and almost surely — both are the fixed-time kernel. -/
theorem predictableSectionKernel_horizon_consistent
    (hB : IsPreBrownianReal B P) (hm : ∀ s, StronglyMeasurable (B s))
    (hgen : IsWienerGenerated B) {T₁ T₂ : ℝ≥0} (h : T₁ ≤ T₂) :
    ∀ᵐ t ∂finiteHorizonTimeMeasure T₁, 0 < t →
      ∀ᵐ w ∂P,
        predictableSectionKernel (finiteHorizonProductMeasure P T₁)
            (Filtration.natural B hm) (t, w)
          = predictableSectionKernel (finiteHorizonProductMeasure P T₂)
              (Filtration.natural B hm) (t, w) := by
  have hle : finiteHorizonTimeMeasure T₁ ≤ finiteHorizonTimeMeasure T₂ := by
    unfold finiteHorizonTimeMeasure
    exact Measure.restrict_mono (Set.Iic_subset_Iic.mpr h) le_rfl
  have h1 := predictableSectionKernel_ae_eq_condExpKernel hB hm hgen T₁
  have h2 : ∀ᵐ t ∂finiteHorizonTimeMeasure T₁, 0 < t →
      ∀ᵐ w ∂P,
        predictableSectionKernel (finiteHorizonProductMeasure P T₂)
            (Filtration.natural B hm) (t, w)
          = condExpKernel P (Filtration.natural B hm t) w :=
    ae_mono hle (predictableSectionKernel_ae_eq_condExpKernel hB hm hgen T₂)
  filter_upwards [h1, h2] with t ht1 ht2 hat
  filter_upwards [ht1 hat, ht2 hat] with w hw1 hw2
  rw [hw1, hw2]

/-! ### A single global kernel -/

/-- The ceiling-selected kernel map, written as an explicit composition through the horizon
index `⌈t⌉₊`. -/
noncomputable def globalPredictableSectionKernelFun (P : Measure W) [IsGaussian P]
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) : ℝ≥0 × W → Measure W :=
  (fun q : ℕ × (ℝ≥0 × W) ↦
      predictableSectionKernel (finiteHorizonProductMeasure P (q.1 : ℝ≥0)) 𝓕 q.2)
    ∘ fun p ↦ ((⌈p.1⌉₊ : ℕ), p)

/-- Joint predictable measurability of the ceiling-selected kernel map. -/
theorem measurable_globalPredictableSectionKernelFun (P : Measure W) [IsGaussian P]
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) :
    @Measurable (ℝ≥0 × W) (Measure W) 𝓕.predictable inferInstance
      (globalPredictableSectionKernelFun P 𝓕) := by
  have h2 : @Measurable (ℕ × (ℝ≥0 × W)) (Measure W)
      (@Prod.instMeasurableSpace ℕ (ℝ≥0 × W) inferInstance 𝓕.predictable) inferInstance
      (fun q ↦ predictableSectionKernel (finiteHorizonProductMeasure P (q.1 : ℝ≥0)) 𝓕 q.2) :=
    measurable_from_prod_countable_right
      fun n ↦ (predictableSectionKernel (finiteHorizonProductMeasure P (n : ℝ≥0)) 𝓕).measurable
  have h1 : @Measurable (ℝ≥0 × W) (ℕ × (ℝ≥0 × W)) 𝓕.predictable
      (@Prod.instMeasurableSpace ℕ (ℝ≥0 × W) inferInstance 𝓕.predictable)
      (fun p ↦ ((⌈p.1⌉₊ : ℕ), p)) :=
    (Measurable.comp Nat.measurable_ceil (measurable_fst_predictable 𝓕)).prodMk measurable_id
  exact h2.comp h1

/-- **The global predictable-section kernel**: at time `t`, select the finite-horizon kernel
with horizon `⌈t⌉₊`, giving a single jointly predictable kernel on all of `ℝ≥0 × W`. -/
noncomputable def globalPredictableSectionKernel (P : Measure W) [IsGaussian P]
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) :
    @Kernel (ℝ≥0 × W) W 𝓕.predictable inferInstance :=
  @Kernel.mk (ℝ≥0 × W) W 𝓕.predictable inferInstance
    (globalPredictableSectionKernelFun P 𝓕)
    (measurable_globalPredictableSectionKernelFun P 𝓕)

/-- At `(t, w)`, the global kernel is the finite-horizon predictable-section kernel selected
at horizon `⌈t⌉₊`. -/
@[simp]
theorem globalPredictableSectionKernel_apply (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›)
    (p : ℝ≥0 × W) :
    globalPredictableSectionKernel P 𝓕 p =
      predictableSectionKernel (finiteHorizonProductMeasure P ((⌈p.1⌉₊ : ℕ) : ℝ≥0)) 𝓕 p := rfl

/-- The ceiling-selected global predictable-section kernel is a Markov kernel. -/
instance instIsMarkovKernelGlobalPredictableSectionKernel
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) :
    IsMarkovKernel (globalPredictableSectionKernel P 𝓕) := by
  constructor
  intro p
  rw [globalPredictableSectionKernel_apply]
  exact IsMarkovKernel.isProbabilityMeasure p

/-- **Global identification, horizon-free**: for the natural Brownian filtration, for almost
every `t > 0` and almost every `w`, the single jointly predictable Markov kernel
`globalPredictableSectionKernel` is the fixed-time conditional kernel:

  `globalPredictableSectionKernel P 𝓕 (t, w) = condExpKernel P (𝓕 t) w`. -/
theorem globalPredictableSectionKernel_ae_eq_condExpKernel_of_pos
    (hB : IsPreBrownianReal B P) (hm : ∀ s, StronglyMeasurable (B s))
    (hgen : IsWienerGenerated B) :
    ∀ᵐ t ∂nonnegativeLebesgueMeasure, 0 < t →
      ∀ᵐ w ∂P,
        globalPredictableSectionKernel P (Filtration.natural B hm) (t, w)
          = condExpKernel P (Filtration.natural B hm t) w := by
  have hn : ∀ n : ℕ, ∀ᵐ t ∂nonnegativeLebesgueMeasure, t ∈ Set.Iic ((n : ℕ) : ℝ≥0) →
      0 < t → ∀ᵐ w ∂P,
        predictableSectionKernel (finiteHorizonProductMeasure P ((n : ℕ) : ℝ≥0))
            (Filtration.natural B hm) (t, w)
          = condExpKernel P (Filtration.natural B hm t) w := fun n ↦
    ae_imp_of_ae_restrict
      (predictableSectionKernel_ae_eq_condExpKernel hB hm hgen ((n : ℕ) : ℝ≥0))
  have hall := ae_all_iff.mpr hn
  filter_upwards [hall] with t ht hat
  have hceil : t ≤ ((⌈t⌉₊ : ℕ) : ℝ≥0) := Nat.le_ceil t
  have hkey := ht ⌈t⌉₊ (Set.mem_Iic.mpr hceil) hat
  filter_upwards [hkey] with w hw
  rw [globalPredictableSectionKernel_apply]
  exact hw

/-- Guard-free form of the global identification: for almost every time and almost every
sample, the global predictable-section kernel is the fixed-time conditional kernel. -/
theorem globalPredictableSectionKernel_ae_eq_condExpKernel
    (hB : IsPreBrownianReal B P) (hm : ∀ s, StronglyMeasurable (B s))
    (hgen : IsWienerGenerated B) :
    ∀ᵐ t ∂nonnegativeLebesgueMeasure,
      ∀ᵐ w ∂P,
        globalPredictableSectionKernel P (Filtration.natural B hm) (t, w)
          = condExpKernel P (Filtration.natural B hm t) w := by
  filter_upwards [globalPredictableSectionKernel_ae_eq_condExpKernel_of_pos hB hm hgen,
    nonnegativeLebesgueMeasure.ae_ne 0] with t ht ht0
  exact ht (pos_iff_ne_zero.mpr ht0)

/-- Integrating time sections against the global kernel is jointly predictable. -/
theorem stronglyMeasurable_integral_globalPredictableSectionKernel
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) (U : TimeProcessL2 P) :
    StronglyMeasurable[𝓕.predictable]
      (fun p ↦ ∫ y, U (p.1, y) ∂globalPredictableSectionKernel P 𝓕 p) := by
  exact StronglyMeasurable.integral_kernel_prod_right'
    (κ := globalPredictableSectionKernel P 𝓕)
    ((Lp.stronglyMeasurable U).comp_measurable
      (((measurable_fst_predictable 𝓕).comp measurable_fst).prodMk measurable_snd))

/-- On each finite horizon, the two jointly predictable kernel-integral functions — through the
horizon kernel and through the global kernel — agree almost everywhere for the product
measure. -/
theorem integral_predictableSectionKernel_ae_eq_integral_globalPredictableSectionKernel_Iic
    (hB : IsPreBrownianReal B P) (hm : ∀ s, StronglyMeasurable (B s))
    (hgen : IsWienerGenerated B) (U : TimeProcessL2 P) (T : ℝ≥0) :
    (fun p ↦ ∫ y, U (p.1, y)
        ∂predictableSectionKernel (finiteHorizonProductMeasure P T)
          (Filtration.natural B hm) p)
      =ᵐ[finiteHorizonProductMeasure P T]
    fun p ↦ ∫ y, U (p.1, y)
        ∂globalPredictableSectionKernel P (Filtration.natural B hm) p := by
  set 𝓕 := Filtration.natural B hm with h𝓕
  -- both functions are product measurable
  have hm1 : Measurable (fun p ↦ ∫ y, U (p.1, y)
      ∂predictableSectionKernel (finiteHorizonProductMeasure P T) 𝓕 p) :=
    ((StronglyMeasurable.integral_kernel_prod_right'
      (κ := predictableSectionKernel (finiteHorizonProductMeasure P T) 𝓕)
      ((Lp.stronglyMeasurable U).comp_measurable
        (((measurable_fst_predictable 𝓕).comp measurable_fst).prodMk measurable_snd))).mono
      (predictable_le_prod 𝓕)).measurable
  have hm2 : Measurable (fun p ↦ ∫ y, U (p.1, y)
      ∂globalPredictableSectionKernel P 𝓕 p) :=
    ((stronglyMeasurable_integral_globalPredictableSectionKernel 𝓕 U).mono
      (predictable_le_prod 𝓕)).measurable
  have hE : MeasurableSet {p : ℝ≥0 × W |
      (∫ y, U (p.1, y) ∂predictableSectionKernel (finiteHorizonProductMeasure P T) 𝓕 p)
        ≠ ∫ y, U (p.1, y) ∂globalPredictableSectionKernel P 𝓕 p} :=
    (measurableSet_eq_fun hm1 hm2).compl
  -- almost every time, almost every sample the kernels agree
  have hker1 := predictableSectionKernel_ae_eq_condExpKernel hB hm hgen T
  have hker2 : ∀ᵐ t ∂finiteHorizonTimeMeasure T, 0 < t → ∀ᵐ w ∂P,
      globalPredictableSectionKernel P 𝓕 (t, w) = condExpKernel P (𝓕 t) w :=
    ae_restrict_of_ae (globalPredictableSectionKernel_ae_eq_condExpKernel_of_pos hB hm hgen)
  rw [Filter.EventuallyEq, ae_iff]
  change ((finiteHorizonTimeMeasure T).prod P) _ = 0
  apply Measure.measure_prod_null_of_ae_null hE
  filter_upwards [hker1, hker2, ae_pos_finiteHorizonTimeMeasure T] with t h1 h2 hat
  have hsec : ∀ᵐ w ∂P,
      (∫ y, U (t, y) ∂predictableSectionKernel (finiteHorizonProductMeasure P T) 𝓕 (t, w))
        = ∫ y, U (t, y) ∂globalPredictableSectionKernel P 𝓕 (t, w) := by
    filter_upwards [h1 hat, h2 hat] with w hw1 hw2
    rw [hw1, hw2]
  rw [ae_iff] at hsec
  exact hsec

/-- **The global textbook formula for the predictable projection**: on the whole nonnegative
time axis, almost everywhere for the product measure, the product-`L²` predictable projection is
the integral of the time section against the single jointly predictable Markov kernel:

  `Π U (t, ω) = ∫ y, U (t, y) ∂globalPredictableSectionKernel P 𝓕 (t, ω)`. -/
theorem predictableProjection_ae_eq_integral_globalPredictableSectionKernel
    (hB : IsPreBrownianReal B P) (hm : ∀ s, StronglyMeasurable (B s))
    (hgen : IsWienerGenerated B) (U : TimeProcessL2 P) :
    (predictableProjection (Filtration.natural B hm) U : ℝ≥0 × W → ℝ)
      =ᵐ[nonnegativeLebesgueMeasure.prod P]
        fun p ↦ ∫ y, U (p.1, y)
          ∂globalPredictableSectionKernel P (Filtration.natural B hm) p := by
  set 𝓕 := Filtration.natural B hm with h𝓕
  -- almost everywhere on each horizon
  have hn : ∀ n : ℕ,
      (predictableProjection 𝓕 U : ℝ≥0 × W → ℝ)
        =ᵐ[finiteHorizonProductMeasure P ((n : ℕ) : ℝ≥0)]
      fun p ↦ ∫ y, U (p.1, y) ∂globalPredictableSectionKernel P 𝓕 p := fun n ↦
    (predictableProjection_ae_eq_integral_predictableSectionKernel_Iic 𝓕 U ((n : ℕ) : ℝ≥0)).trans
      (integral_predictableSectionKernel_ae_eq_integral_globalPredictableSectionKernel_Iic
        hB hm hgen U ((n : ℕ) : ℝ≥0))
  -- pass from all finite horizons to the full time axis
  rw [Filter.EventuallyEq, ae_iff]
  set S := {p : ℝ≥0 × W | ¬(predictableProjection 𝓕 U : ℝ≥0 × W → ℝ) p
      = ∫ y, U (p.1, y) ∂globalPredictableSectionKernel P 𝓕 p} with hS
  have hcover : S ⊆ ⋃ n : ℕ, S ∩ (Set.Iic ((n : ℕ) : ℝ≥0) ×ˢ Set.univ) := by
    intro p hp
    obtain ⟨n, hn'⟩ := exists_nat_ge p.1
    exact Set.mem_iUnion.mpr ⟨n, hp, Set.mem_Iic.mpr hn', Set.mem_univ _⟩
  refine le_antisymm (le_trans (measure_mono hcover) (le_trans (measure_iUnion_le _) ?_)) bot_le
  have hzero : ∀ n : ℕ,
      (nonnegativeLebesgueMeasure.prod P) (S ∩ (Set.Iic ((n : ℕ) : ℝ≥0) ×ˢ Set.univ)) = 0 := by
    intro n
    have hres := hn n
    rw [Filter.EventuallyEq, ae_iff] at hres
    rw [finiteHorizonProductMeasure_eq_restrict,
      Measure.restrict_apply' (measurableSet_Iic.prod MeasurableSet.univ)] at hres
    exact hres
  simp only [hzero, tsum_zero, Std.le_refl]

/-- The global-kernel integral of a process is square integrable, being almost everywhere the
predictable projection. -/
theorem memLp_integral_globalPredictableSectionKernel
    (hB : IsPreBrownianReal B P) (hm : ∀ s, StronglyMeasurable (B s))
    (hgen : IsWienerGenerated B) (U : TimeProcessL2 P) :
    MemLp (fun p ↦ ∫ y, U (p.1, y)
        ∂globalPredictableSectionKernel P (Filtration.natural B hm) p) 2
      (nonnegativeLebesgueMeasure.prod P) :=
  (Lp.memLp (predictableProjection (Filtration.natural B hm) U : TimeProcessL2 P)).ae_eq
    (predictableProjection_ae_eq_integral_globalPredictableSectionKernel hB hm hgen U)

/-- **The kernel operator is the projection**, at the level of `L²` classes: the class of the
global-kernel integral of `U` is exactly `predictableProjection 𝓕 U`. -/
theorem toLp_integral_globalPredictableSectionKernel
    (hB : IsPreBrownianReal B P) (hm : ∀ s, StronglyMeasurable (B s))
    (hgen : IsWienerGenerated B) (U : TimeProcessL2 P) :
    (memLp_integral_globalPredictableSectionKernel hB hm hgen U).toLp _
      = (predictableProjection (Filtration.natural B hm) U : TimeProcessL2 P) := by
  apply Lp.ext
  refine (MemLp.coeFn_toLp _).trans ?_
  exact (predictableProjection_ae_eq_integral_globalPredictableSectionKernel hB hm hgen U).symm

section ClarkOcone

/-- **The Clark--Ocone integrand through one kernel**: for any Clark--Ocone family, the
integrand `predictableDerivative C F` is, almost everywhere for the product measure, the
integral of the time section of the Malliavin time derivative against the single jointly
predictable Markov kernel:

  `(Dₜ F)_pred (t, ω) = ∫ y, (Dₜ F) (t, y) ∂globalPredictableSectionKernel P 𝓕 (t, ω)`. -/
theorem ClarkOconeFamily.predictableDerivative_ae_eq_integral_globalPredictableSectionKernel
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›} (C : ClarkOconeFamily B P 𝓕) (F : D12 P) :
    (predictableDerivative C F : ℝ≥0 × W → ℝ)
      =ᵐ[nonnegativeLebesgueMeasure.prod P]
        fun p ↦ ∫ y, (C.timeDerivative (mderivD12 P F)) (p.1, y)
          ∂globalPredictableSectionKernel P 𝓕 p := by
  have h := predictableProjection_ae_eq_integral_globalPredictableSectionKernel
    C.isPreBrownian C.stronglyMeasurable C.generated (C.timeDerivative (mderivD12 P F))
  rw [← C.naturalFiltration] at h
  exact h

end ClarkOcone

end Malliavin

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
