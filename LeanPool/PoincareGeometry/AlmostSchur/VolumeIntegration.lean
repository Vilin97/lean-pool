/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

module

public import LeanPool.PoincareGeometry.AlmostSchur.NormalizedMeasure
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # Integrating against the constructed Riemannian volume -/

@[expose] public noncomputable section
open Bundle Set MeasureTheory
open scoped Manifold ENNReal

namespace AlmostSchur

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*} [Fintype ι] [DecidableEq ι]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M] [I.Boundaryless]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [MeasurableSpace M] [BorelSpace M]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]

/-- The chart measure integral is the pullback of the weighted coordinate
measure, without an integrability assumption. -/
theorem integral_chartMetricMeasure (b : Module.Basis ι ℝ E) (c : M) (f : M → ℝ) :
    ∫ x, f x ∂chartMetricMeasure (I := I) μ b c =
      ∫ y in (extChartAt I c).target, f ((extChartAt I c).symm y)
        ∂μ.withDensity (fun y => ENNReal.ofReal
          (matrixDensity (coordinateMetric (I := I) b c y))) := by
  let e := boundarylessExtChart (I := I) c
  let ν := μ.withDensity (fun y => ENNReal.ofReal
    (matrixDensity (coordinateMetric (I := I) b c y)))
  have he := e.isOpenEmbedding_restrict.measurableEmbedding
  have hr : Set.range (e.source.domRestrict e) = (extChartAt I c).target := by
    ext y
    constructor
    · rintro ⟨⟨x, hx⟩, rfl⟩
      exact (extChartAt I c).map_source hx
    · intro hy
      exact ⟨⟨(extChartAt I c).symm y, (extChartAt I c).map_target hy⟩,
        (extChartAt I c).right_inv hy⟩
  have h := he.integral_map (μ := ν.comap (e.source.domRestrict e))
    (fun y => f ((extChartAt I c).symm y))
  rw [he.map_comap, hr] at h
  unfold chartMetricMeasure
  rw [(MeasurableEmbedding.subtype_coe e.open_source.measurableSet).integral_map]
  change (∫ x : e.source, f x ∂ν.comap (e.source.domRestrict e)) = _
  rw [h]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    change f x.val = f ((extChartAt I c).symm (extChartAt I c x.val))
    rw [(extChartAt I c).left_inv x.property]

variable [IsContinuousRiemannianBundle E (TangentSpace I : M → Type _)]

/-- For the continuous actual metric, the chart measure integral equals the
usual real-valued metric-density integral. -/
theorem integral_chartMetricMeasure_density (b : Module.Basis ι ℝ E) (c : M) (f : M → ℝ) :
    ∫ x, f x ∂chartMetricMeasure (I := I) μ b c =
      ∫ y in (extChartAt I c).target,
        matrixDensity (coordinateMetric (I := I) b c y) * f ((extChartAt I c).symm y) ∂μ := by
  rw [integral_chartMetricMeasure]
  rw [setIntegral_withDensity_eq_setIntegral_toReal_smul₀
    ((continuousOn_coordinateDensity b c).aemeasurable
      (isOpen_extChartAt_target c).measurableSet).ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)
    _ (isOpen_extChartAt_target c).measurableSet]
  simp only [matrixDensity, ENNReal.toReal_ofReal (Real.sqrt_nonneg _), smul_eq_mul]

/-- On any measurable chart subset, integration against the chart measure
is exactly the previously constructed chart integral. -/
theorem setIntegral_chartMetricMeasure (b : Module.Basis ι ℝ E) (c : M)
    {s : Set M} (hs : MeasurableSet s) (hc : s ⊆ (extChartAt I c).source) (f : M → ℝ) :
    ∫ x in s, f x ∂chartMetricMeasure (I := I) μ b c =
      chartMetricIntegral (I := I) μ b c s f := by
  have hm := measurableSet_extChartAt_image (I := I) c hs hc
  have hsub : extChartAt I c '' s ⊆ (extChartAt I c).target := by
    rintro y ⟨x, hx, rfl⟩
    exact (extChartAt I c).map_source (hc hx)
  rw [← integral_indicator hs, integral_chartMetricMeasure_density]
  have heq : ∀ y ∈ (extChartAt I c).target,
      matrixDensity (coordinateMetric (I := I) b c y) * s.indicator f ((extChartAt I c).symm y) =
      (extChartAt I c '' s).indicator (fun z => matrixDensity (coordinateMetric (I := I) b c z) *
        f ((extChartAt I c).symm z)) y := by
    intro y hy
    by_cases hx : (extChartAt I c).symm y ∈ s
    · have hi : y ∈ extChartAt I c '' s :=
        ⟨(extChartAt I c).symm y, hx, (extChartAt I c).right_inv hy⟩
      simp only [Set.indicator_of_mem hx, Set.indicator_of_mem hi]
    · have hi : y ∉ extChartAt I c '' s := by
        rintro ⟨x, hxs, rfl⟩
        exact hx (by rwa [(extChartAt I c).left_inv (hc hxs)])
      simp only [Set.indicator_of_notMem hx, Set.indicator_of_notMem hi, mul_zero]
  rw [setIntegral_congr_fun (isOpen_extChartAt_target c).measurableSet heq,
    setIntegral_indicator hm]
  rw [inter_eq_right.mpr hsub]
  rfl

/-- Integrability with respect to a chart measure is equivalent to
integrability of the density-weighted coordinate function. -/
theorem integrable_chartMetricMeasure_iff (b : Module.Basis ι ℝ E) (c : M) (f : M → ℝ) :
    Integrable f (chartMetricMeasure (I := I) μ b c) ↔
      IntegrableOn (fun y => matrixDensity (coordinateMetric (I := I) b c y) *
        f ((extChartAt I c).symm y)) (extChartAt I c).target μ := by
  let e := boundarylessExtChart (I := I) c
  let ν := μ.withDensity (fun y => ENNReal.ofReal
    (matrixDensity (coordinateMetric (I := I) b c y)))
  have he := e.isOpenEmbedding_restrict.measurableEmbedding
  have hr : Set.range (e.source.domRestrict e) = (extChartAt I c).target := by
    ext y
    constructor
    · rintro ⟨⟨x, hx⟩, rfl⟩
      exact (extChartAt I c).map_source hx
    · intro hy
      exact ⟨⟨(extChartAt I c).symm y, (extChartAt I c).map_target hy⟩,
        (extChartAt I c).right_inv hy⟩
  have h := he.integrable_map_iff (μ := ν.comap (e.source.domRestrict e))
    (g := fun y => f ((extChartAt I c).symm y))
  rw [he.map_comap, hr] at h
  have hf : (fun x : e.source => f ((extChartAt I c).symm (e.source.domRestrict e x))) =
      (fun x : e.source => f x) := by
    funext x
    change f ((extChartAt I c).symm (extChartAt I c x.val)) = f x.val
    rw [(extChartAt I c).left_inv x.property]
  simp only [Function.comp_def] at h
  rw [hf] at h
  unfold chartMetricMeasure
  rw [(MeasurableEmbedding.subtype_coe e.open_source.measurableSet).integrable_map_iff]
  simp only [Function.comp_def]
  rw [← h]
  change Integrable _ (ν.restrict (extChartAt I c).target) ↔ _
  dsimp only [ν]
  rw [restrict_withDensity (isOpen_extChartAt_target c).measurableSet,
    integrable_withDensity_iff_integrable_smul₀'
      ((continuousOn_coordinateDensity b c).aemeasurable
        (isOpen_extChartAt_target c).measurableSet).ennreal_ofReal
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [matrixDensity, ENNReal.toReal_ofReal (Real.sqrt_nonneg _), smul_eq_mul, IntegrableOn]

/-- A chart measure is supported on its chart source. -/
theorem chartMetricMeasure_restrict_source (b : Module.Basis ι ℝ E) (c : M) :
    (chartMetricMeasure (I := I) μ b c).restrict (extChartAt I c).source =
      chartMetricMeasure (I := I) μ b c := by
  let e := boundarylessExtChart (I := I) c
  unfold chartMetricMeasure
  rw [(MeasurableEmbedding.subtype_coe e.open_source.measurableSet).restrict_map]
  have h : (Subtype.val : e.source → M) ⁻¹' (extChartAt I c).source = univ := by
    ext x
    simp only [mem_preimage, mem_univ, iff_true]
    exact x.property
  rw [h, Measure.restrict_univ]

variable [Nonempty M] [LindelofSpace M]

/-- The global metric-density measure computes the same chart integral. -/
theorem setIntegral_metricDensityMeasure (b : Module.Basis ι ℝ E) (c : M)
    {s : Set M} (hs : MeasurableSet s) (hc : s ⊆ (extChartAt I c).source) (f : M → ℝ) :
    ∫ x in s, f x ∂metricDensityMeasure (I := I) μ b =
      chartMetricIntegral (I := I) μ b c s f := by
  have h := congrArg (fun ν : Measure M => ν.restrict s)
    (metricDensityMeasure_restrict (I := I) μ b c)
  simp only [Measure.restrict_restrict_of_subset hc] at h
  change (∫ x, f x ∂(metricDensityMeasure (I := I) μ b).restrict s) = _
  rw [h]
  exact setIntegral_chartMetricMeasure μ b c hs hc f

/-- The chart formula for integration against normalized Riemannian volume. -/
theorem setIntegral_riemannianVolume (b : Module.Basis ι ℝ E) (c : M)
    {s : Set M} (hs : MeasurableSet s) (hc : s ⊆ (extChartAt I c).source) (f : M → ℝ) :
    ∫ x in s, f x ∂riemannianVolume (I := I) =
      chartMetricIntegral (I := I) b.addHaar b c s f := by
  rw [riemannianVolume_eq b]
  exact setIntegral_metricDensityMeasure b.addHaar b c hs hc f

/-- Integrability on a chart for normalized volume is precisely weighted
coordinate integrability. -/
theorem integrableOn_riemannianVolume_chart_iff (b : Module.Basis ι ℝ E) (c : M) (f : M → ℝ) :
    IntegrableOn f (extChartAt I c).source (riemannianVolume (I := I)) ↔
      IntegrableOn (fun y => matrixDensity (coordinateMetric (I := I) b c y) *
        f ((extChartAt I c).symm y)) (extChartAt I c).target b.addHaar := by
  rw [riemannianVolume_eq b]
  unfold IntegrableOn
  rw [metricDensityMeasure_restrict, chartMetricMeasure_restrict_source]
  exact integrable_chartMetricMeasure_iff b.addHaar b c f

end AlmostSchur
