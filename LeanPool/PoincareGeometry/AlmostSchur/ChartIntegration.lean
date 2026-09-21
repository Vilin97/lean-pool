/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.AlmostSchur.ChartMetric
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Integration in actual Riemannian charts

The chart is promoted to an open partial homeomorphism only in the boundaryless
case. Measurability of chart images is proved through its restricted embedding.
-/

@[expose] public noncomputable section
open Bundle Set MeasureTheory
open scoped Manifold ENNReal

namespace AlmostSchur

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M] [I.Boundaryless]

/-- The extended chart is a genuine open partial homeomorphism for a
boundaryless model. -/
def boundarylessExtChart (c : M) : OpenPartialHomeomorph M E :=
  { extChartAt I c with
    open_source := isOpen_extChartAt_source c
    open_target := isOpen_extChartAt_target c
    continuousOn_toFun := continuousOn_extChartAt c
    continuousOn_invFun := continuousOn_extChartAt_symm c }

variable [MeasurableSpace M] [BorelSpace M] [MeasurableSpace E] [BorelSpace E]

omit [IsManifold I 1 M] [I.Boundaryless] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace E] [BorelSpace E] in
/-- Coordinate change carries the coordinate image of an overlap to its image
in the other chart. No openness of the overlap is required. -/
theorem extChartAt_transition_image (c c' : M) {s : Set M}
    (hs : s ⊆ (extChartAt I c).source) :
    (extChartAt I c' ∘ (extChartAt I c).symm) '' (extChartAt I c '' s) =
      extChartAt I c' '' s := by
  ext y
  constructor
  · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, by simp only [Function.comp_apply,
      (extChartAt I c).left_inv (hs hx)]⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨extChartAt I c x, ⟨x, hx, rfl⟩, by
      simp only [Function.comp_apply, (extChartAt I c).left_inv (hs hx)]⟩

omit [IsManifold I 1 M] [I.Boundaryless] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace E] [BorelSpace E] in
/-- Coordinate change is injective on every common chart domain. -/
theorem extChartAt_transition_injOn (c c' : M) {s : Set M}
    (hs : s ⊆ (extChartAt I c).source)
    (hs' : s ⊆ (extChartAt I c').source) :
    InjOn (extChartAt I c' ∘ (extChartAt I c).symm) (extChartAt I c '' s) := by
  rintro y ⟨x, hx, rfl⟩ z ⟨w, hw, rfl⟩ heq
  simp only [Function.comp_apply, (extChartAt I c).left_inv (hs hx),
    (extChartAt I c).left_inv (hs hw)] at heq
  exact congrArg (extChartAt I c) ((extChartAt I c').injOn (hs' hx) (hs' hw) heq)

omit [MeasurableSpace M] [BorelSpace M] [MeasurableSpace E] [BorelSpace E] in
theorem extChartAt_transition_differentiableAt (c c' x : M)
    (hx : x ∈ (extChartAt I c).source)
    (hx' : x ∈ (extChartAt I c').source) :
    DifferentiableAt ℝ (extChartAt I c' ∘ (extChartAt I c).symm) (extChartAt I c x) := by
  have h := I.contDiffWithinAt_extendCoordChange' (n := 1)
    (IsManifold.chart_mem_maximalAtlas c) (IsManifold.chart_mem_maximalAtlas c')
    (by simpa only [extChartAt_source] using hx)
    (by simpa only [extChartAt_source] using hx')
  rw [I.range_eq_univ, contDiffWithinAt_univ] at h
  exact h.differentiableAt (by norm_num)

omit [IsManifold I 1 M] in
theorem measurableSet_extChartAt_image (c : M) {s : Set M}
    (hs : MeasurableSet s) (hsub : s ⊆ (extChartAt I c).source) :
    MeasurableSet (extChartAt I c '' s) := by
  let e := boundarylessExtChart (I := I) c
  have hm := e.isOpenEmbedding_restrict.measurableEmbedding.measurableSet_image'
    (measurable_subtype_coe hs)
  have heq : e.source.domRestrict e '' (Subtype.val ⁻¹' s) = extChartAt I c '' s := by
    ext y
    constructor
    · rintro ⟨⟨x, hx⟩, hxs, rfl⟩
      exact ⟨x, hxs, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hsub hx⟩, hx, rfl⟩
  rwa [heq] at hm

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  [FiniteDimensional ℝ E] [RiemannianBundle (TangentSpace I : M → Type _)]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]

/-- The metric-density integral of a function over a measurable chart domain. -/
def chartMetricIntegral (b : Module.Basis ι ℝ E) (c : M) (s : Set M) (f : M → ℝ) : ℝ :=
  ∫ y in extChartAt I c '' s,
    matrixDensity (coordinateMetric (I := I) b c y) * f ((extChartAt I c).symm y) ∂μ

/-- Local integration for the actual tangent metric is independent of the
chart on a measurable overlap. -/
theorem chartMetricIntegral_eq (b : Module.Basis ι ℝ E) (c c' : M) {s : Set M}
    (hs : MeasurableSet s) (hc : s ⊆ (extChartAt I c).source)
    (hc' : s ⊆ (extChartAt I c').source) (f : M → ℝ) :
    chartMetricIntegral (I := I) μ b c s f = chartMetricIntegral (I := I) μ b c' s f := by
  let F := extChartAt I c' ∘ (extChartAt I c).symm
  have hd : ∀ y ∈ extChartAt I c '' s, DifferentiableAt ℝ F y := by
    rintro y ⟨x, hx, rfl⟩
    exact extChartAt_transition_differentiableAt c c' x (hc hx) (hc' hx)
  have h := integral_image_eq_integral_abs_det_fderiv_smul μ
    (measurableSet_extChartAt_image c hs hc)
    (fun y hy => (hd y hy).hasFDerivAt.hasFDerivWithinAt)
    (extChartAt_transition_injOn c c' hc hc')
    (fun y => matrixDensity (coordinateMetric (I := I) b c' y) *
      f ((extChartAt I c').symm y))
  rw [extChartAt_transition_image c c' hc] at h
  unfold chartMetricIntegral
  rw [h]
  apply setIntegral_congr_fun (measurableSet_extChartAt_image c hs hc)
  rintro y ⟨x, hx, rfl⟩
  have ht := tangentChart_density_transition (I := I) b c c' x
    (by simpa only [extChartAt_source, Set.mem_inter_iff] using And.intro (hc hx) (hc' hx))
  simp only [coordinateMetric, F, Function.comp_apply, (extChartAt I c).left_inv (hc hx),
    (extChartAt I c').left_inv (hc' hx), smul_eq_mul]
  rw [ht, mul_assoc]

/-- Nonnegative metric-density integration, including infinite mass. -/
def chartMetricLIntegral (b : Module.Basis ι ℝ E) (c : M) (s : Set M)
    (f : M → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ y in extChartAt I c '' s,
    ENNReal.ofReal (matrixDensity (coordinateMetric (I := I) b c y)) *
      f ((extChartAt I c).symm y) ∂μ

/-- Chart independence also holds before any finiteness or integrability
assumption, as needed for constructing a measure. -/
theorem chartMetricLIntegral_eq (b : Module.Basis ι ℝ E) (c c' : M) {s : Set M}
    (hs : MeasurableSet s) (hc : s ⊆ (extChartAt I c).source)
    (hc' : s ⊆ (extChartAt I c').source) (f : M → ℝ≥0∞) :
    chartMetricLIntegral (I := I) μ b c s f =
      chartMetricLIntegral (I := I) μ b c' s f := by
  let F := extChartAt I c' ∘ (extChartAt I c).symm
  have hd : ∀ y ∈ extChartAt I c '' s, DifferentiableAt ℝ F y := by
    rintro y ⟨x, hx, rfl⟩
    exact extChartAt_transition_differentiableAt c c' x (hc hx) (hc' hx)
  have h := lintegral_image_eq_lintegral_abs_det_fderiv_mul μ
    (measurableSet_extChartAt_image c hs hc)
    (fun y hy => (hd y hy).hasFDerivAt.hasFDerivWithinAt)
    (extChartAt_transition_injOn c c' hc hc')
    (fun y => ENNReal.ofReal (matrixDensity (coordinateMetric (I := I) b c' y)) *
      f ((extChartAt I c').symm y))
  rw [extChartAt_transition_image c c' hc] at h
  unfold chartMetricLIntegral
  rw [h]
  apply setLIntegral_congr_fun (measurableSet_extChartAt_image c hs hc)
  rintro y ⟨x, hx, rfl⟩
  have ht := tangentChart_density_transition (I := I) b c c' x
    (by simpa only [extChartAt_source, Set.mem_inter_iff] using And.intro (hc hx) (hc' hx))
  simp only [coordinateMetric, F, Function.comp_apply, (extChartAt I c).left_inv (hc hx),
    (extChartAt I c').left_inv (hc' hx)]
  rw [ht, ENNReal.ofReal_mul (abs_nonneg _), mul_assoc]

/-- The Riemannian density measure on one chart, extended by zero off its
source. The restricted chart is a measurable embedding. -/
def chartMetricMeasure (b : Module.Basis ι ℝ E) (c : M) : Measure M :=
  let e := boundarylessExtChart (I := I) c
  Measure.map (Subtype.val : e.source → M)
    ((μ.withDensity fun y => ENNReal.ofReal
      (matrixDensity (coordinateMetric (I := I) b c y))).comap
        (e.source.domRestrict e))

/-- On a measurable subset of its chart, the measure is exactly the
nonnegative integral of the metric density. -/
theorem chartMetricMeasure_apply (b : Module.Basis ι ℝ E) (c : M) {s : Set M}
    (hs : MeasurableSet s) (hc : s ⊆ (extChartAt I c).source) :
    chartMetricMeasure (I := I) μ b c s =
      chartMetricLIntegral (I := I) μ b c s (fun _ => 1) := by
  let e := boundarylessExtChart (I := I) c
  have he := e.isOpenEmbedding_restrict.measurableEmbedding
  have heq : e.source.domRestrict e '' (Subtype.val ⁻¹' s) = extChartAt I c '' s := by
    ext y
    constructor
    · rintro ⟨⟨x, hx⟩, hxs, rfl⟩
      exact ⟨x, hxs, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hc hx⟩, hx, rfl⟩
  unfold chartMetricMeasure
  rw [Measure.map_apply measurable_subtype_coe hs,
    Measure.comap_apply _ he.injective (fun t ht => he.measurableSet_image' ht) _
      (measurable_subtype_coe hs)]
  rw [heq, withDensity_apply _ (measurableSet_extChartAt_image c hs hc)]
  simp only [chartMetricLIntegral, mul_one]

/-- The chart measures agree on every measurable common domain. -/
theorem chartMetricMeasure_apply_eq (b : Module.Basis ι ℝ E) (c c' : M) {s : Set M}
    (hs : MeasurableSet s) (hc : s ⊆ (extChartAt I c).source)
    (hc' : s ⊆ (extChartAt I c').source) :
    chartMetricMeasure (I := I) μ b c s = chartMetricMeasure (I := I) μ b c' s := by
  rw [chartMetricMeasure_apply μ b c hs hc, chartMetricMeasure_apply μ b c' hs hc']
  exact chartMetricLIntegral_eq μ b c c' hs hc hc' _

/-- Compatibility as equality of measures restricted to an overlap, the
gluing condition for a global Riemannian measure. -/
theorem chartMetricMeasure_restrict_eq (b : Module.Basis ι ℝ E) (c c' : M)
    {s : Set M} (hs : MeasurableSet s) (hc : s ⊆ (extChartAt I c).source)
    (hc' : s ⊆ (extChartAt I c').source) :
    (chartMetricMeasure (I := I) μ b c).restrict s =
      (chartMetricMeasure (I := I) μ b c').restrict s := by
  ext t ht
  rw [Measure.restrict_apply ht, Measure.restrict_apply ht]
  exact chartMetricMeasure_apply_eq μ b c c' (ht.inter hs)
    (fun _ hx => hc hx.2) (fun _ hx => hc' hx.2)

end AlmostSchur
