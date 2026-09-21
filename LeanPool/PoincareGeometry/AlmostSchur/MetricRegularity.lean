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

public import LeanPool.PoincareGeometry.AlmostSchur.GlobalMeasure
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! # Continuity of the actual coordinate metric density -/

@[expose] public noncomputable section
open Bundle Set MeasureTheory
open scoped Manifold ENNReal

namespace AlmostSchur

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M] [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContinuousRiemannianBundle E (TangentSpace I : M → Type _)]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Constant coordinate vectors give continuous local tangent sections. -/
theorem continuousOn_tangentTrivialization_section
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I) → M))
    [e.IsLinear ℝ] (v : E) :
    ContinuousOn (fun x => (⟨x, e.symmL ℝ x v⟩ : TotalSpace E (TangentSpace I)))
      e.baseSet := by
  have h := e.continuousOn_symm.comp
    (continuous_id.prodMk (continuous_const (y := v))).continuousOn
      (fun x hx => mk_mem_prod hx (mem_univ v))
  apply h.congr
  intro x hx
  simp only [e.symmL_apply hx, Function.comp_apply, id_eq]

/-- The coordinate Gram matrix is continuous for a continuous Riemannian
metric; the hypothesis concerns the given fiber inner products. -/
theorem continuousOn_tangentTrivializationGram
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I) → M))
    [e.IsLinear ℝ] (b : Module.Basis ι ℝ E) :
    ContinuousOn (tangentTrivializationGram e b) e.baseSet := by
  apply continuousOn_pi.mpr
  intro i
  apply continuousOn_pi.mpr
  intro j
  exact (continuousOn_tangentTrivialization_section e (b i)).inner_bundle
    (continuousOn_tangentTrivialization_section e (b j))

variable [I.Boundaryless]

/-- The actual metric matrix in a boundaryless chart is continuous on its
target. -/
theorem continuousOn_coordinateMetric (b : Module.Basis ι ℝ E) (c : M) :
    ContinuousOn (coordinateMetric (I := I) b c) (extChartAt I c).target := by
  apply (continuousOn_tangentTrivializationGram
    (trivializationAt E (TangentSpace I) c) b).comp (continuousOn_extChartAt_symm c)
  intro y hy
  change (extChartAt I c).symm y ∈ (chartAt H c).source
  simpa only [extChartAt_source] using (extChartAt I c).map_target hy

/-- Continuity of the positive density used to define the global measure. -/
theorem continuousOn_coordinateDensity (b : Module.Basis ι ℝ E) (c : M) :
    ContinuousOn (fun y => matrixDensity (coordinateMetric (I := I) b c y))
      (extChartAt I c).target := by
  exact Real.continuous_sqrt.comp_continuousOn
    ((continuous_id.matrix_det).comp_continuousOn (continuousOn_coordinateMetric b c))

variable [MeasurableSpace M] [BorelSpace M] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] [Nonempty M] [LindelofSpace M]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]

/-- Compact subsets contained in one chart have finite metric-density mass.
This uses continuity of the actual Riemannian metric, not assumed local
integrability of a density. -/
theorem metricDensityMeasure_compact_chart_lt_top (b : Module.Basis ι ℝ E) (c : M)
    {K : Set M} (hK : IsCompact K) (hmK : MeasurableSet K)
    (hc : K ⊆ (extChartAt I c).source) :
    metricDensityMeasure (I := I) μ b K < ∞ := by
  have hci : IsCompact (extChartAt I c '' K) :=
    hK.image_of_continuousOn ((continuousOn_extChartAt c).mono hc)
  have hsub : extChartAt I c '' K ⊆ (extChartAt I c).target := by
    rintro y ⟨x, hx, rfl⟩
    exact (extChartAt I c).map_source (hc hx)
  have hi : IntegrableOn (fun y => matrixDensity (coordinateMetric (I := I) b c y))
      (extChartAt I c '' K) μ :=
    ((continuousOn_coordinateDensity b c).mono hsub).integrableOn_compact hci
  rw [metricDensityMeasure_apply μ b c hmK hc]
  simp only [chartMetricLIntegral, mul_one]
  apply lt_top_iff_ne_top.mpr
  exact (lintegral_ofReal_ne_top_iff_integrable hi.aestronglyMeasurable
    (Filter.Eventually.of_forall fun _ => Real.sqrt_nonneg _)).mpr hi

/-- The global density measure of a continuous Riemannian metric is locally
finite on a Hausdorff finite-dimensional manifold. -/
theorem metricDensityMeasure_locallyFinite [T2Space M] (b : Module.Basis ι ℝ E) :
    IsLocallyFiniteMeasure (metricDensityMeasure (I := I) (M := M) μ b) := by
  let : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional I
  constructor
  intro x
  obtain ⟨K, hKn, hKsub, hK⟩ := local_compact_nhds
    ((isOpen_extChartAt_source (I := I) x).mem_nhds (mem_extChartAt_source x))
  exact ⟨K, hKn, metricDensityMeasure_compact_chart_lt_top μ b x hK hK.measurableSet hKsub⟩

/-- A continuous Riemannian metric on a compact Hausdorff manifold has finite
total density mass. -/
theorem metricDensityMeasure_univ_lt_top [T2Space M] [CompactSpace M]
    (b : Module.Basis ι ℝ E) : metricDensityMeasure (I := I) (M := M) μ b univ < ∞ := by
  let : IsLocallyFiniteMeasure (metricDensityMeasure (I := I) (M := M) μ b) :=
    metricDensityMeasure_locallyFinite μ b
  exact isCompact_univ.measure_lt_top

/-- Every nonempty open subset contained in a chart has positive mass. -/
theorem metricDensityMeasure_open_chart_pos (b : Module.Basis ι ℝ E) (c : M)
    {s : Set M} (hs : IsOpen s) (hne : s.Nonempty)
    (hc : s ⊆ (extChartAt I c).source) :
    0 < metricDensityMeasure (I := I) μ b s := by
  let t := extChartAt I c '' s
  have ht : IsOpen t :=
    (boundarylessExtChart (I := I) c).isOpen_image_of_subset_source hs hc
  have hsub : t ⊆ (extChartAt I c).target := by
    rintro y ⟨x, hx, rfl⟩
    exact (extChartAt I c).map_source (hc hx)
  have hm := ((continuousOn_coordinateDensity (I := I) b c).mono hsub).aemeasurable
    ht.measurableSet (μ := μ)
  rw [metricDensityMeasure_apply μ b c hs.measurableSet hc]
  simp only [chartMetricLIntegral, mul_one]
  apply pos_iff_ne_zero.mpr
  intro hz
  have he := (setLIntegral_eq_zero_iff' ht.measurableSet hm.ennreal_ofReal).mp hz
  have hn : ∀ᵐ y ∂μ, y ∉ t := he.mono fun y hy hyt =>
    (ne_of_gt (ENNReal.ofReal_pos.mpr (coordinateMetric_density_pos b c y (hsub hyt))))
      (hy hyt)
  have hz' : μ t = 0 := by simpa [ae_iff] using hn
  exact (ht.measure_pos (μ := μ) (hne.image _)).ne' hz'

/-- The global measure assigns positive mass to every nonempty open set. -/
theorem metricDensityMeasure_open_pos (b : Module.Basis ι ℝ E)
    {s : Set M} (hs : IsOpen s) (hne : s.Nonempty) :
    0 < metricDensityMeasure (I := I) μ b s := by
  obtain ⟨x, hx⟩ := hne
  exact (metricDensityMeasure_open_chart_pos μ b x
    (hs.inter (isOpen_extChartAt_source x))
    ⟨x, hx, mem_extChartAt_source x⟩ inter_subset_right).trans_le
      (measure_mono inter_subset_left)

/-- A nonempty manifold has strictly positive total metric-density mass. -/
theorem metricDensityMeasure_univ_pos (b : Module.Basis ι ℝ E) :
    0 < metricDensityMeasure (I := I) (M := M) μ b univ :=
  metricDensityMeasure_open_pos μ b isOpen_univ Set.univ_nonempty

end AlmostSchur
