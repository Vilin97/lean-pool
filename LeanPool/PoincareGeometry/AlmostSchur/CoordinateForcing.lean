/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.AlmostSchur.ChartLpRegularity
public import LeanPool.PoincareGeometry.AlmostSchur.MetricRegularity

/-! # Actual density-weighted local forcing

An actual-volume L² datum remains L² after chart pullback and multiplication
by the coordinate density on every compact chart subset.
-/

@[expose] public noncomputable section
open Bundle Set MeasureTheory Metric
open scoped Manifold ContDiff Topology

namespace AlmostSchur

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M] [I.Boundaryless]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContinuousRiemannianBundle E (TangentSpace I : M → Type _)]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M] [LindelofSpace M]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem memLp_density_chart_comp_on_compact (b : Module.Basis ι ℝ E) (c : M)
    {K : Set E} (hK : IsCompact K) (hKt : K ⊆ (extChartAt I c).target)
    (h : Lp ℝ 2 (riemannianVolume (I := I))) :
    MemLp (fun z => matrixDensity (coordinateMetric (I := I) b c z) *
      h ((extChartAt I c).symm z)) 2 ((volume : Measure E).restrict K) := by
  have hp := memLp_chart_comp_on_compact c hK hKt h
  have hd := (continuousOn_coordinateDensity (I := I) b c).mono hKt
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hd
  apply hp.of_le_mul (c := C) (hd.aestronglyMeasurable hK.measurableSet |>.mul hp.aestronglyMeasurable)
  filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
  simp only [Pi.mul_apply, Function.comp_apply, norm_mul]
  exact mul_le_mul_of_nonneg_right (hC z hz) (norm_nonneg _)

theorem integrableOn_density_chart_comp_on_compact (b : Module.Basis ι ℝ E) (c : M)
    {K : Set E} (hK : IsCompact K) (hKt : K ⊆ (extChartAt I c).target)
    (h : Lp ℝ 2 (riemannianVolume (I := I))) :
    IntegrableOn (fun z => matrixDensity (coordinateMetric (I := I) b c z) *
      h ((extChartAt I c).symm z)) K volume := by
  let : IsFiniteMeasure ((volume : Measure E).restrict K) :=
    isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  exact (memLp_density_chart_comp_on_compact b c hK hKt h).integrable (by norm_num)

theorem locallyIntegrableOn_density_chart_comp (b : Module.Basis ι ℝ E) (c : M)
    (h : Lp ℝ 2 (riemannianVolume (I := I))) :
    LocallyIntegrableOn (fun z => matrixDensity (coordinateMetric (I := I) b c z) *
      h ((extChartAt I c).symm z)) (extChartAt I c).target volume := by
  intro z hz
  obtain ⟨d, hd, hdT⟩ := Metric.isOpen_iff.mp (isOpen_extChartAt_target (I := I) c) z hz
  have hK : closedBall z (d / 2) ⊆ (extChartAt I c).target :=
    (closedBall_subset_ball (by linarith : d / 2 < d)).trans hdT
  refine ⟨closedBall z (d / 2), nhdsWithin_le_nhds (closedBall_mem_nhds z (by positivity)), ?_⟩
  exact integrableOn_density_chart_comp_on_compact b c (isCompact_closedBall _ _) hK h

end AlmostSchur
