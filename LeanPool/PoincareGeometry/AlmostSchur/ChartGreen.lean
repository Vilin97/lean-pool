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

public import LeanPool.PoincareGeometry.AlmostSchur.ChartFlux
public import LeanPool.PoincareGeometry.AlmostSchur.TorsionCoordinates
public import LeanPool.PoincareGeometry.AlmostSchur.VolumeIntegration

/-!
# Green's formula for a compactly chart-supported tangent field

This transports the coordinate Green identity to the actual connection,
manifold differential and Riemannian chart measure. Metric compatibility and
vanishing torsion are the geometric hypotheses; no differential or integration
identity is assumed.
-/

@[expose] public noncomputable section
open Bundle FiberBundle Set MeasureTheory
open scoped Manifold ContDiff Topology Matrix.Norms.Elementwise

namespace AlmostSchur

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  [MeasurableSpace M] [BorelSpace M]

local notation "TM" => (TangentSpace I : M → Type _)

local instance : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
  continuousRiemannianBundle_of_contMDiff (I := I)

/-- The actual connection is compatible with the coordinate metric throughout
the chart target. -/
theorem coordinateConnection_compatible_on
    (cov : CovariantDerivative I E TM) (hm : tangentMetricCompatible cov)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E) (c : M)
    (z : E) (hz : z ∈ (extChartAt I c).target) :
    localMetricCompatible b (coordinateMetric (I := I) b c)
      (coordinateConnection cov b c) z := by
  have hx : (extChartAt I c).symm z ∈ (chartAt H c).source := by
    simpa only [extChartAt_source] using (extChartAt I c).map_target hz
  simpa only [(extChartAt I c).right_inv hz] using
    coordinateConnection_localMetricCompatible cov hm b c ((extChartAt I c).symm z) hx

/-- Zero torsion gives the coordinate symmetry needed by density divergence. -/
theorem coordinateConnection_symmetric_on
    (cov : CovariantDerivative I E TM) (ht : cov.torsion = 0)
    {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ E) (c : M)
    (z : E) (hz : z ∈ (extChartAt I c).target) (u v : E) :
    coordinateConnection cov b c z u v = coordinateConnection cov b c z v u := by
  apply frameConnectionCoefficients_symmetric cov ht b c ((extChartAt I c).symm z)
  simpa only [extChartAt_source] using (extChartAt I c).map_target hz

/-- Local Green formula expressed entirely with the actual manifold operators
and the constructed Riemannian chart measure. -/
theorem integral_chartMetricMeasure_mul_divergence
    (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    (cov : CovariantDerivative I E TM) (hm : tangentMetricCompatible cov)
    (ht : cov.torsion = 0) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ E) (c : M) (f : M → ℝ) (X : Π x : M, TM x)
    (hf : CMDiff[(chartAt H c).source] 1 f)
    (hX : CMDiff[(chartAt H c).source] 1 (T% X))
    (hc : HasCompactSupport (fun x => ‖X x‖))
    (hs : tsupport (fun x => ‖X x‖) ⊆ (extChartAt I c).source) :
    ∫ x, f x * divergence cov X x ∂chartMetricMeasure (I := I) μ b c =
      -∫ x, mvfderiv I f x (X x) ∂chartMetricMeasure (I := I) μ b c := by
  have hU := isOpen_extChartAt_target (I := I) c
  have hx (z : E) (hz : z ∈ (extChartAt I c).target) :
      (extChartAt I c).symm z ∈ (chartAt H c).source := by
    simpa only [extChartAt_source] using (extChartAt I c).map_target hz
  have hXa (z : E) (hz : z ∈ (extChartAt I c).target) :
      MDiffAt (T% X) ((extChartAt I c).symm z) :=
    ((hX _ (hx z hz)).contMDiffAt ((chartAt H c).open_source.mem_nhds (hx z hz))).mdifferentiableAt
      (by simp)
  have hfa (z : E) (hz : z ∈ (extChartAt I c).target) :
      MDiffAt f ((extChartAt I c).symm z) :=
    ((hf _ (hx z hz)).contMDiffAt ((chartAt H c).open_source.mem_nhds (hx z hz))).mdifferentiableAt
      (by simp)
  have hlocal := setIntegral_mul_localConnectionDivergence_openDomain (ν := μ) hU b
    (coordinateMetric (I := I) b c) (coordinateConnection cov b c)
    (f ∘ (extChartAt I c).symm) (chartFlux (I := I) c X)
    (contDiffOn_coordinateMetric b c) (coordinateMetric_posDef b c)
    (contDiffOn_chart_comp c f hf) (contDiff_chartFlux c X hX hc hs).contDiffOn
    (hasCompactSupport_chartFlux c X hc hs) (tsupport_chartFlux_subset_target c X hc hs)
    (coordinateConnection_compatible_on cov hm b c) (coordinateConnection_symmetric_on cov ht b c)
  rw [integral_chartMetricMeasure μ b c, integral_chartMetricMeasure μ b c]
  have hl : ∀ z ∈ (extChartAt I c).target,
      f ((extChartAt I c).symm z) * divergence cov X ((extChartAt I c).symm z) =
      (f ∘ (extChartAt I c).symm) z *
        localConnectionDivergence (coordinateConnection cov b c) (chartFlux (I := I) c X) z := by
    intro z hz
    rw [divergence_eq_chartFlux cov b c X z hz (hXa z hz)]
    rfl
  have hr : ∀ z ∈ (extChartAt I c).target,
      mvfderiv I f ((extChartAt I c).symm z) (X ((extChartAt I c).symm z)) =
      fderiv ℝ (f ∘ (extChartAt I c).symm) z (chartFlux (I := I) c X z) := by
    intro z hz
    have h := fderiv_chart_coordinateVectorField f X c ((extChartAt I c).symm z)
      (hx z hz) (hfa z hz)
    rw [(extChartAt I c).right_inv hz] at h
    rw [(chartFlux_eventually_eq c X z hz).eq_of_nhds]
    exact h.symm
  rw [setIntegral_congr_fun hU.measurableSet hl, setIntegral_congr_fun hU.measurableSet hr]
  exact hlocal

end AlmostSchur
