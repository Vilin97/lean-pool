/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.AlmostSchur.ChartGreen

/-!
# Continuity of the intrinsic divergence

For a metric-compatible torsion-free connection, the coordinate density
formula proves continuity from C1 regularity of the metric and field. No
separate regularity assumption on the connection trace is required.
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

/-- The metric density is C1 and positive on each open chart target. -/
theorem contDiffOn_coordinateDensity
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E) (c : M) :
    ContDiffOn ℝ 1 (fun z => matrixDensity (coordinateMetric (I := I) b c z))
      (extChartAt I c).target := by
  apply ContDiffOn.sqrt
  · exact (determinantMultilinear (ι := ι)).contDiff.comp_contDiffOn
      (contDiffOn_coordinateMetric b c)
  · intro z hz
    exact (coordinateMetric_posDef b c z hz).det_pos.ne'

/-- Intrinsic divergence is the actual metric-density divergence in a chart. -/
theorem divergence_eq_coordinateDensityDivergence
    (cov : CovariantDerivative I E TM) (hm : tangentMetricCompatible cov)
    (ht : cov.torsion = 0) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ E) (c : M) (X : Π x : M, TM x)
    (hX : CMDiff[(chartAt H c).source] 1 (T% X))
    (z : E) (hz : z ∈ (extChartAt I c).target) :
    divergence cov X ((extChartAt I c).symm z) =
      localDensityDivergence (fun y => matrixDensity (coordinateMetric (I := I) b c y))
        (coordinateVectorField (I := I) c X) z := by
  have hx : (extChartAt I c).symm z ∈ (chartAt H c).source := by
    simpa only [extChartAt_source] using (extChartAt I c).map_target hz
  have hXa := ((hX _ hx).contMDiffAt ((chartAt H c).open_source.mem_nhds hx)).mdifferentiableAt
    (by simp)
  have hd := divergence_eq_localConnectionDivergence cov b X c ((extChartAt I c).symm z) hx hXa
  rw [(extChartAt I c).right_inv hz] at hd
  rw [hd]
  apply localConnectionDivergence_eq_density b (coordinateMetric (I := I) b c)
  · exact ((contDiffOn_coordinateMetric b c).contDiffAt
      ((isOpen_extChartAt_target c).mem_nhds hz)).differentiableAt (by simp)
  · exact coordinateMetric_posDef b c z hz
  · exact ((contDiffOn_coordinateVectorField c X hX).contDiffAt
      ((isOpen_extChartAt_target c).mem_nhds hz)).differentiableAt (by simp)
  · exact coordinateConnection_compatible_on cov hm b c z hz
  · exact coordinateConnection_symmetric_on cov ht b c z hz

/-- The divergence of a C1 vector field is continuous for the geometric
metric-compatible torsion-free connection. -/
theorem continuous_divergence
    (cov : CovariantDerivative I E TM) (hm : tangentMetricCompatible cov)
    (ht : cov.torsion = 0) (X : Π x : M, TM x) (hX : CMDiff 1 (T% X)) :
    Continuous (divergence cov X) := by
  classical
  rw [continuous_iff_continuousAt]
  intro x
  let b := (stdOrthonormalBasis ℝ E).toBasis
  let ρ := fun z => matrixDensity (coordinateMetric (I := I) b x z)
  let Y := coordinateVectorField (I := I) x X
  have hc : ContinuousOn (localDensityDivergence ρ Y) (extChartAt I x).target :=
    continuousOn_localDensityDivergence (isOpen_extChartAt_target x) ρ Y
      (contDiffOn_coordinateDensity b x) (contDiffOn_coordinateVectorField x X hX.contMDiffOn)
      (fun z hz => coordinateMetric_density_pos b x z hz)
  have hd : ContinuousAt (fun y => localDensityDivergence ρ Y (extChartAt I x y)) x :=
    (hc.continuousAt ((isOpen_extChartAt_target x).mem_nhds (mem_extChartAt_target x))).comp
      (continuousAt_extChartAt x)
  apply hd.congr_of_eventuallyEq
  filter_upwards [(isOpen_extChartAt_source (I := I) x).mem_nhds (mem_extChartAt_source x)] with y hy
  have h := divergence_eq_coordinateDensityDivergence cov hm ht b x X hX.contMDiffOn
    (extChartAt I x y) ((extChartAt I x).map_source hy)
  rw [(extChartAt I x).left_inv hy] at h
  exact h

/-- The scalar differential evaluated on a C1 field is continuous. The
identity follows from the already proved divergence product rule. -/
theorem continuous_differential_apply
    (cov : CovariantDerivative I E TM) (hm : tangentMetricCompatible cov)
    (ht : cov.torsion = 0) (f : M → ℝ) (X : Π x : M, TM x)
    (hf : CMDiff 1 f) (hX : CMDiff 1 (T% X)) :
    Continuous (fun x => mvfderiv I f x (X x)) := by
  have he : (fun x => mvfderiv I f x (X x)) =
      fun x => divergence cov (fun y => f y • X y) x - f x * divergence cov X x := by
    funext x
    rw [divergence_smul cov f X x (hf.mdifferentiable (by simp) x)
      (hX.mdifferentiable (by simp) x)]
    ring
  rw [he]
  exact (continuous_divergence cov hm ht _ (hf.smul_section hX)).sub
    (hf.continuous.mul (continuous_divergence cov hm ht X hX))

end AlmostSchur
