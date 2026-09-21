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

public import LeanPool.PoincareGeometry.AlmostSchur.ChartIntegration
public import Mathlib.Topology.Compactness.Lindelof

/-!
# Gluing the Riemannian chart measures

Disjointifying a countable chart cover constructs a measure. Its restriction
to every chart is the actual metric-density measure, independently of the cover.
The coordinate Haar measure and basis are explicit parameters; canonical
normalization and comparison with Hausdorff volume are separate questions.
-/

@[expose] public noncomputable section
open Bundle Set MeasureTheory
open scoped Manifold ENNReal

namespace AlmostSchur

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M] [I.Boundaryless]
  [MeasurableSpace M] [BorelSpace M] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*} [Fintype ι] [DecidableEq ι]
  [FiniteDimensional ℝ E] [RiemannianBundle (TangentSpace I : M → Type _)]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]

/-- Glue the chart density measures along the disjointification of a sequence
of chart domains. Coverage is required in the characterization theorem. -/
def chartFamilyMeasure (b : Module.Basis ι ℝ E) (a : ℕ → M) : Measure M :=
  Measure.sum fun n => (chartMetricMeasure (I := I) μ b (a n)).restrict
    (disjointed (fun k => (extChartAt I (a k)).source) n)

/-- The glued measure has the prescribed density on every chart, not just
those selected for the covering sequence. -/
theorem chartFamilyMeasure_restrict (b : Module.Basis ι ℝ E) (a : ℕ → M)
    (ha : (⋃ n, (extChartAt I (a n)).source) = univ) (c : M) :
    (chartFamilyMeasure (I := I) μ b a).restrict (extChartAt I c).source =
      (chartMetricMeasure (I := I) μ b c).restrict (extChartAt I c).source := by
  let d := disjointed (fun k => (extChartAt I (a k)).source)
  have hm : ∀ n, MeasurableSet (d n) :=
    MeasurableSet.disjointed fun n => (isOpen_extChartAt_source (a n)).measurableSet
  have hu : (⋃ n, d n) = univ := by
    simpa only [d, iUnion_disjointed] using ha
  have hc := (isOpen_extChartAt_source (I := I) c).measurableSet
  unfold chartFamilyMeasure
  rw [Measure.restrict_sum _ hc]
  have heq : (fun n => ((chartMetricMeasure (I := I) μ b (a n)).restrict (d n)).restrict
      (extChartAt I c).source) =
      (fun n => ((chartMetricMeasure (I := I) μ b c).restrict (d n)).restrict
        (extChartAt I c).source) := by
    funext n
    rw [Measure.restrict_restrict hc, Measure.restrict_restrict hc]
    exact chartMetricMeasure_restrict_eq μ b (a n) c (hc.inter (hm n))
      (fun x hx => disjointed_subset _ n hx.2) (fun _ hx => hx.1)
  change Measure.sum (fun n => ((chartMetricMeasure (I := I) μ b (a n)).restrict (d n)).restrict
    (extChartAt I c).source) = _
  rw [heq, ← Measure.restrict_sum _ hc]
  rw [← Measure.restrict_iUnion (disjoint_disjointed _) hm, hu, Measure.restrict_univ]

/-- The resulting measure is independent of the chosen countable cover. -/
theorem chartFamilyMeasure_eq (b : Module.Basis ι ℝ E) (a a' : ℕ → M)
    (ha : (⋃ n, (extChartAt I (a n)).source) = univ)
    (ha' : (⋃ n, (extChartAt I (a' n)).source) = univ) :
    chartFamilyMeasure (I := I) μ b a = chartFamilyMeasure (I := I) μ b a' := by
  apply Measure.ext_of_iUnion_eq_univ ha
  intro n
  rw [chartFamilyMeasure_restrict μ b a ha, chartFamilyMeasure_restrict μ b a' ha']

omit [IsManifold I 1 M] [I.Boundaryless] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace E] [BorelSpace E] [Fintype ι] [DecidableEq ι]
  [FiniteDimensional ℝ E] [RiemannianBundle (TangentSpace I : M → Type _)] in
/-- A nonempty Lindelöf manifold admits a sequence of chart domains covering
the whole space. In particular, this applies to compact manifolds. -/
theorem exists_countable_chart_cover [Nonempty M] [LindelofSpace M] :
    ∃ a : ℕ → M, (⋃ n, (extChartAt I (a n)).source) = univ := by
  obtain ⟨a, ha⟩ := isLindelof_univ.indexed_countable_subcover
    (fun c : M => (extChartAt I c).source)
    (fun c => isOpen_extChartAt_source c) (by
      intro x _
      exact mem_iUnion.mpr ⟨x, mem_extChartAt_source x⟩)
  exact ⟨a, univ_subset_iff.mp ha⟩

/-- Global Riemannian density measure, characterized locally below. -/
def metricDensityMeasure [Nonempty M] [LindelofSpace M]
    (b : Module.Basis ι ℝ E) : Measure M :=
  chartFamilyMeasure (I := I) μ b (Classical.choose (exists_countable_chart_cover (I := I)))

/-- The global measure restricts to the actual metric-density measure in
every chart. No global analytic identity is assumed in this construction. -/
theorem metricDensityMeasure_restrict [Nonempty M] [LindelofSpace M]
    (b : Module.Basis ι ℝ E) (c : M) :
    (metricDensityMeasure (I := I) μ b).restrict (extChartAt I c).source =
      (chartMetricMeasure (I := I) μ b c).restrict (extChartAt I c).source :=
  chartFamilyMeasure_restrict μ b _ (Classical.choose_spec
    (exists_countable_chart_cover (I := I))) c

/-- Local evaluation of the global measure as a density integral. -/
theorem metricDensityMeasure_apply [Nonempty M] [LindelofSpace M]
    (b : Module.Basis ι ℝ E) (c : M) {s : Set M} (hs : MeasurableSet s)
    (hc : s ⊆ (extChartAt I c).source) :
    metricDensityMeasure (I := I) μ b s =
      chartMetricLIntegral (I := I) μ b c s (fun _ => 1) := by
  have h := congrArg (fun ν : Measure M => ν s) (metricDensityMeasure_restrict (I := I) μ b c)
  simp only [Measure.restrict_apply hs, inter_eq_left.mpr hc] at h
  exact h.trans (chartMetricMeasure_apply μ b c hs hc)

/-- Uniqueness of a measure with the prescribed chartwise density. -/
theorem metricDensityMeasure_unique [Nonempty M] [LindelofSpace M]
    (b : Module.Basis ι ℝ E) (ν : Measure M)
    (hν : ∀ c : M, ν.restrict (extChartAt I c).source =
      (chartMetricMeasure (I := I) μ b c).restrict (extChartAt I c).source) :
    ν = metricDensityMeasure (I := I) μ b := by
  obtain ⟨a, ha⟩ := exists_countable_chart_cover (I := I) (M := M)
  apply Measure.ext_of_iUnion_eq_univ ha
  intro n
  rw [hν, metricDensityMeasure_restrict μ b]

end AlmostSchur
