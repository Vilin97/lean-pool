/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module
public import LeanPool.PoincareGeometry.RellichKondrachov.Geometry.Manifold.Riemannian.VolumeMeasure.Finiteness
public import LeanPool.PoincareGeometry.RellichKondrachov.Geometry.Manifold.Riemannian.ChartLocalLipschitzForward
public import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Finite positive intrinsic Hausdorff volume

This volume is defined by the Riemannian distance, not by an arbitrary measure.
Its equality with the smooth Riemannian density and integration by parts are
separate pending results.
-/

@[expose] public noncomputable section
open Bundle Set Filter MeasureTheory
open _root_.Manifold
open scoped Manifold ContDiff ENNReal Topology

namespace AlmostSchur

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M] [I.Boundaryless] [T3Space M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContinuousRiemannianBundle E (TangentSpace I : M → Type _)]

local instance : MeasurableSpace M := borel M
local instance : BorelSpace M := ⟨rfl⟩

/-- Dimensional Hausdorff measure for the metric's induced distance. -/
def volumeMeasure : Measure M :=
  RellichKondrachov.Geometry.Manifold.Riemannian.riemannianVolumeMeasure (I := I)

/-- Every neighborhood has positive intrinsic volume. -/
theorem volumeMeasure_pos_of_mem_nhds {x : M} {s : Set M} (hs : s ∈ 𝓝 x) :
    0 < volumeMeasure (I := I) s := by
  classical
  letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  let : BorelSpace M := ⟨rfl⟩
  borelize E
  have : IsRiemannianManifold I M := by infer_instance
  rcases RellichKondrachov.Geometry.Manifold.Riemannian.lipschitzOnWith_extChartAt_ofRiemannianMetric
    (I := I) x with ⟨C, hC, r, hr, hLip⟩
  let U : Set M := {y | riemannianEDist I x y < (r : ℝ≥0∞)}
  have hU : U ∈ 𝓝 x := by
    have hr' : (0 : ℝ≥0∞) < r := by exact_mod_cast hr
    simpa only [U, IsRiemannianManifold.out (I := I) (M := M), Metric.eball,
      edist_comm, riemannianEDist_comm] using!
      Metric.eball_mem_nhds x hr'
  have himage : extChartAt I x '' (s ∩ U) ∈ 𝓝 (extChartAt I x x) :=
    extChartAt_image_nhds_mem_nhds_of_boundaryless (inter_mem hs hU)
  have hpos : 0 < (μH[Module.finrank ℝ E] : Measure E) (extChartAt I x '' (s ∩ U)) :=
    Measure.measure_pos_of_mem_nhds _ himage
  have hle := (hLip.mono (inter_subset_right : s ∩ U ⊆ U)).hausdorffMeasure_image_le
    (d := (Module.finrank ℝ E : ℝ)) (by positivity)
  change 0 < (μH[Module.finrank ℝ E] : Measure M) s
  by_contra h
  have hz : (μH[Module.finrank ℝ E] : Measure M) s = 0 := le_antisymm (not_lt.mp h) bot_le
  have hz' : (μH[Module.finrank ℝ E] : Measure M) (s ∩ U) = 0 :=
    measure_mono_null inter_subset_left hz
  rw [hz', mul_zero] at hle
  exact (not_le_of_gt hpos) hle

theorem volumeMeasure_univ_pos [Nonempty M] :
    0 < volumeMeasure (I := I) (Set.univ : Set M) :=
  volumeMeasure_pos_of_mem_nhds (x := Classical.choice ‹Nonempty M›) Filter.univ_mem

omit [I.Boundaryless] in
theorem volumeMeasure_finite [CompactSpace M] :
    IsFiniteMeasure (volumeMeasure (I := I) (M := M)) :=
  RellichKondrachov.Geometry.Manifold.Riemannian.riemannianVolumeMeasure_isFiniteMeasure
    (I := I)

/-- The denominator in an average is genuinely positive, not a totalized zero inverse. -/
theorem totalVolume_pos [CompactSpace M] [Nonempty M] :
    0 < (volumeMeasure (I := I) (M := M) Set.univ).toReal := by
  let := volumeMeasure_finite (I := I) (M := M)
  exact ENNReal.toReal_pos (volumeMeasure_univ_pos (I := I)).ne' (measure_ne_top _ _)

end AlmostSchur
