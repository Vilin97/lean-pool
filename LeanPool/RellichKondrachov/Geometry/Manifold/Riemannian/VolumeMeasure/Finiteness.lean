/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/

import LeanPool.RellichKondrachov.Geometry.Manifold.Riemannian.ChartLocalLipschitz
import LeanPool.RellichKondrachov.Geometry.Manifold.Riemannian.VolumeMeasure

/-!
# `RellichKondrachov.Geometry.Manifold.Riemannian.VolumeMeasure.Finiteness`

Finiteness properties of `riemannianVolumeMeasure`.

## Main results

- `RellichKondrachov.Geometry.Manifold.Riemannian.`
  `riemannianVolumeMeasure_isFiniteMeasureOnCompacts`:
  the Riemannian Hausdorff-volume measure is finite on compact sets.
- `RellichKondrachov.Geometry.Manifold.Riemannian.riemannianVolumeMeasure_isFiniteMeasure`:
  on a compact manifold, the total volume is finite.
-/

namespace RellichKondrachov
namespace Geometry
namespace Manifold
namespace Riemannian

open Set Filter MeasureTheory
open _root_.Manifold _root_.Bundle
open scoped NNReal ENNReal MeasureTheory Topology Manifold

local notation "n∞" => (⊤ : WithTop ℕ∞)

section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I n∞ M] [IsManifold I (1 : WithTop ℕ∞) M]
  [Bundle.RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [T3Space M]

/-- Borel σ-algebra on the model space `E`. -/
local instance instMeasurableSpaceFiniteness : MeasurableSpace M := borel M
local instance instBorelSpaceFiniteness : BorelSpace M := ⟨rfl⟩

omit [IsManifold I n∞ M] in
theorem riemannianVolumeMeasure_isFiniteMeasureOnCompacts :
    IsFiniteMeasureOnCompacts (riemannianVolumeMeasure (I := I) (M := M)) := by
  classical
  letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  letI : BorelSpace M := ⟨rfl⟩
  haveI : IsRiemannianManifold I M := by infer_instance
  have hμ : IsFiniteMeasureOnCompacts (μH[Module.finrank ℝ E] : Measure M) := by
    refine ⟨?_⟩
    intro K hK
    have hU :
        ∀ x : M, ∃ U : Set M, U ∈ 𝓝 x ∧ (μH[Module.finrank ℝ E] : Measure M) U < ∞ := by
      intro x
      rcases lipschitzOnWith_symm_extChartAt_ofRiemannianMetric (I := I) (M := M) x
        with ⟨C, C_pos, r, r_pos, hLip⟩
      let s : Set E := Metric.ball (extChartAt I x x) r ∩ range I
      let U : Set M := (extChartAt I x) ⁻¹' s ∩ (extChartAt I x).source
      have hs : s ∈ 𝓝[range I] (extChartAt I x x) := by
        have : range I ∩ Metric.ball (extChartAt I x x) r ∈ 𝓝[range I] (extChartAt I x x) :=
          inter_mem_nhdsWithin (range I) (Metric.ball_mem_nhds _ r_pos)
        simpa [s, inter_comm, inter_left_comm, inter_assoc] using this
      have hpre : (extChartAt I x) ⁻¹' s ∈ 𝓝 x :=
        extChartAt_preimage_mem_nhds_of_mem_nhdsWithin (I := I) (x := x) (by simp) hs
      have hU_nhds : U ∈ 𝓝 x := Filter.inter_mem hpre (extChartAt_source_mem_nhds (I := I) x)
      refine ⟨U, hU_nhds, ?_⟩
      have hU_sub : U ⊆ (extChartAt I x).symm '' s := by
        intro y hy
        rcases hy with ⟨hyU, hyS⟩
        refine ⟨extChartAt I x y, hyU, ?_⟩
        simpa [hyS] using (extChartAt I x).left_inv hyS
      have hs_fin : (μH[Module.finrank ℝ E] : Measure E) s < ∞ := by
        borelize E
        have hs_le :
            (μH[Module.finrank ℝ E] : Measure E) s ≤
              (μH[Module.finrank ℝ E] : Measure E) (Metric.closedBall (extChartAt I x x) r) := by
          gcongr
          intro y hy
          exact (Metric.ball_subset_closedBall :
            Metric.ball (extChartAt I x x) r ⊆
              Metric.closedBall (extChartAt I x x) r) hy.1
        have hclosed :
            (μH[Module.finrank ℝ E] : Measure E) (Metric.closedBall (extChartAt I x x) r) < ∞ := by
          haveI : IsFiniteMeasureOnCompacts
              (μH[Module.finrank ℝ E] : Measure E) := by
            infer_instance
          simpa using
            (isCompact_closedBall (extChartAt I x x) r).measure_lt_top
              (μ := (μH[Module.finrank ℝ E] : Measure E))
        exact lt_of_le_of_lt hs_le hclosed
      have himage_fin :
          (μH[Module.finrank ℝ E] : Measure M) ((extChartAt I x).symm '' s) < ∞ := by
        have hle := hLip.hausdorffMeasure_image_le (d := (Module.finrank ℝ E : ℝ)) (by positivity)
        refine lt_of_le_of_lt hle ?_
        refine ENNReal.mul_lt_top ?_ hs_fin
        exact ENNReal.rpow_lt_top_of_nonneg (by positivity) ENNReal.coe_ne_top
      exact lt_of_le_of_lt (measure_mono hU_sub) himage_fin
    choose U U_nhds U_fin using hU
    rcases hK.elim_nhds_subcover (U := U) (hU := fun x _ => U_nhds x) with ⟨t, htK, hKt⟩
    refine lt_of_le_of_lt (measure_mono hKt) ?_
    have hle := measure_biUnion_finset_le (μ := (μH[Module.finrank ℝ E] : Measure M)) t U
    refine lt_of_le_of_lt hle ?_
    refine ENNReal.sum_lt_top.2 ?_
    intro x hx
    exact U_fin x
  simpa [riemannianVolumeMeasure] using hμ

omit [IsManifold I n∞ M] in
theorem riemannianVolumeMeasure_isFiniteMeasure [CompactSpace M] :
    IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M)) := by
  classical
  -- `IsFiniteMeasureOnCompacts` implies finiteness on `univ` in a compact space.
  letI : IsFiniteMeasureOnCompacts (riemannianVolumeMeasure (I := I) (M := M)) :=
    riemannianVolumeMeasure_isFiniteMeasureOnCompacts (I := I) (M := M)
  infer_instance

end

end Riemannian
end Manifold
end Geometry
end RellichKondrachov
