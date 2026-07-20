/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/

import LeanPool.RellichKondrachov.Geometry.Manifold.Riemannian.VolumeMeasure
import LeanPool.RellichKondrachov.Geometry.Manifold.Sobolev.ChartDataRiemannian
import LeanPool.RellichKondrachov.Geometry.Manifold.Sobolev.ChartMeasure
import Mathlib.Geometry.Manifold.IsManifold.Basic

/-!
# `RellichKondrachov.Geometry.Manifold.Sobolev.ChartMeasureRiemannian`

Measure-comparison lemmas for chart pushforward measures arising from the Riemannian Hausdorff
volume measure.

The key input is local Lipschitz control of chart inverses (in chart coordinates) for the
Riemannian distance. This yields one-sided domination of chart measures by Euclidean Hausdorff
measure on the chart target, restricted to suitable neighborhoods.

## Main results

- `RellichKondrachov.Geometry.Manifold.Sobolev.RiemannianFiniteChartData.`
  `chartMeasure_restrict_le_hausdorff`:
  on the chart ball, the pushforward of `riemannianVolumeMeasure` is dominated by `μH[dim]` on `E`
  with an explicit constant.
-/

namespace RellichKondrachov
namespace Geometry
namespace Manifold
namespace Sobolev

open Set Filter Topology
open scoped ENNReal MeasureTheory Manifold NNReal
open MeasureTheory
open _root_.Manifold _root_.Bundle

universe uE uH uM

local notation "n∞" => (⊤ : WithTop ℕ∞)

noncomputable section

section

variable
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type uH} [TopologicalSpace H]
  {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
  (I : ModelWithCorners ℝ E H)
  [IsManifold I n∞ M] [IsManifold I (1 : WithTop ℕ∞) M]
  [Bundle.RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [T3Space M]

/-- Borel σ-algebra on the manifold `M`. -/
local instance instMeasurableSpaceMChartMeasureRiemannian : MeasurableSpace M := borel M
local instance instBorelSpaceMChartMeasureRiemannian : BorelSpace M := ⟨rfl⟩

/-- Borel σ-algebra on the model space `E`. -/
local instance instMeasurableSpaceEChartMeasureRiemannian : MeasurableSpace E := borel E
local instance instBorelSpaceEChartMeasureRiemannian : BorelSpace E := ⟨rfl⟩
local instance instOpensMeasurableSpaceChartMeasureRiemannian :
    OpensMeasurableSpace E := by
  infer_instance

namespace RiemannianFiniteChartData

variable (dR : RiemannianFiniteChartData (H := H) (M := M) I)

omit
  [IsManifold I (1 : WithTop ℕ∞) M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [T3Space M] in
private lemma chartBall_subset_ball_range (i : dR.d.ι) :
    chartBall (dR := dR) (I := I) i ⊆
      Metric.ball (extChartAt I (dR.d.center i) (dR.d.center i)) (dR.r i) ∩ range I := by
  intro y hy
  refine ⟨hy.1, ?_⟩
  exact extChartAt_target_subset_range (I := I) (x := dR.d.center i) hy.2

/-- On the chart ball, the chart pushforward measure of the Riemannian Hausdorff volume measure is
dominated by Euclidean Hausdorff measure, with an explicit Lipschitz constant. -/
lemma chartMeasure_restrict_le_hausdorff (i : dR.d.ι) :
    (FiniteChartData.chartMeasure (d := dR.d) (I := I)
        (RellichKondrachov.Geometry.Manifold.Riemannian.riemannianVolumeMeasure
          (I := I) (M := M)) i).restrict
        (chartBall (dR := dR) (I := I) i) ≤
      ((dR.C i : ℝ≥0∞) ^ (Module.finrank ℝ E : ℝ)) •
        (μH[(Module.finrank ℝ E : ℝ)] : Measure E).restrict (chartBall (dR := dR) (I := I) i) := by
  classical
  -- Work in the emetric space structure induced by the Riemannian metric, so `μM = μH[dim]`.
  letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  letI : BorelSpace M := ⟨rfl⟩
  haveI : IsRiemannianManifold I M := by infer_instance
  let μM : Measure M :=
    RellichKondrachov.Geometry.Manifold.Riemannian.riemannianVolumeMeasure (I := I) (M := M)
  let μE : Measure E := (μH[(Module.finrank ℝ E : ℝ)] : Measure E)
  let S : Set E := chartBall (dR := dR) (I := I) i
  have hμM : μM = (μH[(Module.finrank ℝ E : ℝ)] : Measure M) := by
    simp [μM, RellichKondrachov.Geometry.Manifold.Riemannian.riemannianVolumeMeasure]
  have hS_meas : MeasurableSet S := by
    have hball : MeasurableSet (Metric.ball (extChartAt I (dR.d.center i) (dR.d.center i)) (dR.r
      i)) :=
      (Metric.isOpen_ball).measurableSet
    have htarget : MeasurableSet ((extChartAt I (dR.d.center i)).target : Set E) := by
      -- `extChartAt.target = (I.symm ⁻¹' chartAt.target) ∩ range I`, where both parts are
      -- measurable.
      have hopen : IsOpen (I.symm ⁻¹' (chartAt H (dR.d.center i)).target : Set E) :=
        I.continuous_symm.isOpen_preimage _ (chartAt H (dR.d.center i)).open_target
      have hclosed : IsClosed (range I) := ModelWithCorners.isClosed_range (I := I)
      simpa [extChartAt_target (I := I) (x := dR.d.center i), inter_assoc, inter_comm,
        inter_left_comm] using
        (hopen.measurableSet.inter hclosed.measurableSet)
    simpa [S, chartBall, hball, htarget] using hball.inter htarget
  intro A
  -- Reduce to a measurable superset (measurable w.r.t. `μE.restrict S`) so we can use
  -- `restrict_apply`.
  set t : Set E := toMeasurable (μE.restrict S) A with ht
  have hAt : A ⊆ t := subset_toMeasurable (μ := μE.restrict S) A
  have ht_meas : MeasurableSet t := measurableSet_toMeasurable (μ := μE.restrict S) A
  have hleA :
      (FiniteChartData.chartMeasure (d := dR.d) (I := I) μM i).restrict S A ≤
        (FiniteChartData.chartMeasure (d := dR.d) (I := I) μM i).restrict S t :=
    measure_mono hAt
  refine hleA.trans ?_
  have htS_meas : MeasurableSet (t ∩ S) := ht_meas.inter hS_meas
  -- Convert the Riemannian-distance inequality to a `LipschitzOnWith` statement in the induced
  -- emetric space structure on `M`.
  have hLip :
      LipschitzOnWith (dR.C i) (extChartAt I (dR.d.center i)).symm
        (Metric.ball (extChartAt I (dR.d.center i) (dR.d.center i)) (dR.r i) ∩ range I) := by
    intro y₁ hy₁ y₂ hy₂
    simpa [IsRiemannianManifold.out (I := I) (M := M)] using
      dR.riemannianLipschitz_symm i y₁ hy₁ y₂ hy₂
  have hLipS : LipschitzOnWith (dR.C i) (extChartAt I (dR.d.center i)).symm S :=
    hLip.mono (chartBall_subset_ball_range (dR := dR) (I := I) i)
  have hSubT : t ∩ S ⊆ (extChartAt I (dR.d.center i)).target := by
    intro y hy
    exact hy.2.2
  -- Rewrite `chartMeasure` as the `μM`-measure of a `symm` image on the chart target.
  have hChart :
      (FiniteChartData.chartMeasure (d := dR.d) (I := I) μM i) (t ∩ S) =
        μM ((extChartAt I (dR.d.center i)).symm '' (t ∩ S)) := by
    have hf :
        AEMeasurable (extChartAt I (dR.d.center i))
          (μM.restrict (extChartAt I (dR.d.center i)).source) :=
      FiniteChartData.aemeasurable_extChartAt (d := dR.d) (I := I) (μ := μM) i
    have hmap :
        (FiniteChartData.chartMeasure (d := dR.d) (I := I) μM i) (t ∩ S) =
          (μM.restrict (extChartAt I (dR.d.center i)).source)
            ((extChartAt I (dR.d.center i)) ⁻¹' (t ∩ S)) := by
      unfold FiniteChartData.chartMeasure
      exact Measure.map_apply_of_aemeasurable hf htS_meas
    have hpre_null :
        NullMeasurableSet ((extChartAt I (dR.d.center i)) ⁻¹' (t ∩ S))
          (μM.restrict (extChartAt I (dR.d.center i)).source) :=
      hf.nullMeasurable htS_meas
    have hrestrict :
        (μM.restrict (extChartAt I (dR.d.center i)).source)
            ((extChartAt I (dR.d.center i)) ⁻¹' (t ∩ S)) =
          μM (((extChartAt I (dR.d.center i)) ⁻¹' (t ∩ S)) ∩ (extChartAt I (dR.d.center i)).source)
            := by
      exact
        (Measure.restrict_apply₀ (μ := μM) (s := (extChartAt I (dR.d.center i)).source)
          (t := (extChartAt I (dR.d.center i)) ⁻¹' (t ∩ S)) hpre_null)
    have hsymm :
        (extChartAt I (dR.d.center i)).symm '' (t ∩ S) =
          (extChartAt I (dR.d.center i)).source ∩ (extChartAt I (dR.d.center i)) ⁻¹' (t ∩ S) :=
      (PartialEquiv.symm_image_eq_source_inter_preimage (e := extChartAt I (dR.d.center i)) hSubT)
    calc
      (FiniteChartData.chartMeasure (d := dR.d) (I := I) μM i) (t ∩ S) =
          (μM.restrict (extChartAt I (dR.d.center i)).source)
            ((extChartAt I (dR.d.center i)) ⁻¹' (t ∩ S)) := hmap
      _ = μM (((extChartAt I (dR.d.center i)) ⁻¹' (t ∩ S)) ∩ (extChartAt I (dR.d.center i)).source)
        := hrestrict
      _ = μM ((extChartAt I (dR.d.center i)).source ∩ (extChartAt I (dR.d.center i)) ⁻¹' (t ∩ S)) :=
          congrArg μM (inter_comm _ _)
      _ = μM ((extChartAt I (dR.d.center i)).symm '' (t ∩ S)) :=
          congrArg μM (Eq.symm hsymm)
  -- Apply Hausdorff measure distortion on the smaller set `t ∩ S`.
  have hLipTS :
      LipschitzOnWith (dR.C i) (extChartAt I (dR.d.center i)).symm (t ∩ S) :=
    hLipS.mono (by intro y hy; exact hy.2)
  have hleHaus :=
    hLipTS.hausdorffMeasure_image_le (d := (Module.finrank ℝ E : ℝ)) (by positivity)
  have hμEt : (μE.restrict S) t = (μE.restrict S) A := by
    rw [ht]
    exact measure_toMeasurable (μ := μE.restrict S) A
  have hmain_t :
      (FiniteChartData.chartMeasure (d := dR.d) (I := I) μM i).restrict S t ≤
        ((dR.C i : ℝ≥0∞) ^ (Module.finrank ℝ E : ℝ)) • (μE.restrict S) t := by
    have hle' :
        μM ((extChartAt I (dR.d.center i)).symm '' (t ∩ S)) ≤
          ((dR.C i : ℝ≥0∞) ^ (Module.finrank ℝ E : ℝ)) * μE (t ∩ S) := by
      simpa [hμM, μE] using hleHaus
    -- Convert the inequality to the restricted-measure form.
    simpa [Measure.restrict_apply, ht_meas, Measure.smul_apply, hChart] using hle'
  -- Conclude for `A` via monotonicity and `toMeasurable`.
  have hright_A :
      ((dR.C i : ℝ≥0∞) ^ (Module.finrank ℝ E : ℝ)) • (μE.restrict S) t =
        ((dR.C i : ℝ≥0∞) ^ (Module.finrank ℝ E : ℝ)) • (μE.restrict S) A := by
    simp [hμEt]
  exact hmain_t.trans (le_of_eq hright_A)

/-! ### Reverse domination on chart balls -/

/-- On the chart ball, Euclidean Hausdorff measure is dominated by the chart pushforward measure of
the Riemannian Hausdorff volume measure. -/
lemma hausdorff_restrict_le_chartMeasure (i : dR.d.ι) :
    (μH[(Module.finrank ℝ E : ℝ)] : Measure E).restrict (chartBall (dR := dR) (I := I) i) ≤
      ((dR.Cfwd i : ℝ≥0∞) ^ (Module.finrank ℝ E : ℝ)) •
        (FiniteChartData.chartMeasure (d := dR.d) (I := I)
              (RellichKondrachov.Geometry.Manifold.Riemannian.riemannianVolumeMeasure
                (I := I) (M := M)) i).restrict
          (chartBall (dR := dR) (I := I) i) := by
  classical
  -- Work in the emetric space structure induced by the Riemannian metric, so `μM = μH[dim]`.
  letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  letI : BorelSpace M := ⟨rfl⟩
  haveI : IsRiemannianManifold I M := by infer_instance
  let μM : Measure M :=
    RellichKondrachov.Geometry.Manifold.Riemannian.riemannianVolumeMeasure (I := I) (M := M)
  let μE : Measure E := (μH[(Module.finrank ℝ E : ℝ)] : Measure E)
  let S : Set E := chartBall (dR := dR) (I := I) i
  have hμM : μM = (μH[(Module.finrank ℝ E : ℝ)] : Measure M) := by
    simp [μM, RellichKondrachov.Geometry.Manifold.Riemannian.riemannianVolumeMeasure]
  have hS_meas : MeasurableSet S := by
    have hball : MeasurableSet (Metric.ball (extChartAt I (dR.d.center i) (dR.d.center i)) (dR.r
      i)) :=
      (Metric.isOpen_ball).measurableSet
    have htarget : MeasurableSet ((extChartAt I (dR.d.center i)).target : Set E) := by
      -- `extChartAt.target = (I.symm ⁻¹' chartAt.target) ∩ range I`, where both parts are
      -- measurable.
      have hopen : IsOpen (I.symm ⁻¹' (chartAt H (dR.d.center i)).target : Set E) :=
        I.continuous_symm.isOpen_preimage _ (chartAt H (dR.d.center i)).open_target
      have hclosed : IsClosed (range I) := ModelWithCorners.isClosed_range (I := I)
      simpa [extChartAt_target (I := I) (x := dR.d.center i), inter_assoc, inter_comm,
        inter_left_comm] using
        (hopen.measurableSet.inter hclosed.measurableSet)
    simpa [S, chartBall, hball, htarget] using hball.inter htarget
  intro A
  -- Reduce to a measurable superset (measurable w.r.t. `chartMeasure.restrict S`) so we can use
  -- `restrict_apply`.
  set chartMeasure :
      Measure E :=
    FiniteChartData.chartMeasure (d := dR.d) (I := I) μM i
  set t : Set E := toMeasurable (chartMeasure.restrict S) A with ht
  have hAt : A ⊆ t := subset_toMeasurable (μ := chartMeasure.restrict S) A
  have ht_meas : MeasurableSet t := measurableSet_toMeasurable (μ := chartMeasure.restrict S) A
  have hleA : (μE.restrict S) A ≤ (μE.restrict S) t := measure_mono hAt
  refine hleA.trans ?_
  have htS_meas : MeasurableSet (t ∩ S) := ht_meas.inter hS_meas
  -- Convert the Riemannian-distance inequality to a `LipschitzOnWith` statement in the induced
  -- emetric space structure on `M`.
  let U : Set M :=
    (extChartAt I (dR.d.center i)) ⁻¹' Metric.ball (extChartAt I (dR.d.center i) (dR.d.center i))
      (dR.r i) ∩
      (extChartAt I (dR.d.center i)).source
  have hLipU :
      LipschitzOnWith (dR.Cfwd i) (extChartAt I (dR.d.center i)) U := by
    intro x₁ hx₁ x₂ hx₂
    simpa [IsRiemannianManifold.out (I := I) (M := M)] using dR.riemannianLipschitz i x₁ hx₁ x₂ hx₂
  -- Rewrite `chartMeasure` as the `μM`-measure of a `symm` image on the chart target.
  have hSubT : t ∩ S ⊆ (extChartAt I (dR.d.center i)).target := by
    intro y hy
    exact hy.2.2
  have hChart :
      chartMeasure (t ∩ S) = μM ((extChartAt I (dR.d.center i)).symm '' (t ∩ S)) := by
    have hf :
        AEMeasurable (extChartAt I (dR.d.center i)) (μM.restrict (extChartAt I (dR.d.center
          i)).source) :=
      FiniteChartData.aemeasurable_extChartAt (d := dR.d) (I := I) (μ := μM) i
    have hmap :
        chartMeasure (t ∩ S) =
          (μM.restrict (extChartAt I (dR.d.center i)).source) ((extChartAt I (dR.d.center i)) ⁻¹'
            (t ∩ S)) := by
      unfold chartMeasure FiniteChartData.chartMeasure
      exact Measure.map_apply_of_aemeasurable hf htS_meas
    have hpre_null :
        NullMeasurableSet ((extChartAt I (dR.d.center i)) ⁻¹' (t ∩ S))
          (μM.restrict (extChartAt I (dR.d.center i)).source) :=
      hf.nullMeasurable htS_meas
    have hrestrict :
        (μM.restrict (extChartAt I (dR.d.center i)).source) ((extChartAt I (dR.d.center i)) ⁻¹' (t
          ∩ S)) =
          μM (((extChartAt I (dR.d.center i)) ⁻¹' (t ∩ S)) ∩ (extChartAt I (dR.d.center i)).source)
            := by
      exact
        (Measure.restrict_apply₀ (μ := μM) (s := (extChartAt I (dR.d.center i)).source)
          (t := (extChartAt I (dR.d.center i)) ⁻¹' (t ∩ S)) hpre_null)
    have hsymm :
        (extChartAt I (dR.d.center i)).symm '' (t ∩ S) =
          (extChartAt I (dR.d.center i)).source ∩ (extChartAt I (dR.d.center i)) ⁻¹' (t ∩ S) :=
      (PartialEquiv.symm_image_eq_source_inter_preimage (e := extChartAt I (dR.d.center i)) hSubT)
    calc
      chartMeasure (t ∩ S) =
          (μM.restrict (extChartAt I (dR.d.center i)).source) ((extChartAt I (dR.d.center i)) ⁻¹'
            (t ∩ S)) := hmap
      _ = μM (((extChartAt I (dR.d.center i)) ⁻¹' (t ∩ S)) ∩ (extChartAt I (dR.d.center i)).source)
        := hrestrict
      _ = μM ((extChartAt I (dR.d.center i)).source ∩ (extChartAt I (dR.d.center i)) ⁻¹' (t ∩ S)) :=
          congrArg μM (inter_comm _ _)
      _ = μM ((extChartAt I (dR.d.center i)).symm '' (t ∩ S)) :=
          congrArg μM (Eq.symm hsymm)
  -- Apply Hausdorff measure distortion for the forward chart on `symm '' (t ∩ S)`.
  let Apre : Set M := (extChartAt I (dR.d.center i)).symm '' (t ∩ S)
  have hApre_sub : Apre ⊆ U := by
    intro x hx
    rcases hx with ⟨y, hy, rfl⟩
    have hy_target : y ∈ (extChartAt I (dR.d.center i)).target := hSubT hy
    refine ⟨?_, (extChartAt I (dR.d.center i)).map_target hy_target⟩
    -- `extChartAt (symm y) = y`, hence membership in the chart ball.
    have : (extChartAt I (dR.d.center i)) ((extChartAt I (dR.d.center i)).symm y) = y :=
      (extChartAt I (dR.d.center i)).right_inv hy_target
    -- `S = ball ∩ target`, so `y` lies in the `ball` part.
    have hy_ball : y ∈ Metric.ball (extChartAt I (dR.d.center i) (dR.d.center i)) (dR.r i) := hy.2.1
    have hy_dist :
        dist y (extChartAt I (dR.d.center i) (dR.d.center i)) < dR.r i := by
      simpa [Metric.mem_ball] using hy_ball
    have hy_dist' :
        dist ((extChartAt I (dR.d.center i)) ((extChartAt I (dR.d.center i)).symm y))
            (extChartAt I (dR.d.center i) (dR.d.center i)) < dR.r i := by
      simpa only [this] using hy_dist
    -- Turn the `dist` inequality back into a membership statement.
    simpa [U, Metric.mem_ball] using hy_dist'
  have hLipApre : LipschitzOnWith (dR.Cfwd i) (extChartAt I (dR.d.center i)) Apre :=
    hLipU.mono hApre_sub
  have hleHaus :=
    hLipApre.hausdorffMeasure_image_le (d := (Module.finrank ℝ E : ℝ)) (by positivity)
  have himage :
      (extChartAt I (dR.d.center i)) '' Apre = t ∩ S := by
    simpa [Apre] using
      (PartialEquiv.image_symm_image_of_subset_target (e := extChartAt I (dR.d.center i)) hSubT)
  have hle' :
      μE (t ∩ S) ≤ ((dR.Cfwd i : ℝ≥0∞) ^ (Module.finrank ℝ E : ℝ)) * chartMeasure (t ∩ S) := by
    have hleHaus' :
        μE ((extChartAt I (dR.d.center i)) '' Apre) ≤
          ((dR.Cfwd i : ℝ≥0∞) ^ (Module.finrank ℝ E : ℝ)) *
            μM ((extChartAt I (dR.d.center i)).symm '' (t ∩ S)) := by
      simpa [μE, hμM, Apre] using hleHaus
    -- Match the definitional expansions of `extChartAt` / `extChartAt.symm` in `hleHaus'`.
    have himage' :
        (fun a : M => (I (chartAt H (dR.d.center i) a))) '' Apre = t ∩ S := by
      simpa [extChartAt_coe, Function.comp] using himage
    have hChart' : chartMeasure (t ∩ S) = μM (((chartAt H (dR.d.center i)).symm ∘ I.symm) '' (t ∩
      S)) := by
      simpa [extChartAt_coe_symm] using hChart
    -- Rewrite `f '' Apre = t ∩ S` and `μM Apre = chartMeasure (t ∩ S)`.
    simpa [himage', hChart', extChartAt_coe_symm, Function.comp] using hleHaus'
  have hchart_t : (chartMeasure.restrict S) t = (chartMeasure.restrict S) A := by
    rw [ht]
    exact measure_toMeasurable (μ := chartMeasure.restrict S) A
  have hmain_t :
      (μE.restrict S) t ≤ ((dR.Cfwd i : ℝ≥0∞) ^ (Module.finrank ℝ E : ℝ)) • (chartMeasure.restrict
        S) t := by
    simpa [Measure.restrict_apply, ht_meas, Measure.smul_apply, hS_meas, hle'] using hle'
  have hright_A :
      ((dR.Cfwd i : ℝ≥0∞) ^ (Module.finrank ℝ E : ℝ)) • (chartMeasure.restrict S) t =
        ((dR.Cfwd i : ℝ≥0∞) ^ (Module.finrank ℝ E : ℝ)) • (chartMeasure.restrict S) A := by
    simp [hchart_t]
  exact hmain_t.trans (le_of_eq hright_A)

end RiemannianFiniteChartData

end

end

end Sobolev
end Manifold
end Geometry
end RellichKondrachov
