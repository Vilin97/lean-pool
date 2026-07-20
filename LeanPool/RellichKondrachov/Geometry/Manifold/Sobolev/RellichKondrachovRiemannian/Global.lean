/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/

import LeanPool.RellichKondrachov.Geometry.Manifold.Sobolev.RellichKondrachov
import LeanPool.RellichKondrachov.Geometry.Manifold.Sobolev.RellichKondrachovRiemannian.Chartwise

/-!
# `RellichKondrachov.Geometry.Manifold.Sobolev.RellichKondrachovRiemannian.Global`

Finite-atlas assembly: turn the per-chart compactness result into compactness of the global
`H¹ → L²` map for the Riemannian volume measure.
-/

namespace RellichKondrachov
namespace Geometry
namespace Manifold
namespace Sobolev

open Set Filter Topology
open scoped BigOperators ENNReal MeasureTheory Manifold NNReal
open MeasureTheory
open _root_.Manifold _root_.Bundle

local notation "n∞" => (⊤ : WithTop ℕ∞)

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  (I : ModelWithCorners ℝ E H)
  [IsManifold I n∞ M] [IsManifold I (1 : WithTop ℕ∞) M]
  [Bundle.RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [I.Boundaryless]
  [T3Space M]
  [T2Space M] [CompactSpace M]

/-- Borel σ-algebra on the manifold `M`. -/
local instance instMeasurableSpaceMGlobal :
    MeasurableSpace M := borel M
local instance instBorelSpaceMGlobal : BorelSpace M := ⟨rfl⟩

/-- Borel σ-algebra on the model space `E`. -/
local instance instMeasurableSpaceEGlobal :
    MeasurableSpace E := borel E
local instance instBorelSpaceEGlobal : BorelSpace E := ⟨rfl⟩
local instance instOpensMeasurableSpaceGlobal :
    OpensMeasurableSpace E := by
  infer_instance

-- On compact manifolds, the Riemannian volume measure is finite.
local instance instIsFiniteMeasureriemannianVolumeMeasureGlobal :
    IsFiniteMeasure
        (RellichKondrachov.Geometry.Manifold.Riemannian.riemannianVolumeMeasure
          (I := I) (M := M)) :=
  Riemannian.riemannianVolumeMeasure_isFiniteMeasure
    (I := I) (M := M)

namespace RiemannianFiniteChartData

variable (dR : RiemannianFiniteChartData (H := H) (M := M) I)

omit [T2Space M] in
private lemma isCompactOperator_chartToGlobalL2_h1ToChartL2 (i : dR.d.ι) :
    let μM :=
      RellichKondrachov.Geometry.Manifold.Riemannian.riemannianVolumeMeasure (I := I) (M := M)
    IsCompactOperator fun x : ↥(FiniteChartData.h1 (d := dR.d) (I := I) (μ := μM)) =>
      (FiniteChartData.chartToGlobalL2 (d := dR.d) (I := I) (μ := μM) (F := ℝ) i)
        ((FiniteChartData.h1ToChartL2 (d := dR.d) (I := I) (μ := μM) i) x) := by
  classical
  intro μM
  let μchart := FiniteChartData.chartMeasure (d := dR.d) (I := I) μM i
  let K : Set E := FiniteChartData.rhoSupportImage (d := dR.d) (I := I) i
  have hKm : MeasurableSet K := rhoSupportImage_measurable (dR := dR) (I := I) i
  have hcomp : IsCompactOperator (h1ToChartL2Range (dR := dR) (I := I) (i := i) : _ → _) := by
    simpa [μchart, K] using (isCompactOperator_h1ToChartL2Range (dR := dR) (I := I) (E := E) i)
  -- Postcompose by the inclusion into `L²(μchart)` and then by `chartToGlobalL2`.
  have hcomp' :
      IsCompactOperator fun x : ↥(FiniteChartData.h1 (d := dR.d) (I := I) (μ := μM)) =>
        ((LinearMap.range
              ((MeasureTheory.Lp.extendByZeroₗᵢ
                    (μ := μchart) (E := ℝ) (p := (2 : ℝ≥0∞)) (s := K) hKm).toLinearMap)).subtypeL)
          ((h1ToChartL2Range (dR := dR) (I := I) (i := i)) x) :=
    hcomp.clm_comp
      ((LinearMap.range
            ((MeasureTheory.Lp.extendByZeroₗᵢ
                  (μ := μchart) (E := ℝ) (p := (2 : ℝ≥0∞)) (s := K) hKm).toLinearMap)).subtypeL)
  have hcomp'' :
      IsCompactOperator fun x : ↥(FiniteChartData.h1 (d := dR.d) (I := I) (μ := μM)) =>
        (FiniteChartData.chartToGlobalL2 (d := dR.d) (I := I) (μ := μM) (F := ℝ) i)
          (((LinearMap.range
                ((MeasureTheory.Lp.extendByZeroₗᵢ
                      (μ := μchart) (E := ℝ) (p := (2 : ℝ≥0∞)) (s := K) hKm).toLinearMap)).subtypeL)
            ((h1ToChartL2Range (dR := dR) (I := I) (i := i)) x)) :=
    hcomp'.clm_comp (FiniteChartData.chartToGlobalL2 (d := dR.d) (I := I) (μ := μM) (F := ℝ) i)
  -- Identify the composite through the range with the original summand.
  simpa [h1ToChartL2Range, μchart, K] using hcomp''

omit [T2Space M] in
theorem isCompactOperator_h1ToL2_riemannianVolume :
    IsCompactOperator fun x :
        ↥(FiniteChartData.h1 (d := dR.d) (I := I)
              (μ :=
                RellichKondrachov.Geometry.Manifold.Riemannian.riemannianVolumeMeasure (I := I)
                  (M := M))) =>
      FiniteChartData.h1ToL2 (d := dR.d) (I := I)
        (μ :=
          RellichKondrachov.Geometry.Manifold.Riemannian.riemannianVolumeMeasure
            (I := I) (M := M)) x := by
  classical
  let μM :=
    RellichKondrachov.Geometry.Manifold.Riemannian.riemannianVolumeMeasure (I := I) (M := M)
  -- Apply the finite-sum glue lemma once each chart contribution is compact.
  refine
    (FiniteChartData.isCompactOperator_h1ToL2_of_summands (d := dR.d) (I := I) (μ := μM) ?_)
  intro i
  simpa [μM] using (isCompactOperator_chartToGlobalL2_h1ToChartL2 (dR := dR) (I := I) (E := E) i)

end RiemannianFiniteChartData

end

end Sobolev
end Manifold
end Geometry
end RellichKondrachov
