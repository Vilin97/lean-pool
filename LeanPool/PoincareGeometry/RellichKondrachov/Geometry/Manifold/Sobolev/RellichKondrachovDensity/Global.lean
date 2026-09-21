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

public import LeanPool.PoincareGeometry.RellichKondrachov.Geometry.Manifold.Sobolev.RellichKondrachov
public import LeanPool.PoincareGeometry.RellichKondrachov.Geometry.Manifold.Sobolev.RellichKondrachovDensity.Chartwise

/-! # Global -/

@[expose] public section

/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson

Adaptation: generic finite-measure, two-sided local-density comparison version,
derived from RellichKondrachovRiemannian at upstream commit
70f85d4c1bf99c6e7d61e8be4daa6f3664d08d23 and its local Lean 4.33 migration.
The original support, graph-closure, and compactness proofs are retained;
Riemannian/Hausdorff-specific comparison constants are replaced by explicit
finite bounds on the compact localization supports. No measure equality,
compactness hypothesis, or Poincare inequality is assumed.
-/

/-! # Generic finite-measure manifold Rellich compactness -/

namespace RellichKondrachov
namespace Geometry
namespace Manifold
namespace Sobolev

open Set Filter Topology
open scoped BigOperators ENNReal MeasureTheory Manifold NNReal
open MeasureTheory
open _root_.Manifold _root_.Bundle

local notation "n∞" => (↑(⊤ : ℕ∞) : WithTop ℕ∞)

noncomputable section
variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H}
  [IsManifold I n∞ M] [IsManifold I (1 : WithTop ℕ∞) M]
  [I.Boundaryless] [T2Space M] [CompactSpace M]

local instance densityGlobalInstance0 : MeasurableSpace M := borel M
local instance densityGlobalInstance1 : BorelSpace M := ⟨rfl⟩
local instance densityGlobalInstance2 : MeasurableSpace E := borel E
local instance densityGlobalInstance3 : BorelSpace E := ⟨rfl⟩
local instance densityGlobalInstance4 : OpensMeasurableSpace E := by infer_instance

namespace Density
variable (d : FiniteChartData (H := H) (M := M) I)
  (μ : Measure M) [IsFiniteMeasure μ]

variable (hcomp : LocalMeasureComparison d μ)
include μ hcomp

lemma vendorGeometryManifoldSobolevRellichKondrachovDensityGlobal_isCompactOperator_chartToGlobalL2_h1ToChartL2 (i : d.ι) :
    let μM :=
      μ
    IsCompactOperator fun x : ↥(FiniteChartData.h1 (d := d) (I := I) (μ := μM)) =>
      (FiniteChartData.chartToGlobalL2 (d := d) (I := I) (μ := μM) (F := ℝ) i)
        ((FiniteChartData.h1ToChartL2 (d := d) (I := I) (μ := μM) i) x) := by
  classical
  intro μM
  let μchart := FiniteChartData.chartMeasure (d := d) (I := I) μM i
  let K : Set E := FiniteChartData.rhoSupportImage (d := d) (I := I) i
  have hKm : MeasurableSet K := rhoSupportImage_measurable (d := d) (μ := μ) (I := I) i
  have hcomp : IsCompactOperator (h1ToChartL2Range (d := d) (μ := μ) (I := I) (i := i) : _ → _) := by
    simpa [μchart, K] using! (isCompactOperator_h1ToChartL2Range (d := d) (μ := μ) (hcomp := hcomp) (I := I) (E := E) i)
  -- Postcompose by the inclusion into `L²(μchart)` and then by `chartToGlobalL2`.
  have hcomp' :
      IsCompactOperator fun x : ↥(FiniteChartData.h1 (d := d) (I := I) (μ := μM)) =>
        ((LinearMap.range
              ((MeasureTheory.Lp.extendByZeroₗᵢ
                    (μ := μchart) (E := ℝ) (p := (2 : ℝ≥0∞)) (s := K) hKm).toLinearMap)).subtypeL)
          ((h1ToChartL2Range (d := d) (μ := μ) (I := I) (i := i)) x) :=
    hcomp.clm_comp
      ((LinearMap.range
            ((MeasureTheory.Lp.extendByZeroₗᵢ
                  (μ := μchart) (E := ℝ) (p := (2 : ℝ≥0∞)) (s := K) hKm).toLinearMap)).subtypeL)
  have hcomp'' :
      IsCompactOperator fun x : ↥(FiniteChartData.h1 (d := d) (I := I) (μ := μM)) =>
        (FiniteChartData.chartToGlobalL2 (d := d) (I := I) (μ := μM) (F := ℝ) i)
          (((LinearMap.range
                ((MeasureTheory.Lp.extendByZeroₗᵢ
                      (μ := μchart) (E := ℝ) (p := (2 : ℝ≥0∞)) (s := K) hKm).toLinearMap)).subtypeL)
            ((h1ToChartL2Range (d := d) (μ := μ) (I := I) (i := i)) x)) :=
    hcomp'.clm_comp (FiniteChartData.chartToGlobalL2 (d := d) (I := I) (μ := μM) (F := ℝ) i)
  -- Identify the composite through the range with the original summand.
  simpa [h1ToChartL2Range, μchart, K] using! hcomp''

/-- Rellich compactness for the actual chartwise graph-closure H¹ space over
an arbitrary finite measure. The only analytic input beyond the geometric
finite-chart setup is finite two-sided measure comparison on each fixed
localization support; no compactness or Poincare hypothesis is used. -/
theorem isCompactOperator_h1ToL2 :
    IsCompactOperator fun x :
        ↥(FiniteChartData.h1 (d := d) (I := I)
              (μ :=
                μ)) =>
      FiniteChartData.h1ToL2 (d := d) (I := I)
        (μ :=
          μ) x := by
  classical
  let μM :=
    μ
  -- Apply the finite-sum glue lemma once each chart contribution is compact.
  refine
    (FiniteChartData.isCompactOperator_h1ToL2_of_summands (d := d) (I := I) (μ := μM) ?_)
  intro i
  simpa [μM] using! (vendorGeometryManifoldSobolevRellichKondrachovDensityGlobal_isCompactOperator_chartToGlobalL2_h1ToChartL2 (d := d) (μ := μ) (hcomp := hcomp) (I := I) (E := E) i)



end Density
end
end Sobolev
end Manifold
end Geometry
end RellichKondrachov
