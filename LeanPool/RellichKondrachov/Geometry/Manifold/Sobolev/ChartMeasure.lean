/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/

import LeanPool.RellichKondrachov.Geometry.Manifold.Sobolev.ChartData
import Mathlib.MeasureTheory.Measure.AEMeasurable
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

/-!
# `RellichKondrachov.Geometry.Manifold.Sobolev.ChartMeasure`

Pushforward measures on the model space arising from charts.

For chart-based Sobolev spaces on a manifold `M`, it is convenient to transport the ambient measure
on `M` to a measure on the model space `E` using `extChartAt`. This file defines the resulting
measures and records basic finiteness instances needed by the Euclidean Sobolev baseline.
-/

namespace RellichKondrachov
namespace Geometry
namespace Manifold
namespace Sobolev

open scoped Manifold MeasureTheory Topology
open MeasureTheory

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners ℝ E H} [IsManifold I (⊤ : WithTop ℕ∞) M]

/-- Borel σ-algebra on the model space `E`. -/
local instance instMeasurableSpaceChartMeasure : MeasurableSpace M := borel M
local instance instBorelSpaceChartMeasure : BorelSpace M := ⟨rfl⟩

/-- Borel σ-algebra on the model space `E`. -/
local instance instMeasurableSpaceChartMeasure1 : MeasurableSpace E := borel E
local instance instBorelSpaceChartMeasure1 : BorelSpace E := ⟨rfl⟩
local instance instOpensMeasurableSpaceChartMeasure : OpensMeasurableSpace E := by infer_instance

/-- Any finite measure is finite on compact sets. -/
lemma isFiniteMeasureOnCompacts_of_isFiniteMeasure {α : Type*} [TopologicalSpace α]
    [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ] :
    IsFiniteMeasureOnCompacts μ :=
  ⟨fun K _hK =>
    (measure_mono (Set.subset_univ K)).trans_lt (measure_lt_top μ Set.univ)⟩

namespace FiniteChartData

variable (d : FiniteChartData (H := H) (M := M) I)

/-!
## Chart measures

Given a measure `μ` on `M`, each chart center `d.center i` yields a pushforward measure on `E`
along the extended chart `extChartAt I (d.center i)`.

We define this as a pushforward of the **restricted** measure
`μ.restrict (extChartAt I (d.center i)).source`
so that the value of `extChartAt` outside its source is irrelevant.
-/

/-- The pushforward of a measure `μ` on `M` along the extended chart `extChartAt`. -/
noncomputable def chartMeasure (μ : Measure M) (i : d.ι) : Measure E :=
  (μ.restrict (extChartAt I (d.center i)).source).map (extChartAt I (d.center i))

section

omit [FiniteDimensional ℝ E]

/-- The extended chart is a.e.-measurable with respect to the restricted measure on its source. -/
lemma aemeasurable_extChartAt (μ : Measure M) (i : d.ι) :
    AEMeasurable (extChartAt I (d.center i))
      (μ.restrict (extChartAt I (d.center i)).source) := by
  classical
  have hs :
      MeasurableSet (extChartAt I (d.center i)).source :=
    (isOpen_extChartAt_source (I := I) (x := d.center i)).measurableSet
  have hcont :
      Continuous ((extChartAt I (d.center i)).source.restrict (extChartAt I (d.center i))) :=
    (continuousOn_iff_continuous_restrict).1 (continuousOn_extChartAt (I := I) (x := d.center i))
  exact aemeasurable_restrict_of_measurable_subtype (μ := μ) hs hcont.measurable

end

instance instIsFiniteMeasurechartMeasure (μ : Measure M) (i : d.ι) [IsFiniteMeasure μ] :
    IsFiniteMeasure (chartMeasure (d := d) (I := I) μ i) := by
  classical
  delta chartMeasure
  infer_instance

instance instIsFiniteMeasureOnCompactschartMeasure (μ : Measure M) (i : d.ι) [IsFiniteMeasure μ] :
    IsFiniteMeasureOnCompacts (chartMeasure (d := d) (I := I) μ i) := by
  classical
  exact isFiniteMeasureOnCompacts_of_isFiniteMeasure (μ := chartMeasure (d := d) (I := I) μ i)

end FiniteChartData

end

end Sobolev
end Manifold
end Geometry
end RellichKondrachov
