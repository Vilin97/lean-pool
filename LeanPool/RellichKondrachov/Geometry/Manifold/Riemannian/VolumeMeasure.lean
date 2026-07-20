/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/

import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Topology.Compactness.Compact

/-!
# `RellichKondrachov.Geometry.Manifold.Riemannian.VolumeMeasure`

Define a canonical “volume” measure on a smooth Riemannian manifold as the Hausdorff measure at
the manifold dimension, and record a finiteness-on-compacts / compact-manifold finiteness goal.

At the current Mathlib pin, a differential-form based construction of the Riemannian volume form
is not available. The Hausdorff-measure route provides a fully-defined measure compatible with
Riemannian isometries and suitable for building `L²(M)` once finiteness properties are in place.

## Main definitions

- `RellichKondrachov.Geometry.Manifold.Riemannian.riemannianVolumeMeasure`:
  Hausdorff measure `μH[dim]` on `M`, using the emetric structure induced by the Riemannian metric.
-/

namespace RellichKondrachov
namespace Geometry
namespace Manifold
namespace Riemannian

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal MeasureTheory Topology Manifold

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
local instance instMeasurableSpaceVolumeMeasure : MeasurableSpace M := borel M
local instance instBorelSpaceVolumeMeasure : BorelSpace M := ⟨rfl⟩

/-- The “Riemannian volume measure” as Hausdorff measure at the manifold dimension.

This uses `EMetricSpace.ofRiemannianMetric` to construct the emetric structure in a way that is
defeq to the existing topology on `M`, as recommended by the Mathlib Riemannian manifold API. -/
noncomputable def riemannianVolumeMeasure : Measure M := by
  classical
  letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  letI : BorelSpace M := ⟨rfl⟩
  exact (μH[(Module.finrank ℝ E : ℝ)] : Measure M)

end

end Riemannian
end Manifold
end Geometry
end RellichKondrachov
