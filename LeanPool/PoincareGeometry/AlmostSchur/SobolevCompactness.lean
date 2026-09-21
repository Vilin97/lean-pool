/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.AlmostSchur.SobolevReconstruction
public import LeanPool.PoincareGeometry.RellichKondrachov.Geometry.Manifold.Sobolev.RellichKondrachovDensity.Global

/-!
# Sobolev compactness for normalized Riemannian volume

The adapted Rellich proof transports both graph components to Euclidean
Lebesgue measure. Its two local comparison hypotheses are discharged here
using the actual positive continuous metric density. Hausdorff volume
identification, Poincaré, and Poisson solvability are not hypotheses.
-/

@[expose] public noncomputable section
open Bundle Set MeasureTheory
open scoped Manifold ContDiff ENNReal Topology
open RellichKondrachov.Geometry.Manifold.Sobolev

namespace AlmostSchur

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless] [T2Space M] [CompactSpace M] [Nonempty M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContinuousRiemannianBundle E (TangentSpace I : M → Type _)]

local instance sobolevCompactnessMeasurableM : MeasurableSpace M := borel M
local instance sobolevCompactnessBorelM : BorelSpace M := ⟨rfl⟩
local instance sobolevCompactnessMeasurableE : MeasurableSpace E := borel E
local instance sobolevCompactnessBorelE : BorelSpace E := ⟨rfl⟩
local instance sobolevCompactnessFiniteVolume :
    IsFiniteMeasure (riemannianVolume (I := I) (M := M)) :=
  ⟨(riemannianVolume_finite_positive (I := I)).2⟩

/-- The local measure comparison data come from the actual Riemannian metric. -/
def sobolevLocalMeasureComparison (d : FiniteChartData (H := H) (M := M) I) :
    Density.LocalMeasureComparison d (riemannianVolume (I := I)) := by
  classical
  have h (i : d.ι) := chartPushforward_measure_comparison (I := I) (d.center i)
    (FiniteChartData.isCompact_rhoSupportImage (d := d) i)
    (FiniteChartData.rhoSupportImage_subset_target (d := d) i)
  choose A B hA hB hlo hhi using h
  exact {
    chartToVolume := B
    volumeToChart := A
    chartToVolume_ne_top := hB
    volumeToChart_ne_top := hA
    chart_le_volume := hhi
    volume_le_chart := hlo
  }

/-- Genuine compactness of the graph-closure H1 to L2 map for normalized
Riemannian density volume on a closed smooth manifold. -/
theorem isCompactOperator_sobolevH1ToL2
    (d : FiniteChartData (H := H) (M := M) I) :
    IsCompactOperator (FiniteChartData.h1ToL2 (d := d) (riemannianVolume (I := I))) :=
  Density.isCompactOperator_h1ToL2 d (riemannianVolume (I := I))
    (sobolevLocalMeasureComparison d)

/-- Bounded sequences in the actual chart Sobolev graph have strongly
convergent L2 subsequences. The intrinsic-energy bound is a separate input
needed before applying this result to a Poincaré counterexample sequence. -/
theorem exists_sobolevL2_subsequence
    (d : FiniteChartData (H := H) (M := M) I)
    (u : ℕ → ↥(FiniteChartData.h1 (d := d) (riemannianVolume (I := I))))
    (C : ℝ) (hu : ∀ n, ‖u n‖ ≤ C) :
    ∃ v : M →₂[riemannianVolume (I := I)] ℝ, ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Filter.Tendsto
        (fun n => FiniteChartData.h1ToL2 (d := d) (riemannianVolume (I := I)) (u (φ n)))
        Filter.atTop (𝓝 v) := by
  let T := FiniteChartData.h1ToL2 (d := d) (riemannianVolume (I := I))
  have hc := (isCompactOperator_sobolevH1ToL2 d).isCompact_closure_image_closedBall
    (f := T.toLinearMap) C
  have hmem (n : ℕ) : T (u n) ∈ closure (T '' Metric.closedBall 0 C) :=
    subset_closure ⟨u n, by simpa only [Metric.mem_closedBall, dist_zero_right] using hu n, rfl⟩
  obtain ⟨v, _, φ, hφ, hlim⟩ := hc.tendsto_subseq hmem
  exact ⟨v, φ, hφ, hlim⟩

end AlmostSchur
