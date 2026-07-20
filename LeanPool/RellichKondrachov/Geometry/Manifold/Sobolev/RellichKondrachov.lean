/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/

import Mathlib.Analysis.Normed.Operator.Compact.Basic
import LeanPool.RellichKondrachov.Geometry.Manifold.Sobolev.EmbeddingL2

/-!
# `RellichKondrachov.Geometry.Manifold.Sobolev.RellichKondrachov`

Infrastructure for proving Rellich–Kondrachov compact embeddings on compact manifolds.

This file is intentionally small: it packages the *operator-theoretic glue* showing that the
manifold embedding `H¹ → L²` (defined as a finite sum of chart contributions in
`Sobolev.EmbeddingL2`) is compact once each chart contribution is compact.

The analytic heart of Rellich (compactness on Euclidean chart domains) is tracked separately.

## Main results

- `RellichKondrachov.Geometry.Manifold.Sobolev.FiniteChartData.isCompactOperator_h1ToL2_of_summands`
- `RellichKondrachov.Geometry.Manifold.Sobolev.FiniteChartData.isCompactOperator_h2ToL2_of_summands`
-/

namespace RellichKondrachov
namespace Geometry
namespace Manifold
namespace Sobolev

open Set Topology
open scoped BigOperators ENNReal MeasureTheory
open MeasureTheory
open scoped _root_.Manifold

local notation "n∞" => (⊤ : WithTop ℕ∞)

noncomputable section

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners ℝ E H}
variable [IsManifold I n∞ M] [IsManifold I (1 : WithTop ℕ∞) M]
variable [I.Boundaryless]
variable [T2Space M] [CompactSpace M]

/-- Borel σ-algebra on the manifold `M`. -/
local instance instMeasurableSpaceMRellichKondrachov : MeasurableSpace M := borel M
local instance instBorelSpaceMRellichKondrachov : BorelSpace M := ⟨rfl⟩

/-- Borel σ-algebra on the model space `E`. -/
local instance instMeasurableSpaceERellichKondrachov : MeasurableSpace E := borel E
local instance instBorelSpaceERellichKondrachov : BorelSpace E := ⟨rfl⟩
local instance instOpensMeasurableSpaceERellichKondrachov : OpensMeasurableSpace E := by
  infer_instance

namespace FiniteChartData

variable (d : FiniteChartData (H := H) (M := M) I)

private lemma isCompactOperator_fintype_sum {X Y : Type*} [TopologicalSpace X] [AddCommMonoid X]
    [TopologicalSpace Y] [AddCommMonoid Y] [ContinuousAdd Y]
    {ι : Type*} [Fintype ι] (f : ι → X → Y) (hf : ∀ i, IsCompactOperator (f i)) :
    IsCompactOperator fun x : X => ∑ i : ι, f i x := by
  classical
  -- Work with the `Finset.univ` sum and use `IsCompactOperator.add`.
  have huniv : IsCompactOperator (fun x : X => (Finset.univ : Finset ι).sum fun i => f i x) := by
    refine Finset.induction_on (s := (Finset.univ : Finset ι)) ?_ ?_
    · exact (isCompactOperator_zero : IsCompactOperator (fun _ : X => (0 : Y)))
    · intro a s ha hs
      have hfa : IsCompactOperator (f a) := hf a
      simp only [Finset.sum_insert ha]
      exact hfa.add hs
  simpa using huniv

omit [T2Space M] in
/-- If each chart contribution in the definition of `h1ToL2` is a compact operator, then the
manifold inclusion `H¹ → L²` is a compact operator. -/
theorem isCompactOperator_h1ToL2_of_summands (μ : Measure M) [IsFiniteMeasure μ]
    (h :
      ∀ i : d.ι,
        IsCompactOperator
          (fun x => (chartToGlobalL2 (d := d) (I := I) (μ := μ) (F := ℝ) i)
              (h1ToChartL2 (d := d) (I := I) (μ := μ) i x))) :
    IsCompactOperator fun x => h1ToL2 (d := d) (I := I) (μ := μ) x := by
  classical
  -- `h1ToL2` is a finite sum over the chart index type.
  simpa [h1ToL2] using
    (isCompactOperator_fintype_sum
      (X := ↥(h1 (d := d) (I := I) (μ := μ)))
      (Y := (M →₂[μ] ℝ))
      (ι := d.ι)
      (f := fun i x =>
        (chartToGlobalL2 (d := d) (I := I) (μ := μ) (F := ℝ) i)
          ((h1ToChartL2 (d := d) (I := I) (μ := μ) i) x))
      h)

omit [IsManifold I (1 : WithTop ℕ∞) M] [T2Space M] in
/-- If each chart contribution in the definition of `h2ToL2` is a compact operator, then the
manifold inclusion `H² → L²` is a compact operator. -/
theorem isCompactOperator_h2ToL2_of_summands (μ : Measure M) [IsFiniteMeasure μ]
    (h :
      ∀ i : d.ι,
        IsCompactOperator
          (fun x => (chartToGlobalL2 (d := d) (I := I) (μ := μ) (F := ℝ) i)
              (h2ToChartL2 (d := d) (I := I) (μ := μ) i x))) :
    IsCompactOperator fun x => h2ToL2 (d := d) (I := I) (μ := μ) x := by
  classical
  simpa [h2ToL2] using
    (isCompactOperator_fintype_sum
      (X := ↥(h2 (d := d) (I := I) (μ := μ)))
      (Y := (M →₂[μ] ℝ))
      (ι := d.ι)
      (f := fun i x =>
        (chartToGlobalL2 (d := d) (I := I) (μ := μ) (F := ℝ) i)
          ((h2ToChartL2 (d := d) (I := I) (μ := μ) i) x))
      h)

end FiniteChartData

end

end

end Sobolev
end Manifold
end Geometry
end RellichKondrachov
