/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.Topology.Order.IntermediateValue

/-!
# Hausdorff measure of connected sets

A preconnected set has one-dimensional Hausdorff measure at least its extended diameter.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped MeasureTheory

namespace LeanPool.Besicovitch

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The Hausdorff one-measure of a preconnected set bounds the distance between its points. -/
theorem edist_le_hausdorffMeasure_one_of_isPreconnected {s : Set X} (hs : IsPreconnected s)
    {x y : X} (hx : x ∈ s) (hy : y ∈ s) : edist x y ≤ μH[1] s := by
  let f : X → ℝ := fun z ↦ dist x z
  have hf : LipschitzWith 1 f := LipschitzWith.dist_right x
  have hIcc : Icc 0 (dist x y) ⊆ f '' s := by
    simpa [f] using hs.intermediate_value hx hy hf.continuous.continuousOn
  calc
    edist x y = μH[1] (Icc 0 (dist x y)) := by
      rw [hausdorffMeasure_real, Real.volume_Icc]
      simp [edist_dist]
    _ ≤ μH[1] (f '' s) := measure_mono hIcc
    _ ≤ μH[1] s := by simpa using hf.hausdorffMeasure_image_le (d := 1) zero_le_one s

/-- The Hausdorff one-measure of a preconnected set bounds its extended diameter. -/
theorem ediam_le_hausdorffMeasure_one_of_isPreconnected {s : Set X} (hs : IsPreconnected s) :
    Metric.ediam s ≤ μH[1] s := by
  exact Metric.ediam_le fun _ hx _ hy ↦
    edist_le_hausdorffMeasure_one_of_isPreconnected hs hx hy

end LeanPool.Besicovitch
