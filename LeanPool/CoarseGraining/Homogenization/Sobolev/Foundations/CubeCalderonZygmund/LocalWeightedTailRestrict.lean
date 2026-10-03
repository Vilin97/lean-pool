/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.LocalWeightedTail

/-! # Local Weighted Tail Restrict -/

@[expose] public section

namespace Homogenization

open scoped ENNReal

noncomputable section

namespace CubeCalderonZygmund

open MeasureTheory

/-!
# Local weighted comparison tails

This is the restriction-stable form of the weighted comparison estimate.  It
requires measurability only on the ball (or other local set) under study.
-/

/-- The weighted comparison-tail estimate with all measurability assumptions
localized to the measurable set `B`. -/
theorem sqWeightedMeasure_tail_le_comparison_restrict
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {B : Set α} (hB : MeasurableSet B)
    {f v : α → E} (hf : AEStronglyMeasurable f (μ.restrict B))
    (hv : AEStronglyMeasurable v (μ.restrict B))
    {r a : ℝ} (hr : 2 < r) (ha : 0 < a) :
    sqWeightedMeasure f μ ({x | a < ‖f x‖} ∩ B) ≤
      2 * ENNReal.ofReal ((a / 2) ^ (2 - r)) *
          (∫⁻ x in B, ENNReal.ofReal (‖v x‖ ^ r) ∂μ) +
        6 * (∫⁻ x in B, ENNReal.ofReal (‖f x - v x‖ ^ (2 : ℕ)) ∂μ) := by
  let T : Set α := {x | a < ‖f x‖}
  have htail := sqWeightedMeasure_tail_le_comparison
    (μ := μ.restrict B) (B := Set.univ) MeasurableSet.univ hf hv hr ha
  simp only [Set.inter_univ] at htail
  have hweight : sqWeightedMeasure f (μ.restrict B) T =
      sqWeightedMeasure f μ (T ∩ B) := by
    change ((μ.restrict B).withDensity fun x => ENNReal.ofReal (‖f x‖ ^ (2 : ℕ))) T =
      (μ.withDensity fun x => ENNReal.ofReal (‖f x‖ ^ (2 : ℕ))) (T ∩ B)
    rw [← MeasureTheory.restrict_withDensity hB]
    exact Measure.restrict_apply' hB
  rw [hweight] at htail
  simpa only [T, MeasureTheory.Measure.restrict_univ] using htail

end CubeCalderonZygmund

end

end Homogenization
