/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import LeanPool.Besicovitch.BPC.Basic

/-!
# Extracting separated children from density

This file isolates the measure estimate that turns a dense root ball into two well-separated
points of the same set. The missing mass is charged to one common leakage set.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LeanPool.Besicovitch

/-- After paying for a leakage set, the part of a ball in its own color retains the remaining
mass. -/
theorem measure_inter_gt_of_ball_gt_of_leakage {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {e other ball ambient : Set X} {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hball : ball ⊆ ambient)
    (hdisjoint : Disjoint ball other)
    (hdensity : ENNReal.ofReal (a + b) < μ ball)
    (hleakage : μ (ambient \ (e ∪ other)) ≤ ENNReal.ofReal b) :
    ENNReal.ofReal a < μ (e ∩ ball) := by
  have hsubset : ball ⊆ (e ∩ ball) ∪ (ambient \ (e ∪ other)) := by
    intro x hx
    by_cases hxe : x ∈ e
    · exact Or.inl ⟨hxe, hx⟩
    · refine Or.inr ⟨hball hx, ?_⟩
      rintro (hxe' | hxo)
      · exact hxe hxe'
      · exact Set.disjoint_left.1 hdisjoint hx hxo
  have hmeasure : μ ball ≤ μ (e ∩ ball) + μ (ambient \ (e ∪ other)) :=
    (measure_mono hsubset).trans (measure_union_le _ _)
  by_contra h
  have hinter : μ (e ∩ ball) ≤ ENNReal.ofReal a := le_of_not_gt h
  have hsum : μ (e ∩ ball) + μ (ambient \ (e ∪ other)) ≤
      ENNReal.ofReal a + ENNReal.ofReal b := add_le_add hinter hleakage
  have hab : ENNReal.ofReal (a + b) = ENNReal.ofReal a + ENNReal.ofReal b :=
    ENNReal.ofReal_add ha hb
  exact (not_lt_of_ge (hmeasure.trans (hsum.trans_eq hab.symm))) hdensity

/-- Straightness converts enough mass in one color of a root ball into two separated children. -/
theorem IsStraightMeasure.exists_children {μ : Measure (EuclideanSpace ℝ (Fin 2))}
    (hμ : IsStraightMeasure μ) {e : Set (EuclideanSpace ℝ (Fin 2))}
    (he : MeasurableSet e) {root : (EuclideanSpace ℝ (Fin 2))} {d γ : ℝ}
    (hmass : ENNReal.ofReal (2 * γ * d) < μ (e ∩ Metric.ball root d)) :
    ∃ left ∈ e ∩ Metric.ball root d, ∃ right ∈ e ∩ Metric.ball root d,
      2 * γ * d < dist left right := by
  exact hμ.exists_dist_gt (he.inter Metric.isOpen_ball.measurableSet) hmass

end LeanPool.Besicovitch
