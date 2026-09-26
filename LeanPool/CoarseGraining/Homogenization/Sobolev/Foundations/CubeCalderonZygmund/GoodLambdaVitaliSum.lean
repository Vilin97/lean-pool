/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Ambient.Basic
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.GoodLambda

/-! # Good Lambda Vitali Sum -/

@[expose] public section

namespace Homogenization

open scoped ENNReal BigOperators

noncomputable section

namespace CubeCalderonZygmund

open MeasureTheory

/-!
# Measure summation after Vitali selection

This file isolates the purely measure-theoretic summation step used after a
Vitali selection of stopping balls.  It deliberately knows nothing about the
origin of the high-level set or the control measure.
-/

/-- A disjoint positive-radius family of closed sup-metric balls in `Vec d`
is countable.  This is the topological input needed to sum the local bounds
over a Vitali-selected subfamily. -/
private theorem countable_of_pairwiseDisjoint_closedBall {d : ℕ} {ι : Type*}
    {u : Set ι} (centre : ι → Vec d) (radius : ι → ℝ)
    (hpositive : ∀ i ∈ u, 0 < radius i)
    (hdisjoint : u.PairwiseDisjoint fun i => Metric.closedBall (centre i) (radius i)) :
    u.Countable := by
  apply hdisjoint.countable_of_nonempty_interior
  intro i hi
  refine ⟨centre i, ?_⟩
  exact Metric.ball_subset_interior_closedBall
    (Metric.mem_ball_self (hpositive i hi))

/-- Sum local estimates over a Vitali-selected family.  The selected original
balls are pairwise disjoint and have positive radius, hence are countable in
the separable space `Vec d`; their enlarged balls only provide the cover and
need not be disjoint. -/
theorem measure_le_mul_measure_of_vitali_closedBall_cover
    {d : ℕ} {ι : Type*} (ν κ : Measure (Vec d))
    (target ambient : Set (Vec d)) (u : Set ι)
    (centre : ι → Vec d) (radius : ι → ℝ) (τ : ℝ) (K : ℝ≥0∞)
    (hpositive : ∀ i ∈ u, 0 < radius i)
    (hdisjoint : u.PairwiseDisjoint fun i => Metric.closedBall (centre i) (radius i))
    (hcover : target ⊆ ⋃ i ∈ u, Metric.closedBall (centre i) (τ * radius i))
    (hlocal : ∀ i ∈ u,
      ν (target ∩ Metric.closedBall (centre i) (τ * radius i)) ≤
        K * κ (Metric.closedBall (centre i) (radius i)))
    (hambient : (⋃ i ∈ u, Metric.closedBall (centre i) (radius i)) ⊆ ambient) :
    ν target ≤ K * κ ambient := by
  have hcount : u.Countable :=
    countable_of_pairwiseDisjoint_closedBall centre radius hpositive hdisjoint
  have htarget : target ⊆ ⋃ i ∈ u,
      target ∩ Metric.closedBall (centre i) (τ * radius i) := by
    intro x hx
    rcases Set.mem_iUnion₂.mp (hcover hx) with ⟨i, hi, hxi⟩
    exact Set.mem_iUnion₂.mpr ⟨i, hi, ⟨hx, hxi⟩⟩
  have hν_union :
      ν (⋃ i ∈ u, target ∩ Metric.closedBall (centre i) (τ * radius i)) ≤
        ∑' i : u, ν (target ∩ Metric.closedBall (centre i) (τ * radius i)) :=
    measure_biUnion_le ν hcount _
  have hlocal_tsum :
      (∑' i : u, ν (target ∩ Metric.closedBall (centre i) (τ * radius i))) ≤
        ∑' i : u, K * κ (Metric.closedBall (centre i) (radius i)) := by
    exact ENNReal.tsum_le_tsum fun i => hlocal i i.2
  have hκ_union :
      κ (⋃ i ∈ u, Metric.closedBall (centre i) (radius i)) =
        ∑' i : u, κ (Metric.closedBall (centre i) (radius i)) := by
    exact measure_biUnion hcount hdisjoint fun _ _ => measurableSet_closedBall
  calc
    ν target ≤ ν (⋃ i ∈ u, target ∩ Metric.closedBall (centre i) (τ * radius i)) :=
      measure_mono htarget
    _ ≤ ∑' i : u, ν (target ∩ Metric.closedBall (centre i) (τ * radius i)) := hν_union
    _ ≤ ∑' i : u, K * κ (Metric.closedBall (centre i) (radius i)) := hlocal_tsum
    _ = K * ∑' i : u, κ (Metric.closedBall (centre i) (radius i)) :=
      ENNReal.tsum_mul_left
    _ = K * κ (⋃ i ∈ u, Metric.closedBall (centre i) (radius i)) := by rw [hκ_union]
    _ ≤ K * κ ambient := mul_le_mul_right (measure_mono hambient) K

end CubeCalderonZygmund

end

end Homogenization
