/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import LeanPool.Besicovitch.Statement

/-!
# The common pair of root balls

The direct pair-condition transfer charges both child extractions to one union of root balls.
-/

@[expose] public section

namespace LeanPool.Besicovitch

/-- The common open neighborhood formed by two balls of the same radius. -/
def rootBallUnion (x y : (EuclideanSpace ℝ (Fin 2))) (r : ℝ) :
    Set (EuclideanSpace ℝ (Fin 2)) :=
  Metric.ball x r ∪ Metric.ball y r

/-- The common root-ball union is open. -/
theorem isOpen_rootBallUnion (x y : (EuclideanSpace ℝ (Fin 2))) (r : ℝ) :
    IsOpen (rootBallUnion x y r) :=
  Metric.isOpen_ball.union Metric.isOpen_ball

/-- The diameter of the common root-ball union is bounded by root distance plus two radii. -/
theorem ediam_rootBallUnion_le (x y : (EuclideanSpace ℝ (Fin 2))) (r : ℝ) :
    Metric.ediam (rootBallUnion x y r) ≤ ENNReal.ofReal (dist x y + 2 * r) := by
  apply Metric.ediam_le_of_forall_dist_le
  intro a ha b hb
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · have hab : dist a b < 2 * r := by
      calc
        dist a b ≤ dist a x + dist x b := dist_triangle _ _ _
        _ < r + r := add_lt_add (Metric.mem_ball.mp ha) (Metric.mem_ball'.mp hb)
        _ = 2 * r := by ring
    exact hab.le.trans (le_add_of_nonneg_left dist_nonneg)
  · have hab : dist a b < dist x y + 2 * r := by
      calc
        dist a b ≤ dist a x + dist x y + dist y b := dist_triangle4 _ _ _ _
        _ < r + dist x y + r := by
          gcongr
          · exact Metric.mem_ball.mp ha
          · exact Metric.mem_ball'.mp hb
        _ = dist x y + 2 * r := by ring
    exact hab.le
  · have hab : dist a b < dist x y + 2 * r := by
      rw [dist_comm]
      calc
        dist b a ≤ dist b x + dist x y + dist y a := dist_triangle4 _ _ _ _
        _ < r + dist x y + r := by
          gcongr
          · exact Metric.mem_ball.mp hb
          · exact Metric.mem_ball'.mp ha
        _ = dist x y + 2 * r := by ring
    exact hab.le
  · have hab : dist a b < 2 * r := by
      calc
        dist a b ≤ dist a y + dist y b := dist_triangle _ _ _
        _ < r + r := add_lt_add (Metric.mem_ball.mp ha) (Metric.mem_ball'.mp hb)
        _ = 2 * r := by ring
    exact hab.le.trans (le_add_of_nonneg_left dist_nonneg)

end LeanPool.Besicovitch
