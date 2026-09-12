/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import LeanPool.Besicovitch.SixPoint.Configuration

/-!
# Canonical tangent radii for a triangle

The three radii are the half-perimeter differences, indexed by the six-point labels.
-/

@[expose] public section

noncomputable section

namespace LeanPool.Besicovitch

variable {X : Type*} [PseudoMetricSpace X]

/-- The canonical mutually tangent radii attached to a labelled triangle. -/
def canonicalTriangleRadius (root left right : X) : SixPointLabel → ℝ
  | .root => (dist root left + dist root right - dist left right) / 2
  | .left => (dist root left + dist left right - dist root right) / 2
  | .right => (dist root right + dist left right - dist root left) / 2

/-- The root and left canonical radii sum to their center distance. -/
theorem canonicalTriangleRadius_root_add_left (root left right : X) :
    canonicalTriangleRadius root left right .root +
      canonicalTriangleRadius root left right .left = dist root left := by
  simp only [canonicalTriangleRadius]
  ring

/-- The root and right canonical radii sum to their center distance. -/
theorem canonicalTriangleRadius_root_add_right (root left right : X) :
    canonicalTriangleRadius root left right .root +
      canonicalTriangleRadius root left right .right = dist root right := by
  simp only [canonicalTriangleRadius]
  ring

/-- The left and right canonical radii sum to their center distance. -/
theorem canonicalTriangleRadius_left_add_right (root left right : X) :
    canonicalTriangleRadius root left right .left +
      canonicalTriangleRadius root left right .right = dist left right := by
  simp only [canonicalTriangleRadius]
  ring

/-- Every canonical triangle radius is nonnegative. -/
theorem canonicalTriangleRadius_nonneg (root left right : X) (label : SixPointLabel) :
    0 ≤ canonicalTriangleRadius root left right label := by
  cases label
  · simp only [canonicalTriangleRadius]
    have htriangle := dist_triangle left root right
    rw [dist_comm left root] at htriangle
    nlinarith
  · simp only [canonicalTriangleRadius]
    nlinarith [dist_triangle root left right]
  · simp only [canonicalTriangleRadius]
    have htriangle := dist_triangle root right left
    rw [dist_comm right left] at htriangle
    nlinarith

/-- The root radius is at most the average root-to-child distance. -/
theorem canonicalTriangleRadius_root_le_average (root left right : X) :
    canonicalTriangleRadius root left right .root ≤
      (dist root left + dist root right) / 2 := by
  simp only [canonicalTriangleRadius]
  nlinarith [show 0 ≤ dist left right from dist_nonneg]

/-- The left radius is at most the root-to-left distance. -/
theorem canonicalTriangleRadius_left_le_dist (root left right : X) :
    canonicalTriangleRadius root left right .left ≤ dist root left := by
  simp only [canonicalTriangleRadius]
  have htriangle := dist_triangle left root right
  rw [dist_comm left root] at htriangle
  nlinarith

/-- The right radius is at most the root-to-right distance. -/
theorem canonicalTriangleRadius_right_le_dist (root left right : X) :
    canonicalTriangleRadius root left right .right ≤ dist root right := by
  simp only [canonicalTriangleRadius]
  have htriangle := dist_triangle right root left
  rw [dist_comm right root, dist_comm right left] at htriangle
  nlinarith

/-- Unit root-to-child distances place every canonical radius in the unit interval. -/
theorem canonicalTriangleRadius_le_one (root left right : X)
    (hleft : dist root left ≤ 1) (hright : dist root right ≤ 1) (label : SixPointLabel) :
    canonicalTriangleRadius root left right label ≤ 1 := by
  cases label
  · exact (canonicalTriangleRadius_root_le_average root left right).trans (by linarith)
  · exact (canonicalTriangleRadius_left_le_dist root left right).trans hleft
  · exact (canonicalTriangleRadius_right_le_dist root left right).trans hright

end LeanPool.Besicovitch
