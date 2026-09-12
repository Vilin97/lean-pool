/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import LeanPool.Besicovitch.Geometry.BallUnion
public import LeanPool.Besicovitch.SixPoint.Packing

/-!
# Physical realization of a six-point packing

A normalized packing is realized by multiplying its radii by the physical length scale. This file
relates its virtual diameter and disjointness constraints to the resulting union of open balls.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace LeanPool.Besicovitch

namespace SixPointPacking

variable {normalized physical : SixPointConfiguration}

/-- The physical union of balls obtained from a normalized packing at a given scale. -/
def ballUnionAt (packing : SixPointPacking normalized) (physical : SixPointConfiguration)
    (scale : ℝ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  finiteBallUnion packing.support
    (fun i ↦ physical i.1.1 i.1.2) (fun i ↦ scale * packing.radius i)

/-- The physical radii sum is the scale times the normalized radii sum. -/
theorem sum_radiusAt (packing : SixPointPacking normalized) (scale : ℝ) :
    (∑ i ∈ packing.support.attach, scale * (packing.radius i : ℝ)) =
      scale * packing.totalRadius := by
  simp [totalRadius, Finset.mul_sum]

/-- The physical ball union is open. -/
theorem isOpen_ballUnionAt (packing : SixPointPacking normalized)
    (physical : SixPointConfiguration) (scale : ℝ) :
    IsOpen (packing.ballUnionAt physical scale) :=
  isOpen_finiteBallUnion _ _

/-- Exact scaling of center distances bounds the diameter of the physical ball union. -/
theorem ediam_ballUnionAt_le (packing : SixPointPacking normalized)
    (physical : SixPointConfiguration) {scale : ℝ} (hscale : 0 ≤ scale)
    (hdistance : ∀ i j : packing.support,
      dist (physical i.1.1 i.1.2) (physical j.1.1 j.1.2) =
        scale * dist (normalized i.1.1 i.1.2) (normalized j.1.1 j.1.2)) :
    Metric.ediam (packing.ballUnionAt physical scale) ≤
      ENNReal.ofReal (scale * packing.virtualDiameter) := by
  let maximum := packing.support.attach.sup' packing.support_nonempty.attach fun i ↦
    packing.support.attach.sup' packing.support_nonempty.attach fun j ↦
      dist (physical i.1.1 i.1.2) (physical j.1.1 j.1.2) +
        scale * packing.radius i + scale * packing.radius j
  have hmaximum : maximum ≤ scale * packing.virtualDiameter := by
    dsimp only [maximum]
    apply Finset.sup'_le
    intro i hi
    apply Finset.sup'_le
    intro j hj
    rw [hdistance i j]
    calc
      scale * dist (normalized i.1.1 i.1.2) (normalized j.1.1 j.1.2) +
            scale * packing.radius i + scale * packing.radius j =
          scale * (dist (normalized i.1.1 i.1.2) (normalized j.1.1 j.1.2) +
            packing.radius i + packing.radius j) := by ring
      _ ≤ scale * packing.virtualDiameter :=
        mul_le_mul_of_nonneg_left (packing.pair_le_virtualDiameter i j) hscale
  exact (ediam_finiteBallUnion_le packing.support_nonempty _ _).trans
    (ENNReal.ofReal_le_ofReal hmaximum)

/-- Same-color physical balls remain disjoint under exact distance scaling. -/
theorem disjoint_ballAt (packing : SixPointPacking normalized)
    (physical : SixPointConfiguration) {scale : ℝ} (hscale : 0 ≤ scale)
    (hdistance : ∀ i j : packing.support,
      dist (physical i.1.1 i.1.2) (physical j.1.1 j.1.2) =
        scale * dist (normalized i.1.1 i.1.2) (normalized j.1.1 j.1.2))
    (i j : packing.support) (hij : i ≠ j) (hcolor : i.1.1 = j.1.1) :
    Disjoint (Metric.ball (physical i.1.1 i.1.2) (scale * packing.radius i))
      (Metric.ball (physical j.1.1 j.1.2) (scale * packing.radius j)) := by
  apply Metric.ball_disjoint_ball
  rw [hdistance i j]
  calc
    scale * (packing.radius i : ℝ) + scale * packing.radius j =
        scale * ((packing.radius i : ℝ) + packing.radius j) := by ring
    _ ≤ scale * dist (normalized i.1.1 i.1.2) (normalized j.1.1 j.1.2) :=
      mul_le_mul_of_nonneg_left (packing.same_color_disjoint i j hij hcolor) hscale

end SixPointPacking

end LeanPool.Besicovitch
