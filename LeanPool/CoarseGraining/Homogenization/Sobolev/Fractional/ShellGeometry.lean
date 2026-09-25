/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Geometry.OverlapCenters

/-!
# Shell geometry for the fractional Sobolev versus Besov comparison

Pure triadic-cube geometry and counting; no measure theory.  This file
provides the geometric inputs for both directions of the comparison:

* G1 (diameter): two points of an overlapping cube are at `sup`-distance
  less than its side length `3 * cubeScaleFactor S`;
* scale bookkeeping for centers at a given depth.

The bounded-overlap count (G2) and the pair-capture lemma (G3) build on these
in the companion files.
-/

@[expose] public section

namespace Homogenization
namespace Gagliardo

open ScalarOverlap

variable {d : ℕ}

/-- Positivity of the triadic scale factor (public form). -/
theorem cubeScaleFactor_pos' (S : TriadicCube d) : 0 < cubeScaleFactor S := by
  simpa [cubeScaleFactor] using
    (zpow_pos (show (0 : ℝ) < 3 by norm_num) S.scale)

/-- Coordinates of a point of an overlapping cube lie in the defining window. -/
theorem coord_bounds_of_mem_overlapCubeSet {S : TriadicCube d} {x : Vec d}
    (hx : x ∈ ScalarOverlap.cubeSet S) (i : Fin d) :
    ((S.index i : ℝ) - 3 / 2) * cubeScaleFactor S ≤ x i ∧
      x i < ((S.index i : ℝ) + 3 / 2) * cubeScaleFactor S :=
  hx i

/-- G1 (diameter bound): the overlapping cube of side `3 * cubeScaleFactor S`
has `sup`-norm diameter at most its side length. -/
theorem dist_le_of_mem_overlapCubeSet {S : TriadicCube d} {x y : Vec d}
    (hx : x ∈ ScalarOverlap.cubeSet S) (hy : y ∈ ScalarOverlap.cubeSet S) :
    dist x y ≤ 3 * cubeScaleFactor S := by
  have hside : (0 : ℝ) ≤ 3 * cubeScaleFactor S := by
    have := cubeScaleFactor_pos' S
    linarith
  refine (dist_pi_le_iff hside).2 fun i => ?_
  have hxi := coord_bounds_of_mem_overlapCubeSet hx i
  have hyi := coord_bounds_of_mem_overlapCubeSet hy i
  rw [Real.dist_eq, abs_le]
  constructor <;> nlinarith [hxi.1, hxi.2, hyi.1, hyi.2]

/-- The scale of a center at depth `j` below `Q`. -/
theorem scale_of_mem_centersAtDepth {Q S : TriadicCube d} {j : ℕ}
    (hS : S ∈ centersAtDepth Q j) :
    S.scale = Q.scale - (j + 1 : ℕ) :=
  scale_eq_sub_of_mem_descendantsAtDepth
    (mem_descendantsAtDepth_of_mem_centersAtDepth hS)

/-- Two centers at the same depth with the same index coincide. -/
theorem eq_of_index_eq_of_mem_centersAtDepth {Q S T : TriadicCube d} {j : ℕ}
    (hS : S ∈ centersAtDepth Q j) (hT : T ∈ centersAtDepth Q j)
    (hindex : S.index = T.index) : S = T := by
  have hscale : S.scale = T.scale := by
    rw [scale_of_mem_centersAtDepth hS, scale_of_mem_centersAtDepth hT]
  cases S with
  | mk scaleS indexS =>
      cases T with
      | mk scaleT indexT =>
          simp_all

end Gagliardo
end Homogenization
