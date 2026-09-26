/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Topology
public import Mathlib.Tactic.Linarith

/-! # Compact parabolic balls and changes of center

Compactness is transported through the product homeomorphism. The ball
inclusion uses the triangle inequality and applies without any positivity
assumption on its radii.
-/

public section

open Set Metric
open CKN.Foundation.Parabolic

namespace CKN.Core.Endgame

/-- Every closed ball for the parabolic metric is compact. -/
theorem isCompact_parabolic_closedBall (z₀ : ParabolicPoint) (r : ℝ) :
    IsCompact (closedBall z₀ r) := by
  apply parabolicHomeomorph.symm.isCompact_preimage.mp
  have hspace : IsCompact (vec3Homeomorph ⁻¹'
      closedBall (vec3Homeomorph z₀.1) r) :=
    vec3Homeomorph.isCompact_preimage.mpr (isCompact_closedBall _ _)
  refine (hspace.prod (isCompact_Icc (a := z₀.2 - r ^ 2)
    (b := z₀.2 + r ^ 2))).of_isClosed_subset
      (isClosed_closedBall.preimage parabolicHomeomorph.symm.continuous) ?_
  intro z hz
  change dist (parabolicHomeomorph.symm z) z₀ ≤ r at hz
  rw [dist_eq_parabolicDist] at hz
  have hs := (max_le_iff.mp hz).1
  have ht := (Real.sqrt_le_iff.mp (max_le_iff.mp hz).2).2
  change vec3EuclideanNorm (z.1 - z₀.1) ≤ r at hs
  change |z.2 - z₀.2| ≤ r ^ 2 at ht
  refine ⟨?_, ?_⟩
  · change dist (vec3Homeomorph z.1) (vec3Homeomorph z₀.1) ≤ r
    simpa only [vec3Homeomorph_apply, dist_eq_norm, ← WithLp.toLp_sub,
      ← vec3EuclideanNorm_eq_l2] using hs
  · change z₀.2 - r ^ 2 ≤ z.2 ∧ z.2 ≤ z₀.2 + r ^ 2
    have habs := abs_le.mp ht
    constructor <;> linarith only [habs.1, habs.2]

/-- A ball around a point of a closed ball stays in the outer ball when
the sum of the two radii is at most the outer radius. -/
theorem parabolic_ball_subset_ball_of_center_mem_closedBall
    {z z₀ : ParabolicPoint} {r s R : ℝ}
    (hz : z ∈ closedBall z₀ r) (hr : r + s ≤ R) :
    ball z s ⊆ ball z₀ R := by
  intro w hw
  have hdist : dist w z₀ ≤ dist w z + dist z z₀ := dist_triangle _ _ _
  exact hdist.trans_lt ((add_lt_add_of_lt_of_le hw hz).trans_le
    (by simpa only [add_comm] using hr))

end CKN.Core.Endgame
