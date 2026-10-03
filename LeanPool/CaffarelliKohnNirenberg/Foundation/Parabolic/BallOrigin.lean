/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Vec3Norm

/-!
# Ball Origin

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

noncomputable section

namespace CKN.Foundation.Parabolic

/-- The open ball of radius `ρ` about `x` is contained in the metric closed ball about the origin
    of radius `|x|₂ + ρ`, where `|·|₂` is the Euclidean norm on `Vec3`. -/
theorem vec3Ball_subset_closedBall_zero (x : Vec3) (ρ : ℝ) :
    vec3Ball x ρ ⊆ Metric.closedBall (0 : Vec3) (vec3EuclideanNorm x + ρ) := by
  intro y hy
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
  have hy' : vec3EuclideanNorm (y - x) < ρ := (mem_vec3Ball).1 hy
  have htri : vec3EuclideanNorm y ≤
      vec3EuclideanNorm (y - x) + vec3EuclideanNorm x := by
    calc
      vec3EuclideanNorm y = vec3EuclideanNorm ((y - x) + x) := by abel_nf
      _ ≤ vec3EuclideanNorm (y - x) + vec3EuclideanNorm x :=
        vec3EuclideanNorm_add_le (y - x) x
  linarith only [norm_le_vec3EuclideanNorm y, htri, hy']

end CKN.Foundation.Parabolic
