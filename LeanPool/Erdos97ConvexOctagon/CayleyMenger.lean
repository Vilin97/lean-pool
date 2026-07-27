/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.Gram

/-! # Erdős 97 convex-octagon formalization: Cayley Menger -/

namespace Erdos97Octagon

open scoped InnerProductSpace

/-- Squared Euclidean distance. -/
noncomputable def sqDist (a b : Plane) : ℝ := dist a b ^ 2

/-- The four-point Cayley--Menger polynomial in its six squared distances. -/
def cm4 (A B C D E F : ℝ) : ℝ :=
  -2 * A ^ 2 * F - 2 * A * B * D + 2 * A * B * E + 2 * A * B * F +
    2 * A * C * D - 2 * A * C * E + 2 * A * C * F + 2 * A * D * F +
    2 * A * E * F - 2 * A * F ^ 2 - 2 * B ^ 2 * E + 2 * B * C * D +
    2 * B * C * E - 2 * B * C * F + 2 * B * D * E - 2 * B * E ^ 2 +
    2 * B * E * F - 2 * C ^ 2 * D - 2 * C * D ^ 2 + 2 * C * D * E +
    2 * C * D * F - 2 * D * E * F

/-- Polarisation expresses an inner product through three squared distances. -/
theorem inner_sub_sub_eq
    (a b c : Plane) :
    ⟪b - a, c - a⟫_ℝ = (sqDist a b + sqDist a c - sqDist b c) / 2 := by
  have hsub : (b - a) - (c - a) = b - c := by abel
  have h := norm_sub_sq_real (b - a) (c - a)
  rw [hsub, ← dist_eq_norm, ← dist_eq_norm, ← dist_eq_norm] at h
  simp only [sqDist]
  rw [dist_comm b a, dist_comm c a] at h
  nlinarith

/-- Four planar points have vanishing Cayley--Menger determinant. -/
theorem cm4_sqDist_eq_zero (a b c d : Plane) :
    cm4 (sqDist a b) (sqDist a c) (sqDist a d)
      (sqDist b c) (sqDist b d) (sqDist c d) = 0 := by
  have h := gram_det_eq_zero ![b - a, c - a, d - a]
  rw [gram3_expand] at h
  have n1 : ⟪b - a, b - a⟫_ℝ = sqDist a b := by
    rw [real_inner_self_eq_norm_sq, ← dist_eq_norm]
    simp only [sqDist, dist_comm b a]
  have n2 : ⟪c - a, c - a⟫_ℝ = sqDist a c := by
    rw [real_inner_self_eq_norm_sq, ← dist_eq_norm]
    simp only [sqDist, dist_comm c a]
  have n3 : ⟪d - a, d - a⟫_ℝ = sqDist a d := by
    rw [real_inner_self_eq_norm_sq, ← dist_eq_norm]
    simp only [sqDist, dist_comm d a]
  have i12 := inner_sub_sub_eq a b c
  have i13 := inner_sub_sub_eq a b d
  have i23 := inner_sub_sub_eq a c d
  have i21 : ⟪c - a, b - a⟫_ℝ =
      (sqDist a b + sqDist a c - sqDist b c) / 2 := by
    rw [real_inner_comm]
    exact i12
  have i31 : ⟪d - a, b - a⟫_ℝ =
      (sqDist a b + sqDist a d - sqDist b d) / 2 := by
    rw [real_inner_comm]
    exact i13
  have i32 : ⟪d - a, c - a⟫_ℝ =
      (sqDist a c + sqDist a d - sqDist c d) / 2 := by
    rw [real_inner_comm]
    exact i23
  rw [n1, n2, n3, i12, i13, i23, i21, i31, i32] at h
  dsimp [cm4]
  ring_nf at h ⊢
  linarith

/-- The Cayley--Menger identity remains zero after dividing all squared
distances by one common nonzero scale. -/
theorem cm4_normalized_eq_zero
    (a b c d : Plane) {s : ℝ} (hs : s ≠ 0) :
    cm4 (sqDist a b / s) (sqDist a c / s) (sqDist a d / s)
      (sqDist b c / s) (sqDist b d / s) (sqDist c d / s) = 0 := by
  have h := cm4_sqDist_eq_zero a b c d
  dsimp [cm4] at h ⊢
  field_simp [hs]
  nlinarith

end Erdos97Octagon
