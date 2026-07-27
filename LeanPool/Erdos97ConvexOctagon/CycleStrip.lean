/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.Gram

/-! # Erdős 97 convex-octagon formalization: Cycle Strip -/

namespace Erdos97Octagon

open scoped InnerProductSpace

private lemma cycle_strip_core
    (u1 u2 u3 u4 u5 u6 : Plane) (s s3 s4 s5 : ℝ) (hs0 : 0 < s)
    (n1 : ⟪u1, u1⟫_ℝ = s) (n2 : ⟪u2, u2⟫_ℝ = s) (n6 : ⟪u6, u6⟫_ℝ = s)
    (ns3 : ⟪u3, u3⟫_ℝ = s3) (ns4 : ⟪u4, u4⟫_ℝ = s4)
    (ns5 : ⟪u5, u5⟫_ℝ = s5)
    (i12 : ⟪u1, u2⟫_ℝ = s / 2) (i21 : ⟪u2, u1⟫_ℝ = s / 2)
    (i23 : ⟪u2, u3⟫_ℝ = s3 / 2) (i32 : ⟪u3, u2⟫_ℝ = s3 / 2)
    (i13 : ⟪u1, u3⟫_ℝ = s3 / 2) (i31 : ⟪u3, u1⟫_ℝ = s3 / 2)
    (i34 : ⟪u3, u4⟫_ℝ = (s3 + s4 - s) / 2)
    (i43 : ⟪u4, u3⟫_ℝ = (s3 + s4 - s) / 2)
    (i24 : ⟪u2, u4⟫_ℝ = s4 / 2) (i42 : ⟪u4, u2⟫_ℝ = s4 / 2)
    (i45 : ⟪u4, u5⟫_ℝ = (s4 + s5 - s) / 2)
    (i54 : ⟪u5, u4⟫_ℝ = (s4 + s5 - s) / 2)
    (i35 : ⟪u3, u5⟫_ℝ = (s3 + s5 - s) / 2)
    (i53 : ⟪u5, u3⟫_ℝ = (s3 + s5 - s) / 2)
    (i56 : ⟪u5, u6⟫_ℝ = s5 / 2) (i65 : ⟪u6, u5⟫_ℝ = s5 / 2)
    (i46 : ⟪u4, u6⟫_ℝ = s4 / 2) (i64 : ⟪u6, u4⟫_ℝ = s4 / 2) :
    False := by
  have hM1 := gram_det_eq_zero ![u1, u2, u3]
  rw [gram3_expand] at hM1
  simp only [n1, n2, ns3, i12, i21, i23, i32, i13, i31] at hM1
  have hM2 := gram_det_eq_zero ![u2, u3, u4]
  rw [gram3_expand] at hM2
  simp only [n2, ns3, ns4, i23, i32, i34, i43, i24, i42] at hM2
  have hM3 := gram_det_eq_zero ![u3, u4, u5]
  rw [gram3_expand] at hM3
  simp only [ns3, ns4, ns5, i34, i43, i45, i54, i35, i53] at hM3
  have hM4 := gram_det_eq_zero ![u4, u5, u6]
  rw [gram3_expand] at hM4
  simp only [ns4, ns5, n6, i45, i54, i56, i65, i46, i64] at hM4
  have h1s : s * (s3 * (s3 - 3 * s)) = 0 := by
    nlinarith only [hM1]
  have h1 : s3 * (s3 - 3 * s) = 0 :=
    (mul_eq_zero.mp h1s).resolve_left (ne_of_gt hs0)
  rcases mul_eq_zero.mp h1 with hc | hc
  · rw [hc] at hM2 hM3
    have h2s : s * ((s4 - s) ^ 2) = 0 := by
      nlinarith only [hM2]
    have hs4 : s4 = s := by
      have hh := (mul_eq_zero.mp h2s).resolve_left (ne_of_gt hs0)
      have hz := (pow_eq_zero_iff (n := 2) (by norm_num)).1 hh
      linarith only [hz]
    rw [hs4] at hM3 hM4
    have h3s : s * ((s5 - s) ^ 2) = 0 := by
      nlinarith only [hM3]
    have hs5 : s5 = s := by
      have hh := (mul_eq_zero.mp h3s).resolve_left (ne_of_gt hs0)
      have hz := (pow_eq_zero_iff (n := 2) (by norm_num)).1 hh
      linarith only [hz]
    rw [hs5] at hM4
    have hpos : (0 : ℝ) < s ^ 3 := by positivity
    nlinarith only [hM4, hpos]
  · have es3 : s3 = 3 * s := by linarith only [hc]
    rw [es3] at hM2 hM3
    have h2s : s * ((s4 - 4 * s) * (s4 - s)) = 0 := by
      nlinarith only [hM2]
    have h2 : (s4 - 4 * s) * (s4 - s) = 0 :=
      (mul_eq_zero.mp h2s).resolve_left (ne_of_gt hs0)
    rcases mul_eq_zero.mp h2 with hc2 | hc2
    · have es4 : s4 = 4 * s := by linarith only [hc2]
      rw [es4] at hM3 hM4
      have h4s : s * ((s5 - 3 * s) ^ 2) = 0 := by
        nlinarith only [hM4]
      have hs5 : s5 = 3 * s := by
        have hh := (mul_eq_zero.mp h4s).resolve_left (ne_of_gt hs0)
        have hz := (pow_eq_zero_iff (n := 2) (by norm_num)).1 hh
        linarith only [hz]
      rw [hs5] at hM3
      have hpos : (0 : ℝ) < s ^ 3 := by positivity
      nlinarith only [hM3, hpos]
    · have es4 : s4 = s := by linarith only [hc2]
      rw [es4] at hM3 hM4
      have h3s : s * ((s5 - s) * (s5 - 4 * s)) = 0 := by
        nlinarith only [hM3]
      have h3 : (s5 - s) * (s5 - 4 * s) = 0 :=
        (mul_eq_zero.mp h3s).resolve_left (ne_of_gt hs0)
      have h4s : s * (s5 * (s5 - 3 * s)) = 0 := by
        nlinarith only [hM4]
      have h4 : s5 * (s5 - 3 * s) = 0 :=
        (mul_eq_zero.mp h4s).resolve_left (ne_of_gt hs0)
      rcases mul_eq_zero.mp h3 with q | q <;>
        rcases mul_eq_zero.mp h4 with r | r <;>
        nlinarith only [q, r, hs0]

/-- The twelve listed equal-length edges cannot form this planar cycle-square strip. -/
theorem no_unit_cycle_square_strip
    {o x1 x2 x3 x4 x5 x6 : Plane} {R : ℝ} (hR : 0 < R)
    (e01 : dist o x1 = R) (e02 : dist o x2 = R) (e06 : dist o x6 = R)
    (e12 : dist x1 x2 = R) (e13 : dist x1 x3 = R) (e23 : dist x2 x3 = R)
    (e24 : dist x2 x4 = R) (e34 : dist x3 x4 = R) (e35 : dist x3 x5 = R)
    (e45 : dist x4 x5 = R) (e46 : dist x4 x6 = R) (e56 : dist x5 x6 = R) :
    False := by
  set s : ℝ := R ^ 2 with hs
  have hs0 : 0 < s := by positivity
  have norm_sq : ∀ {x : Plane}, dist o x = R → ⟪x - o, x - o⟫_ℝ = s := by
    intro x hx
    rw [real_inner_self_eq_norm_sq, ← dist_eq_norm, dist_comm, hx, hs]
  have inner_pol : ∀ {x y : Plane}, dist x y = R →
      ⟪x - o, y - o⟫_ℝ =
        (⟪x - o, x - o⟫_ℝ + ⟪y - o, y - o⟫_ℝ - s) / 2 := by
    intro x y hxy
    have hsub : (x - o) - (y - o) = x - y := by abel
    have hxynorm : ‖(x - o) - (y - o)‖ = R := by
      rw [hsub, ← dist_eq_norm, hxy]
    have hpolar := norm_sub_sq_real (x - o) (y - o)
    rw [hxynorm] at hpolar
    simp only [real_inner_self_eq_norm_sq]
    have hR2 : R ^ 2 = s := hs.symm
    nlinarith only [hpolar, hR2]
  set s3 : ℝ := ⟪x3 - o, x3 - o⟫_ℝ with hs3
  set s4 : ℝ := ⟪x4 - o, x4 - o⟫_ℝ with hs4
  set s5 : ℝ := ⟪x5 - o, x5 - o⟫_ℝ with hs5
  refine cycle_strip_core (x1 - o) (x2 - o) (x3 - o) (x4 - o) (x5 - o) (x6 - o)
    s s3 s4 s5 hs0 (norm_sq e01) (norm_sq e02) (norm_sq e06) rfl rfl rfl
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [inner_pol e12, norm_sq e01, norm_sq e02]
    ring
  · rw [real_inner_comm, inner_pol e12, norm_sq e01, norm_sq e02]
    ring
  · rw [inner_pol e23, norm_sq e02, ← hs3]
    ring
  · rw [real_inner_comm, inner_pol e23, norm_sq e02, ← hs3]
    ring
  · rw [inner_pol e13, norm_sq e01, ← hs3]
    ring
  · rw [real_inner_comm, inner_pol e13, norm_sq e01, ← hs3]
    ring
  · rw [inner_pol e34, ← hs3, ← hs4]
  · rw [real_inner_comm, inner_pol e34, ← hs3, ← hs4]
  · rw [inner_pol e24, norm_sq e02, ← hs4]
    ring
  · rw [real_inner_comm, inner_pol e24, norm_sq e02, ← hs4]
    ring
  · rw [inner_pol e45, ← hs4, ← hs5]
  · rw [real_inner_comm, inner_pol e45, ← hs4, ← hs5]
  · rw [inner_pol e35, ← hs3, ← hs5]
  · rw [real_inner_comm, inner_pol e35, ← hs3, ← hs5]
  · rw [inner_pol e56, norm_sq e06, ← hs5]
    ring
  · rw [real_inner_comm, inner_pol e56, norm_sq e06, ← hs5]
    ring
  · rw [inner_pol e46, norm_sq e06, ← hs4]
    ring
  · rw [real_inner_comm, inner_pol e46, norm_sq e06, ← hs4]
    ring

end Erdos97Octagon
