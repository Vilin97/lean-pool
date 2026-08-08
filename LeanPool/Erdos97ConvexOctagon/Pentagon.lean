/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.Gram

/-! # Erdős 97 convex-octagon formalization: Pentagon -/

namespace Erdos97Octagon

open scoped InnerProductSpace

/-- Five equal chords cannot form an odd cycle on a circle with the same radius. -/
theorem no_unit_pentagon_centre
    {o a b c d e : Plane} {R : ℝ} (hR : 0 < R)
    (oa : dist o a = R) (ob : dist o b = R) (oc : dist o c = R)
    (od : dist o d = R) (oe : dist o e = R)
    (ab : dist a b = R) (bc : dist b c = R) (cd : dist c d = R)
    (de : dist d e = R) (ea : dist e a = R) : False := by
  set u0 : Plane := a - o with hu0
  set u1 : Plane := b - o with hu1
  set u2 : Plane := c - o with hu2
  set u3 : Plane := d - o with hu3
  set u4 : Plane := e - o with hu4
  set s : ℝ := R ^ 2 with hs
  have hs0 : 0 < s := by positivity
  have norm_sq : ∀ {x : Plane}, dist o x = R → ⟪x - o, x - o⟫_ℝ = s := by
    intro x hx
    rw [real_inner_self_eq_norm_sq, ← dist_eq_norm, dist_comm, hx, hs]
  have n0 : ⟪u0, u0⟫_ℝ = s := norm_sq oa
  have n1 : ⟪u1, u1⟫_ℝ = s := norm_sq ob
  have n2 : ⟪u2, u2⟫_ℝ = s := norm_sq oc
  have n3 : ⟪u3, u3⟫_ℝ = s := norm_sq od
  have n4 : ⟪u4, u4⟫_ℝ = s := norm_sq oe
  have inner_half : ∀ {x y : Plane}, dist o x = R → dist o y = R →
      dist x y = R → ⟪x - o, y - o⟫_ℝ = s / 2 := by
    intro x y hox hoy hxy
    have hsub : (x - o) - (y - o) = x - y := by abel
    have hxynorm : ‖(x - o) - (y - o)‖ = R := by
      rw [hsub, ← dist_eq_norm, hxy]
    have hpolar := norm_sub_sq_real (x - o) (y - o)
    have hnx : ‖x - o‖ ^ 2 = s := by
      rw [← real_inner_self_eq_norm_sq]
      exact norm_sq hox
    have hny : ‖y - o‖ ^ 2 = s := by
      rw [← real_inner_self_eq_norm_sq]
      exact norm_sq hoy
    rw [hxynorm, hnx, hny] at hpolar
    have hR2 : R ^ 2 = s := hs.symm
    nlinarith only [hpolar, hR2]
  have i01 : ⟪u0, u1⟫_ℝ = s / 2 := inner_half oa ob ab
  have i12 : ⟪u1, u2⟫_ℝ = s / 2 := inner_half ob oc bc
  have i23 : ⟪u2, u3⟫_ℝ = s / 2 := inner_half oc od cd
  have i34 : ⟪u3, u4⟫_ℝ = s / 2 := inner_half od oe de
  have i40 : ⟪u4, u0⟫_ℝ = s / 2 := inner_half oe oa ea
  set p : ℝ := ⟪u0, u2⟫_ℝ with hp
  set q : ℝ := ⟪u0, u3⟫_ℝ with hq
  have i10 : ⟪u1, u0⟫_ℝ = s / 2 := by rw [real_inner_comm]; exact i01
  have i21 : ⟪u2, u1⟫_ℝ = s / 2 := by rw [real_inner_comm]; exact i12
  have i32 : ⟪u3, u2⟫_ℝ = s / 2 := by rw [real_inner_comm]; exact i23
  have i43 : ⟪u4, u3⟫_ℝ = s / 2 := by rw [real_inner_comm]; exact i34
  have i04 : ⟪u0, u4⟫_ℝ = s / 2 := by rw [real_inner_comm]; exact i40
  have p20 : ⟪u2, u0⟫_ℝ = p := by rw [hp, real_inner_comm]
  have q30 : ⟪u3, u0⟫_ℝ = q := by rw [hq, real_inner_comm]
  have hE1 := gram_det_eq_zero ![u0, u1, u2]
  rw [gram3_expand] at hE1
  simp only [n0, n1, n2, i01, i12, i10, i21, ← hp, p20] at hE1
  have hE2 := gram_det_eq_zero ![u0, u2, u3]
  rw [gram3_expand] at hE2
  simp only [n0, n2, n3, i23, i32, ← hp, p20, ← hq, q30] at hE2
  have hE3 := gram_det_eq_zero ![u0, u3, u4]
  rw [gram3_expand] at hE3
  simp only [n0, n3, n4, i34, i43, ← hq, q30, i04, i40] at hE3
  ring_nf at hE1 hE2 hE3
  have hp0 : s * ((p - s) * (2 * p + s)) = 0 := by
    nlinarith only [hE1]
  have hp_factor : (p - s) * (2 * p + s) = 0 :=
    (mul_eq_zero.mp hp0).resolve_left (ne_of_gt hs0)
  have hq0 : s * ((q - s) * (2 * q + s)) = 0 := by
    nlinarith only [hE3]
  have hq_factor : (q - s) * (2 * q + s) = 0 :=
    (mul_eq_zero.mp hq0).resolve_left (ne_of_gt hs0)
  have hs3 : 0 < s ^ 3 := by positivity
  rcases mul_eq_zero.mp hp_factor with hp_branch | hp_branch <;>
    rcases mul_eq_zero.mp hq_factor with hq_branch | hq_branch
  · have ep : p = s := by linarith only [hp_branch]
    have eq : q = s := by linarith only [hq_branch]
    rw [ep, eq] at hE2
    nlinarith only [hE2, hs3]
  · have ep : p = s := by linarith only [hp_branch]
    have eq : q = -(s / 2) := by linarith only [hq_branch]
    rw [ep, eq] at hE2
    nlinarith only [hE2, hs3]
  · have ep : p = -(s / 2) := by linarith only [hp_branch]
    have eq : q = s := by linarith only [hq_branch]
    rw [ep, eq] at hE2
    nlinarith only [hE2, hs3]
  · have ep : p = -(s / 2) := by linarith only [hp_branch]
    have eq : q = -(s / 2) := by linarith only [hq_branch]
    rw [ep, eq] at hE2
    nlinarith only [hE2, hs3]

end Erdos97Octagon
