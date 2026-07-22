/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.Gram

/-! # Erdős 97 convex-octagon formalization: Rhombus Fan -/

namespace Erdos97Octagon

open scoped InnerProductSpace

/-- A same-length rhombus fan cannot have a common point on the two listed bisectors. -/
theorem no_rhombus_fan
    {a b c d x : Plane} {R : ℝ} (hR : 0 < R) (hcd : c ≠ d)
    (hab : dist a b = R) (hac : dist a c = R) (had : dist a d = R)
    (hbc : dist b c = R) (hbd : dist b d = R)
    (hx_ac : dist x a = dist x c) (hx_db : dist x d = dist x b) :
    False := by
  set u : Plane := b - a with hu
  set v : Plane := c - a with hv
  set w : Plane := d - a with hw
  set y : Plane := x - a with hy
  set s : ℝ := R ^ 2 with hs
  have hs0 : 0 < s := by positivity
  have norm_sq : ∀ {z : Plane}, dist a z = R → ⟪z - a, z - a⟫_ℝ = s := by
    intro z hz
    rw [real_inner_self_eq_norm_sq, ← dist_eq_norm, dist_comm, hz, hs]
  have nu : ⟪u, u⟫_ℝ = s := by simpa [u] using norm_sq hab
  have nv : ⟪v, v⟫_ℝ = s := by simpa [v] using norm_sq hac
  have nw : ⟪w, w⟫_ℝ = s := by simpa [w] using norm_sq had
  have inner_half : ∀ {z t : Plane}, dist a z = R → dist a t = R →
      dist z t = R → ⟪z - a, t - a⟫_ℝ = s / 2 := by
    intro z t haz hat hzt
    have hsub : (z - a) - (t - a) = z - t := by abel
    have hzt_norm : ‖(z - a) - (t - a)‖ = R := by
      rw [hsub, ← dist_eq_norm, hzt]
    have hpolar := norm_sub_sq_real (z - a) (t - a)
    have hnz : ‖z - a‖ ^ 2 = s := by
      rw [← real_inner_self_eq_norm_sq]
      exact norm_sq haz
    have hnt : ‖t - a‖ ^ 2 = s := by
      rw [← real_inner_self_eq_norm_sq]
      exact norm_sq hat
    rw [hzt_norm, hnz, hnt] at hpolar
    have hR2 : R ^ 2 = s := hs.symm
    nlinarith only [hpolar, hR2]
  have iuv : ⟪u, v⟫_ℝ = s / 2 := by simpa [u, v] using inner_half hab hac hbc
  have iuw : ⟪u, w⟫_ℝ = s / 2 := by simpa [u, w] using inner_half hab had hbd
  have ivu : ⟪v, u⟫_ℝ = s / 2 := by rw [real_inner_comm]; exact iuv
  have iwu : ⟪w, u⟫_ℝ = s / 2 := by rw [real_inner_comm]; exact iuw
  set t : ℝ := ⟪v, w⟫_ℝ with ht
  have iwv : ⟪w, v⟫_ℝ = t := by rw [ht, real_inner_comm]
  have hG := gram_det_eq_zero ![u, v, w]
  rw [gram3_expand] at hG
  simp only [nu, nv, nw, iuv, ivu, iuw, iwu, ← ht, iwv] at hG
  have hfactor_mul : s * ((t - s) * (2 * t + s)) = 0 := by
    nlinarith only [hG]
  have hfactor : (t - s) * (2 * t + s) = 0 :=
    (mul_eq_zero.mp hfactor_mul).resolve_left (ne_of_gt hs0)
  have ht_ne_s : t ≠ s := by
    intro hts
    have hvn : ‖v‖ ^ 2 = s := by simpa only [real_inner_self_eq_norm_sq] using nv
    have hwn : ‖w‖ ^ 2 = s := by simpa only [real_inner_self_eq_norm_sq] using nw
    have hpolar := norm_sub_sq_real v w
    have hvw_norm : ‖v - w‖ = dist c d := by
      rw [hv, hw]
      convert (dist_eq_norm c d).symm using 1
      abel_nf
    rw [hvw_norm, hvn, hwn, ← ht, hts] at hpolar
    have hdist_pos : 0 < dist c d := dist_pos.mpr hcd
    have hdist_sq_pos : 0 < (dist c d) ^ 2 := by positivity
    nlinarith only [hpolar, hdist_sq_pos]
  have ht_opp : t = -(s / 2) := by
    have hsecond :=
      (mul_eq_zero.mp hfactor).resolve_left (sub_ne_zero.mpr ht_ne_s)
    linarith only [hsecond]
  have hz_inner : ⟪w - u + v, w - u + v⟫_ℝ = 0 := by
    simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right]
    rw [nu, nv, nw, iuv, ivu, iuw, iwu, ← ht, iwv, ht_opp]
    ring
  have hz : w - u + v = 0 := inner_self_eq_zero.mp hz_inner
  have hx_ac_norm : ‖y‖ = ‖y - v‖ := by
    rw [hy, hv]
    rw [dist_eq_norm, dist_eq_norm] at hx_ac
    convert hx_ac using 1
    abel_nf
  have hfan_ac := norm_sub_sq_real y v
  have hynv : ‖v‖ ^ 2 = s := by simpa only [real_inner_self_eq_norm_sq] using nv
  rw [← hx_ac_norm, hynv] at hfan_ac
  have iyv : ⟪y, v⟫_ℝ = s / 2 := by nlinarith only [hfan_ac]
  have hx_db_norm : ‖y - w‖ = ‖y - u‖ := by
    rw [hy, hw, hu]
    rw [dist_eq_norm, dist_eq_norm] at hx_db
    convert hx_db using 1 <;> abel_nf
  have hfan_d := norm_sub_sq_real y w
  have hfan_b := norm_sub_sq_real y u
  have hwn : ‖w‖ ^ 2 = s := by simpa only [real_inner_self_eq_norm_sq] using nw
  have hun : ‖u‖ ^ 2 = s := by simpa only [real_inner_self_eq_norm_sq] using nu
  rw [hx_db_norm, hwn] at hfan_d
  rw [hun] at hfan_b
  have iywu : ⟪y, w⟫_ℝ = ⟪y, u⟫_ℝ := by
    nlinarith only [hfan_d, hfan_b]
  have hinner_zero : ⟪y, w - u + v⟫_ℝ = 0 := by rw [hz, inner_zero_right]
  simp only [inner_add_right, inner_sub_right] at hinner_zero
  nlinarith only [hinner_zero, iywu, iyv, hs0]

/-- The endpoint-swapped form of `no_rhombus_fan`. -/
theorem no_rhombus_fan_swapped
    {a b c d x : Plane} {R : ℝ} (hR : 0 < R) (hcd : c ≠ d)
    (hab : dist a b = R) (hac : dist a c = R) (had : dist a d = R)
    (hbc : dist b c = R) (hbd : dist b d = R)
    (hx_bc : dist x b = dist x c) (hx_da : dist x d = dist x a) :
    False := by
  exact no_rhombus_fan hR hcd (by simpa [dist_comm] using hab)
    hbc hbd hac had hx_bc hx_da

end Erdos97Octagon
