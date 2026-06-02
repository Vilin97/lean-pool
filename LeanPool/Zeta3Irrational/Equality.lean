/-
Copyright (c) 2026 Junqi Liu, Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junqi Liu, Jujian Zhang
-/

import LeanPool.Zeta3Irrational.Integral

/-!
# LeanPool.Zeta3Irrational.Equality
-/

namespace LeanPool.Zeta3Irrational

open scoped Nat
open BigOperators Polynomial

lemma integral_equality_help (s t : ℝ) (s0 : 0 < s) (s1 : s < 1) (t0 : 0 < t) (t1 : t < 1) :
    ∫ (u : ℝ) in (0)..1, 1 / ((1 - (1 - u) * s) * (1 - (1 - t) * u)) =
    ∫ (u : ℝ) in (0)..1,
      1 / (1 - (1 - s) * t) *
        (s / (1 - (1 - u) * s) + (1 - t) / (1 - (1 - t) * u)) := by
  rw[← sub_pos] at s1
  obtain h1 := mul_lt_of_lt_one_right s1 t1
  have h2 : (1 - s) * t < 1 := by linarith
  have eq1 (u : ℝ) (hu : 0 < u) (hu1 : u < 1) :
      1 / (1 - (1 - s) * t) * (s / (1 - (1 - u) * s) + (1 - t) / (1 - (1 - t) * u)) =
      1 / ((1 - (1 - u) * s) * (1 - (1 - t) * u)) := by
    have h4 : (1 - u) * s < 1 := by
      rw[← sub_pos] at hu1
      rw[sub_pos] at s1
      obtain h11 := mul_lt_of_lt_one_right hu1 s1
      linarith
    have h5 : (1 - t) * u < 1 := by
      rw[← sub_pos] at t1
      obtain h11 := mul_lt_of_lt_one_right t1 hu1
      linarith
    rw[div_add_div]
    · field_simp
      rw[div_eq_div_iff]
      · ring_nf
      · apply ne_of_gt
        apply mul_pos
        · apply mul_pos <;> nlinarith
        · nlinarith
      · apply ne_of_gt
        apply mul_pos <;> nlinarith
    · linarith
    · linarith
  rw[← intervalIntegral.integral_congr]
  intro a b
  simp only [one_div, mul_inv_rev]
  rw[inv_eq_one_div, inv_eq_one_div, inv_eq_one_div, one_div_mul_one_div]
  simp only [zero_le_one, Set.uIcc_of_le, Set.mem_Icc] at b
  rcases b with ⟨b1, b2⟩
  by_cases b11 : a = 0
  · rw [b11]
    field_simp [show 1 - s ≠ 0 by linarith, show 1 - (1 - s) * t ≠ 0 by linarith]
    ring_nf
  · by_cases b21 : a = 1
    · rw [b21]
      field_simp [show t ≠ 0 by linarith, show 1 - (1 - s) * t ≠ 0 by linarith]
      ring_nf
    · have b12 : 0 < a := by
        exact lt_of_le_of_ne b1 (Ne.symm b11)
      have b22 : a < 1 := by
        exact lt_of_le_of_ne b2 b21
      obtain b00 := eq1 a b12 b22
      rw [b00]
      ring_nf

lemma integral_equality (s t : ℝ) (s0 : 0 < s) (s1 : s < 1) (t0 : 0 < t) (t1 : t < 1) :
    ∫ (u : ℝ) in (0)..1, 1 /(1 - (1 - (1 - s) * t) * u) =
    ∫ (u : ℝ) in (0)..1, 1 /((1 - (1 - u) * s) * (1 - (1 - t) * u)) := by
  rw[← sub_pos] at s1
  obtain h1 := mul_lt_of_lt_one_right s1 t1
  have h2 : (1 - s) * t < 1 := by linarith
  have h3 := integral1 (mul_pos s1 t0) h2
  have eq3 : ∫ (x : ℝ) in (0)..1, s / (1 - (1 - x) * s) = - (1 - s).log := by
    have eq3_1 := intervalIntegral.integral_comp_sub_mul (a := 0) (b := 1) (c := 1)
      (d := 1) (f := fun z ↦ (s / (1 - z * s))) (by norm_num)
    have eq3_2 := intervalIntegral.integral_comp_add_mul (a := 0) (b := 1) (c := s)
      (d := 0) (f := fun z ↦ (1 / (1 - z))) (by positivity)
    have eq3_3 := integral_inv_of_pos (a := 1 - s) (b := 1) s1 (by norm_num)
    have comm1 := intervalIntegral.integral_comp_mul_right (a := 0) (b := 1) (c := s)
      (f := fun z ↦ s / (1 - z)) (by positivity)
    have comm2 := intervalIntegral.integral_comp_mul_left (a := 0) (b := 1) (c := s)
      (f := fun z ↦ s / (1 - z)) (by positivity)
    simp only [one_mul, inv_one, mul_one, sub_self, mul_zero, sub_zero, smul_eq_mul] at eq3_1
    simp only [zero_add, one_div, mul_zero, add_zero, mul_one,
      intervalIntegral.integral_comp_sub_left, sub_zero, smul_eq_mul] at eq3_2
    rw [← mul_right_inj' (a := s) (by linarith),
      ← intervalIntegral.integral_const_mul, ← mul_assoc,
      show s * s⁻¹  = 1 by field_simp, one_mul, eq3_3] at eq3_2
    simp_rw [← div_eq_mul_inv] at eq3_2
    simp only [mul_zero, zero_mul, mul_one, one_mul, smul_eq_mul] at comm1 comm2
    rw [eq3_1, comm1, ← comm2, eq3_2, ← Real.log_inv, ← one_div]
  have eq4 : ∫ (x : ℝ) in (0)..1, (1 - t) / (1 - (1 - t) * x) = - t.log := by
    rw[← sub_pos] at t1
    have eq4_1 := intervalIntegral.integral_comp_mul_left (a := 0) (b := 1)
      (c := 1 - t) (f := fun z ↦ (1 - t) * (1 - z)⁻¹) (by positivity)
    have eq4_2 := intervalIntegral.mul_integral_comp_sub_mul (a := 0) (b := 1 - t)
      (f := fun x ↦ (x)⁻¹) (c := 1) (d := 1)
    have eq4_3 := integral_inv_of_pos (a := t) (b := 1) t0 (by norm_num)
    simp only [mul_zero, mul_one, smul_eq_mul] at eq4_1
    nth_rewrite 2 [intervalIntegral.integral_const_mul] at eq4_1
    rw[← mul_assoc, show (1 - t)⁻¹ * (1 - t) = 1 by field_simp, one_mul] at eq4_1
    simp_rw [← div_eq_mul_inv] at eq4_1
    rw [eq4_1, ← Real.log_inv, ← one_div, ← eq4_3]
    simp_rw [one_mul, sub_zero, ← sub_add, sub_self, zero_add] at eq4_2
    exact eq4_2
  rw[integral_equality_help , intervalIntegral.integral_const_mul, h3,
    intervalIntegral.integral_add, eq3, eq4, ← neg_add, ← Real.log_mul]
  · field_simp
  · positivity
  · positivity
  · have hs_rewrite : ∀ x : ℝ,
        s / (1 - (1 - x) * s) = s * 1 / (1 - (1 - x) * s) := by
      intro x
      simp
    simp_rw [hs_rewrite]
    apply IntervalIntegrable.continuousOn_mul (hg := continuousOn_const)
    apply intervalIntegral.intervalIntegrable_inv
    · intros x hx
      simp only [zero_le_one, Set.uIcc_of_le, Set.mem_Icc] at hx
      intro r
      rw [sub_eq_zero] at r
      have ineq3 : (1 - x) * s ≤ 1 * s := by
        apply mul_le_mul <;> linarith
      rw [one_mul] at ineq3
      linarith
    · apply ContinuousOn.sub continuousOn_const
      apply ContinuousOn.mul ?_ continuousOn_const
      apply ContinuousOn.sub continuousOn_const continuousOn_id
  · have ht_rewrite : ∀ x : ℝ,
        (1 - t) / (1 - (1 - t) * x) = (1 - t) * 1 / (1 - (1 - t) * x) := by
      simp
    simp_rw [ht_rewrite]
    apply IntervalIntegrable.continuousOn_mul (hg := continuousOn_const)
    apply intervalIntegral.intervalIntegrable_inv
    · intro x hx
      simp only [zero_le_one, Set.uIcc_of_le, Set.mem_Icc] at hx
      intro a
      rw [sub_eq_zero] at a
      have ineq : (1 - t) * x ≤ (1 - t) * 1 := by
        apply mul_le_mul <;> linarith
      rw [mul_one] at ineq
      linarith
    apply ContinuousOn.sub continuousOn_const
    apply ContinuousOn.mul continuousOn_const continuousOn_id
  · exact s0
  · linarith
  · exact t0
  · exact t1

end LeanPool.Zeta3Irrational
