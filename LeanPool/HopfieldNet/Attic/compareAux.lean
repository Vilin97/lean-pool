/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Complex.Exponential

set_option checkBinderAnnotations false

theorem compare_swap {α} [LinearOrder α] (x y : α) : compare x y = (compare y x).swap :=
  Eq.symm (Batteries.OrientedCmp.symm y x)

theorem compare_neg_neg {α} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] (x y : α) :
  compare (-x) (-y) = (compare y x) := by
  rcases lt_trichotomy x y with hlt | heq | hgt

  · -- Case: x < y
    -- In an ordered group: x < y implies -y < -x
    have h_neg_lt : -y < -x := neg_lt_neg hlt
    -- When x < y: compare y x = gt and compare (-x) (-y) = gt
    have c1 : compare y x = Ordering.gt := compare_gt_iff_gt.mpr (hlt)
    have c2 : compare (-x) (-y) = Ordering.gt := compare_gt_iff_gt.mpr (h_neg_lt)
    exact c2.trans c1.symm

  · -- Case: x = y
    subst heq
    -- When x = x: compare x x = eq and compare (-x) (-x) = eq
    have c1 : compare x x = Ordering.eq := compare_eq_iff_eq.mpr rfl
    have c2 : compare (-x) (-x) = Ordering.eq := compare_eq_iff_eq.mpr rfl
    exact c2.trans c1.symm

  · -- Case: y < x
    -- In an ordered group: y < x implies -x < -y
    have h_neg_lt : -x < -y := neg_lt_neg hgt
    -- When y < x: compare y x = lt and compare (-x) (-y) = lt
    have c1 : compare y x = Ordering.lt := compare_lt_iff_lt.mpr hgt
    have c2 : compare (-x) (-y) = Ordering.lt := compare_lt_iff_lt.mpr h_neg_lt
    exact c2.trans c1.symm

theorem compare_add_right_eq {α}
    [LinearOrder α] [AddGroup α] [AddRightStrictMono α] (x y z : α) :
  compare (x + z) (y + z) = compare x y := by
  by_cases h : x = y
  · rw [h]
    simp [compare_eq_iff_eq.mpr rfl]
  · cases lt_or_gt_of_ne h with
    | inl hlt =>
      have : x + z < y + z := add_lt_add_right hlt _
      rw [compare_lt_iff_lt.mpr this, compare_lt_iff_lt.mpr hlt]
    | inr hgt =>
      have : y + z < x + z := add_lt_add_right hgt _
      rw [compare_gt_iff_gt.mpr this, compare_gt_iff_gt.mpr hgt]

theorem compare_add_left_eq {α}
    [LinearOrder α] [AddCommGroup α] [AddRightStrictMono α] (x y z : α) :
  compare (z + x) (z + y) = compare x y := by
  rw [add_comm z x, add_comm z y]
  exact compare_add_right_eq x y z

theorem compare_mul_right_eq_of_pos {α}
    [LinearOrder α] [Group α] [MulLeftMono α] [Zero α] [MulPosStrictMono α]
    [Add α] [AddRightStrictMono α] (x y z : α)
    (hz_pos : 0 < z) : compare (x * z) (y * z) = compare x y := by
  by_cases h : x = y
  · rw [h]
    rw [compare_eq_iff_eq.mpr rfl, compare_eq_iff_eq.mpr rfl]
  · cases lt_or_gt_of_ne h with
    | inl hlt =>
      have : x * z < y * z := mul_lt_mul_of_pos_right hlt hz_pos
      rw [compare_lt_iff_lt.mpr this, compare_lt_iff_lt.mpr hlt]
    | inr hgt =>
      have : y * z < x * z := mul_lt_mul_of_pos_right hgt hz_pos
      rw [compare_gt_iff_gt.mpr this, compare_gt_iff_gt.mpr hgt]

theorem compare_mul_left_eq_of_pos {α}
    [LinearOrder α] [CommGroup α] [MulLeftMono α] [Zero α] [Add α] [AddRightStrictMono α]
    [MulPosStrictMono α] (x y z : α) (hz_pos : 0 < z) : compare (z * x) (z * y) = compare x y := by
  rw [mul_comm z x, mul_comm z y]
  exact compare_mul_right_eq_of_pos x y z hz_pos

theorem compare_sub_sub_equiv_compare_add_add {α}
  [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] (x d u v : α) :
  compare (x - d) (u - v) = compare (x + v) (u + d) := by
  by_cases h_eq_diff : x - d = u - v
  · -- Case: x - d = u - v
    rw [compare_eq_iff_eq.mpr h_eq_diff, compare_eq_iff_eq.mpr (sub_eq_sub_iff_add_eq_add.mp h_eq_diff)]
  · -- Case: x - d ≠ u - v
    rcases lt_or_gt_of_ne h_eq_diff with h_lt | h_gt
    · -- Case: x - d < u - v
      rw [compare_lt_iff_lt.mpr h_lt, compare_lt_iff_lt.mpr (sub_lt_sub_iff.mp h_lt)]
    · -- Case: x - d > u - v (which means u - v < x - d)
      rw [compare_gt_iff_gt.mpr h_gt, compare_gt_iff_gt.mpr (sub_lt_sub_iff.mp h_gt)]

-- theorem compare_sq_eq_compare_abs {α}
--     [Ring R] [LinearOrder R] [IsStrictOrderedRing R]
--     (x y : α) :
--   compare (x^2) (y^2) = compare (abs x) (abs y) := by
--   rw [← abs_sq x, ← abs_sq y]
--   by_cases h : abs x = abs y
--   · -- Case: |x| = |y|
--     rw [h]
--     simp [compare_eq_iff_eq.mpr rfl]
--     rw [@compare_eq_iff_eq]
--     exact (sq_eq_sq_iff_abs_eq_abs x y).mpr h
--   · -- Case: |x| ≠ |y|
--     rcases lt_or_gt_of_ne h with hlt | hgt
--     · -- Case: |x| < |y|
--       have h_sq_lt := mul_self_lt_mul_self (abs_nonneg x) hlt
--       rw [compare_lt_iff_lt.mpr hlt]
--       exact compare_lt_iff_lt.mpr (by rw [abs_sq x, abs_sq y]; exact sq_lt_sq.mpr hlt)
--     · -- Case: |x| > |y|
--       have h_sq_gt := mul_self_lt_mul_self (abs_nonneg y) hgt
--       rw [compare_gt_iff_gt.mpr hgt]
--       exact compare_gt_iff_gt.mpr (by rw [abs_sq x, abs_sq y]; exact sq_lt_sq.mpr hgt)
