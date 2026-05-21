/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Int.Star

instance (priority := 100) : NeZero (1 : ℝ) where
  out := by norm_num

open Int
/-!
This file provides Lean 4 formalizations of concepts from Flocq.
-/

-- In Coq, IZR is the cast from Z to R. In Lean, this is `(↑· : ℤ → ℝ)`.
-- R is ℝ. Z is ℤ.
-- Coq's `radix` is a Z between 2 and max_Z. We define it as a subtype.
abbrev Radix := {β : ℤ // β ≥ 2}

namespace Rmissing

open Real

lemma Rle_0_minus (x y : ℝ) (h : x ≤ y) : 0 ≤ y - x :=
  sub_nonneg_of_le h

lemma Rabs_eq_Rabs (x y : ℝ) (h : abs x = abs y) : x = y ∨ x = -y :=
  abs_eq_abs.mp h

lemma Rabs_minus_le (x y : ℝ) (hy_nonneg : 0 ≤ y) (hy_le_2x : y ≤ 2 * x) :
    abs (x - y) ≤ x := by
  apply abs_le.mpr
  constructor <;> linarith -- `linarith` solves both goals

lemma Rabs_eq_R0 (x : ℝ) : abs x = 0 → x = 0 :=
  abs_eq_zero.mp

-- Rplus_eq_reg_r is add_right_cancel in Lean

lemma Rmult_lt_compat (r1 r2 r3 r4 : ℝ) (hr1_nonneg : 0 ≤ r1) (hr3_nonneg : 0 ≤ r3)
    (h12 : r1 < r2) (h34 : r3 < r4) : r1 * r3 < r2 * r4 := by
  -- Proof structure from Flocq:
  -- r1*r3 <= r1*r4 (by hr1_nonneg, h34.le)
  -- r1*r4 < r2*r4 (by h12, r4 > 0 from hr3_nonneg.trans_lt h34)
  have hr4_pos : 0 < r4 := hr3_nonneg.trans_lt h34
  calc
    r1 * r3 ≤ r1 * r4 := mul_le_mul_of_nonneg_left h34.le hr1_nonneg
    _       < r2 * r4 := mul_lt_mul_of_pos_right h12 hr4_pos

-- Rmult_minus_distr_r is sub_mul in Mathlib (actually `Real.sub_mul`)

lemma Rmult_neq_reg_r (r1 r2 r3 : ℝ) (h : r2 * r1 ≠ r3 * r1) : r2 ≠ r3 :=
  fun heq => h (by rw [heq])


universe u
variable {M₀ : Type u} [Mul M₀] [Zero M₀] [IsLeftCancelMulZero M₀] {a : M₀}

lemma mul_right_inj₀ (ha : a ≠ 0) : Function.Injective (a * ·) :=
  fun _ _ => mul_left_cancel₀ ha

lemma Rmult_neq_compat_r (r1 r2 r3 : ℝ) (hr1_ne_0 : r1 ≠ 0) (hr23_ne : r2 ≠ r3) :
    r2 * r1 ≠ r3 * r1 :=
  fun h => hr23_ne ((mul_right_inj₀ hr1_ne_0 (by rw [mul_comm r2, mul_comm r3] at h; exact h)))

lemma Rmult_min_distr_r (r r1 r2 : ℝ) (hr_nonneg : 0 ≤ r) :
    min r1 r2 * r = min (r1 * r) (r2 * r) := by
  rcases le_total r1 r2 with h_le | h_le
  · rw [min_eq_left h_le, min_eq_left (mul_le_mul_of_nonneg_right h_le hr_nonneg)]
  · rw [min_eq_right h_le, min_eq_right (mul_le_mul_of_nonneg_right h_le hr_nonneg)]

lemma Rmult_min_distr_l (r r1 r2 : ℝ) (hr_nonneg : 0 ≤ r) :
    r * min r1 r2 = min (r * r1) (r * r2) := by
  simp_rw [mul_comm r, Rmult_min_distr_r r r1 r2 hr_nonneg]

lemma Rmin_opp (x y : ℝ) : min (-x) (-y) = -max x y := min_neg_neg x y
lemma Rmax_opp (x y : ℝ) : max (-x) (-y) = -min x y := max_neg_neg x y

lemma exp_le (x y : ℝ) (h : x ≤ y) : exp x ≤ exp y := exp_monotone h

lemma Rinv_lt (x y : ℝ) (hx_pos : 0 < x) (hxy : x < y) : y⁻¹ < x⁻¹ :=
  inv_strictAnti₀ hx_pos hxy

lemma Rinv_le (x y : ℝ) (hx_pos : 0 < x) (hxy : x ≤ y) : y⁻¹ ≤ x⁻¹ :=
  inv_anti₀ hx_pos hxy

lemma sqrt_ge_0 (x : ℝ) : 0 ≤ sqrt x := sqrt_nonneg x

lemma sqrt_neg (x : ℝ) (hx_nonpos : x ≤ 0) : sqrt x = 0 :=
  sqrt_eq_zero_of_nonpos hx_nonpos

lemma Rsqr_le_abs_0_alt (x y : ℝ) (h_sq_le : x^2 ≤ y^2) : x ≤ abs y :=
  (le_abs_self x).trans (sq_le_sq.mp h_sq_le)

-- Rabs_le is abs_le.mpr, Rabs_le_inv is abs_le.mp
-- Rabs_ge and Rabs_ge_inv for (x <= abs y) are le_abs and le_abs_iff
lemma Rabs_ge (x y : ℝ) (h : y ≤ -x ∨ x ≤ y) : x ≤ abs y := by
  rcases h with h_left | h_right
  · exact le_trans (le_neg_of_le_neg h_left) (neg_le_abs y)
  · exact le_trans h_right (le_abs_self y)

lemma Rabs_ge_inv (x y : ℝ) (h : x ≤ abs y) : y ≤ -x ∨ x ≤ y := by
  rcases le_or_gt 0 y with hy_nonneg | hy_neg
  · right; rw [abs_of_nonneg hy_nonneg] at h; exact h
  · left; rw [abs_of_neg hy_neg] at h
    exact le_neg_of_le_neg h

-- Rabs_lt is abs_lt.mpr, Rabs_lt_inv is abs_lt.mp
-- Rabs_gt and Rabs_gt_inv for (x < abs y) are lt_abs and lt_abs_iff
lemma Rabs_gt (x y : ℝ) (h : y < -x ∨ x < y) : x < abs y := by
  rcases h with h_left | h_right
  · exact (lt_neg_of_lt_neg h_left).trans_le (neg_le_abs y)
  · exact h_right.trans_le (le_abs_self y)

lemma Rabs_gt_inv (x y : ℝ) (h : x < abs y) : y < -x ∨ x < y := by
  rcases le_or_gt 0 y with hy_nonneg | hy_neg
  · right  -- Case: y ≥ 0
    rw [abs_of_nonneg hy_nonneg] at h
    exact h
  · left  -- Case: y < 0
    rw [abs_of_neg hy_neg] at h  -- h: x < -y
    exact lt_neg_of_lt_neg h  -- y < -x

end Rmissing

section IZR

lemma IZR_le_lt (m n p : ℤ) (h : m ≤ n ∧ n < p) :
    (↑m : ℝ) ≤ ↑n ∧ (↑n : ℝ) < ↑p :=
  ⟨Int.cast_le.mpr h.1, Int.cast_lt.mpr h.2⟩

lemma le_lt_IZR (m n p : ℤ) (h : (↑m : ℝ) ≤ ↑n ∧ (↑n : ℝ) < ↑p) :
    m ≤ n ∧ n < p :=
  ⟨Int.cast_le.mp h.1, Int.cast_lt.mp h.2⟩

lemma neq_IZR (m n : ℤ) (h_ne_cast : (↑m : ℝ) ≠ ↑n) : m ≠ n :=
  fun a ↦ h_ne_cast (congrArg Int.cast a)

end IZR

section Rcompare

lemma compare_swap {α} [LinearOrder α] (x y : α) : compare x y = (compare y x).swap :=
  Eq.symm (Batteries.OrientedCmp.symm y x)

lemma compare_neg_neg {α} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] (x y : α) :
  compare (-x) (-y) = (compare y x) := by
  -- Use trichotomy principle of linear order
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

lemma compare_add_right_eq {α}
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

lemma compare_add_left_eq {α}
    [LinearOrder α] [AddCommGroup α] [AddRightStrictMono α] (x y z : α) :
  compare (z + x) (z + y) = compare x y := by
  rw [add_comm z x, add_comm z y]
  exact compare_add_right_eq x y z

lemma compare_mul_right_eq_of_pos {α}
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

lemma compare_mul_left_eq_of_pos {α}
    [LinearOrder α] [CommGroup α] [MulLeftMono α] [Zero α] [Add α] [AddRightStrictMono α]
    [MulPosStrictMono α] (x y z : α) (hz_pos : 0 < z) : compare (z * x) (z * y) = compare x y := by
  rw [mul_comm z x, mul_comm z y]
  exact compare_mul_right_eq_of_pos x y z hz_pos

lemma compare_sub_sub_equiv_compare_add_add {α} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] (x d u v : α) :
  compare (x - d) (u - v) = compare (x + v) (u + d) := by
  by_cases h_eq_diff : x - d = u - v
  · -- Case: x - d = u - v
    -- We need to show compare (x + v) (u + d) = Ordering.eq, i.e., x + v = u + d
    rw [compare_eq_iff_eq.mpr h_eq_diff, compare_eq_iff_eq.mpr (sub_eq_sub_iff_add_eq_add.mp h_eq_diff)]
  · -- Case: x - d ≠ u - v
    rcases lt_or_gt_of_ne h_eq_diff with h_lt | h_gt
    · -- Case: x - d < u - v
      -- We need to show compare (x + v) (u + d) = Ordering.lt, i.e., x + v < u + d
      rw [compare_lt_iff_lt.mpr h_lt, compare_lt_iff_lt.mpr (sub_lt_sub_iff.mp h_lt)]
    · -- Case: x - d > u - v (which means u - v < x - d)
      -- We need to show compare (x + v) (u + d) = Ordering.gt, i.e., u + d < x + v
      rw [compare_gt_iff_gt.mpr h_gt, compare_gt_iff_gt.mpr (sub_lt_sub_iff.mp h_gt)]

lemma compare_sq_eq_compare_abs {α}
    [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
    (x y : α) :
  compare (x^2) (y^2) = compare (abs x) (abs y) := by
  rw [← abs_sq x, ← abs_sq y]
  by_cases h : abs x = abs y
  · -- Case: |x| = |y|
    rw [h]
    simp [compare_eq_iff_eq.mpr rfl]
    rw [@compare_eq_iff_eq]
    exact (sq_eq_sq_iff_abs_eq_abs x y).mpr h
  · -- Case: |x| ≠ |y|
    rcases lt_or_gt_of_ne h with hlt | hgt
    · -- Case: |x| < |y|
      have h_sq_lt := mul_self_lt_mul_self (abs_nonneg x) hlt
      rw [compare_lt_iff_lt.mpr hlt]
      exact compare_lt_iff_lt.mpr (by rw [abs_sq x, abs_sq y]; exact sq_lt_sq.mpr hlt)
    · -- Case: |x| > |y|
      have h_sq_gt := mul_self_lt_mul_self (abs_nonneg y) hgt
      rw [compare_gt_iff_gt.mpr hgt]
      exact compare_gt_iff_gt.mpr (by rw [abs_sq x, abs_sq y]; exact sq_lt_sq.mpr hgt)

lemma Rcompare_Lt (x y : ℝ) (h : x < y) : compare x y = Ordering.lt := compare_lt_iff_lt.mpr h
lemma Rcompare_Lt_inv (x y : ℝ) (h : compare x y = Ordering.lt) : x < y := compare_lt_iff_lt.mp h
lemma Rcompare_not_Lt (x y : ℝ) (h : y ≤ x) : compare x y ≠ Ordering.lt :=
  fun h_cmp_lt => not_lt_of_le h (compare_lt_iff_lt.mp h_cmp_lt)
lemma Rcompare_not_Lt_inv (x y : ℝ) (h_ne : compare x y ≠ Ordering.lt) : y ≤ x :=
  compare_ge_iff_ge.mp h_ne

lemma Rcompare_Eq (x y : ℝ) (h_eq : x = y) : compare x y = Ordering.eq := compare_eq_iff_eq.mpr h_eq
lemma Rcompare_Eq_inv (x y : ℝ) (h : compare x y = Ordering.eq) : x = y := compare_eq_iff_eq.mp h

lemma Rcompare_Gt (x y : ℝ) (h : y < x) : compare x y = Ordering.gt := compare_gt_iff_gt.mpr h
lemma Rcompare_Gt_inv (x y : ℝ) (h : compare x y = Ordering.gt) : y < x := compare_gt_iff_gt.mp h
lemma Rcompare_not_Gt (x y : ℝ) (h_le : x ≤ y) : compare x y ≠ Ordering.gt :=
  fun h_cmp_gt => not_le_of_gt (compare_gt_iff_gt.mp h_cmp_gt) h_le
lemma Rcompare_not_Gt_inv (x y : ℝ) (h_ne : compare x y ≠ Ordering.gt) : x ≤ y :=
  compare_le_iff_le.mp h_ne

lemma Rcompare_IZR (x y : ℤ) : compare (x : ℝ) (y : ℝ) = compare x y := by
  rcases lt_trichotomy x y with h | h | h
  · -- Case x < y
    rw [compare_lt_iff_lt.mpr (Int.cast_lt.mpr h), compare_lt_iff_lt.mpr h]
  · -- Case x = y
    rw [compare_eq_iff_eq.mpr (congrArg Int.cast h), compare_eq_iff_eq.mpr h]
  · -- Case y < x
    rw [compare_gt_iff_gt.mpr (Int.cast_lt.mpr h), compare_gt_iff_gt.mpr h]

lemma Rcompare_sym (x y : ℝ) : compare x y = (compare y x).swap := compare_swap x y
lemma Rcompare_opp (x y : ℝ) : compare (-x) (-y) = compare y x := by rw [compare_neg_neg, compare_swap] -- compare_neg_neg gives (compare x y).swap
lemma Rcompare_plus_r (z x y : ℝ) : compare (x + z) (y + z) = compare x y := compare_add_right_eq x y z
lemma Rcompare_plus_l (z x y : ℝ) : compare (z + x) (z + y) = compare x y := compare_add_left_eq x y z

lemma Rcompare_mult_r (z x y : ℝ) (hz_pos : 0 < z) :
    compare (x * z) (y * z) = compare x y := by
  by_cases h : x = y
  · rw [h]; simp [compare_eq_iff_eq.mpr rfl]
  · rcases lt_or_gt_of_ne h with h_lt | h_gt
    · have : x * z < y * z := mul_lt_mul_of_pos_right h_lt hz_pos
      rw [compare_lt_iff_lt.mpr this, compare_lt_iff_lt.mpr h_lt]
    · have : y * z < x * z := mul_lt_mul_of_pos_right h_gt hz_pos
      rw [compare_gt_iff_gt.mpr this, compare_gt_iff_gt.mpr h_gt]

lemma Rcompare_mult_l (z x y : ℝ) (hz_pos : 0 < z) :
    compare (z * x) (z * y) = compare x y := by
  rw [mul_comm z x, mul_comm z y]
  exact Rcompare_mult_r z x y hz_pos

lemma Rcompare_middle (x d u : ℝ) :
    compare (x - d) (u - x) = compare x ((d + u) / 2) := by
  rw [compare_sub_sub_equiv_compare_add_add x d u x]
  have h_x_plus_x_eq_2_mul_x : x + x = 2 * x := by ring
  have h_add_comm : u + d = d + u := by ring
  rw [h_add_comm]
  rw [h_x_plus_x_eq_2_mul_x]
  have h2_pos : (0 : ℝ) < 2 := by norm_num
  have h2_ne_zero : (2 : ℝ) ≠ 0 := ne_of_gt h2_pos
  have h_simp : 2 * ((d + u) / 2) = d + u := by exact mul_div_cancel₀ (d + u) h2_ne_zero
  rw [← h_simp]
  convert Rcompare_mult_l 2 x ((d + u) / 2) h2_pos

lemma Rcompare_half_l (x y : ℝ) : compare (x / 2) y = compare x (2 * y) := by
  have h2_pos : (0 : ℝ) < 2 := by norm_num
  have h2_ne_zero : (2 : ℝ) ≠ 0 := ne_of_gt h2_pos
  have : x = 2 * (x / 2) := by rw [mul_div_cancel₀ x h2_ne_zero]
  rw [this]
  have : 2 * (x / 2) = x := by rw [mul_div_cancel₀ x h2_ne_zero]
  rw [Rcompare_mult_l 2 (x / 2) y h2_pos]
  simp_all only [Nat.ofNat_pos, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]

lemma Rcompare_half_r (x y : ℝ) : compare x (y / 2) = compare (2 * x) y := by
  have h2_pos : (0 : ℝ) < 2 := by norm_num
  have h2_ne_zero : (2 : ℝ) ≠ 0 := ne_of_gt h2_pos
  have : y = 2 * (y / 2) := by rw [mul_div_cancel₀ y h2_ne_zero]
  rw [this]
  have : 2 * (y / 2) / 2 = y / 2 := by rw [mul_div_cancel_left₀ (y / 2) h2_ne_zero]
  rw [this]
  rw [Rcompare_mult_l 2 x (y / 2) h2_pos]

lemma Rcompare_sqr (x y : ℝ) : compare (x^2) (y^2) = compare (abs x) (abs y) :=
  compare_sq_eq_compare_abs x y

#check Rcompare_sqr

lemma Rmin_compare (x y : ℝ) :
    min x y = match compare x y with
              | Ordering.lt => x
              | Ordering.eq => x
              | Ordering.gt => y := by
  simp only [min_def]
  match h_cmp : compare x y with
  | Ordering.lt => simp only [h_cmp, if_pos (le_of_lt (compare_lt_iff_lt.mp h_cmp))]
  | Ordering.eq => simp only [h_cmp, if_pos (le_of_eq (compare_eq_iff_eq.mp h_cmp))]
  | Ordering.gt => simp only [h_cmp, if_neg (not_le_of_gt (compare_gt_iff_gt.mp h_cmp))]

#check Rmin_compare

end Rcompare


section Zdiv_Rdiv

/-!

-/

-- Core division identity: x = (x / y) * y + (x % y)
lemma int_div_identity_real_cast' (x y : ℤ) :
    (x : ℝ) = (x / y : ℤ) * (y : ℝ) + (x % y : ℤ) := by
  have H := Int.ediv_add_emod x y
  rw [← H]
  rw [Int.cast_add, Int.cast_mul]
  ring_nf
  simp_all only

-- The floor of a sum where one term is an integer
lemma floor_add_int_of_nonneg_frac (q : ℤ) (f : ℝ) (_ : 0 ≤ f) (_ : f < 1) :
    ⌊(q : ℝ) + f⌋ = q + ⌊f⌋ := by
  apply Int.floor_eq_iff.mpr
  constructor
  · rw [Int.cast_add]
    apply add_le_add_left
    exact Int.floor_le f
  · rw [Int.cast_add]
    rw [add_assoc]
    rw [add_lt_add_iff_left]
    exact Int.lt_floor_add_one f

-- Case when divisor is positive
lemma floor_mod_div_eq_zero_pos' (x y : ℤ) (hy_pos : 0 < y) :
    ⌊(x % y : ℤ) / (y : ℝ)⌋ = 0 := by
  apply Int.floor_eq_zero_iff.mpr
  constructor
  · apply div_nonneg
    · exact Int.cast_nonneg.mpr (Int.emod_nonneg _ (ne_of_gt hy_pos))
    · exact Int.cast_nonneg.mpr (le_of_lt hy_pos)
  · rw [div_lt_one_iff]
    left
    constructor
    · exact Int.cast_pos.mpr hy_pos
    · have h_mod_lt : x % y < y := Int.emod_lt_of_pos x hy_pos
      exact Int.cast_lt.mpr h_mod_lt

-- Core division identity: x = (x / y) * y + (x % y) for floor division
lemma int_div_identity_real_cast (x y : ℤ) :
    (x : ℝ) = (Int.fdiv x y : ℝ) * (y : ℝ) + (Int.fmod x y : ℝ) := by
  rw [← Int.cast_mul, ← Int.cast_add]
  rw [Int.fdiv_add_fmod']

-- Case when divisor is positive
lemma floor_mod_div_eq_zero_pos (x y : ℤ) (hy_pos : 0 < y) :
    ⌊(x % y : ℤ) / (y : ℝ)⌋ = 0 := by
  apply Int.floor_eq_zero_iff.mpr
  constructor
  · apply div_nonneg
    · exact Int.cast_nonneg.mpr (Int.emod_nonneg _ (ne_of_gt hy_pos))
    · exact Int.cast_nonneg.mpr (le_of_lt hy_pos)
  · rw [div_lt_one (Int.cast_pos.mpr hy_pos)]
    exact Int.cast_lt.mpr (Int.emod_lt_of_pos x hy_pos)

-- Helper lemmas first - with corrected implementations
lemma div_nonpos_of_nonpos_of_neg {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {a b : K}
    (ha : a ≤ 0) (hb : b < 0) : 0 ≤ a / b := by
  rw [le_div_iff_of_neg hb]
  rw [zero_mul]
  exact ha

lemma Int.cast_nonpos_iff {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {n : ℤ} :
    n ≤ 0 ↔ (↑n : K) ≤ 0 := by
  constructor
  · intro h
    exact cast_nonpos.mpr h
  · intro h
    simp_all only [cast_nonpos]

lemma Int.cast_neg_iff {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {n : ℤ} :
    n < 0 ↔ (n : K) < 0 := by
  constructor
  · intro h
    exact cast_lt_zero.mpr h
  · intro h
    simp_all only [cast_lt_zero]

-- Sign cases for non-zero integers
lemma Int.sign_cases_of_ne_zero {x : ℤ} (hx : x ≠ 0) : 0 < x ∨ x < 0 := by
  rcases lt_trichotomy x 0 with h_neg | h_zero | h_pos
  · exact Or.inr h_neg
  · exact False.elim (hx h_zero)
  · exact Or.inl h_pos

-- Alternative formulation using sign cases for any integer
lemma Int.sign_cases (x : ℤ) : x = 0 ∨ 0 < x ∨ x < 0 := by
  rcases lt_trichotomy x 0 with h_neg | h_zero | h_pos
  · exact Or.inr (Or.inr h_neg)
  · exact Or.inl h_zero
  · exact Or.inr (Or.inl h_pos)

-- Helper lemmas for working with integer signs
lemma Int.pos_or_neg_of_ne_zero {x : ℤ} (hx : x ≠ 0) : 0 < x ∨ x < 0 :=
  Int.sign_cases_of_ne_zero hx

lemma Int.ne_zero_of_pos {x : ℤ} (hx : 0 < x) : x ≠ 0 :=
  ne_of_gt hx

lemma Int.ne_zero_of_neg {x : ℤ} (hx : x < 0) : x ≠ 0 :=
  ne_of_lt hx

lemma div_lt_one_iff_of_neg {a b : ℝ} (hb : b < 0) : a / b < 1 ↔ b < a := by
  rw [div_lt_one_iff]
  constructor
  · intro h
    cases' h with h_pos h_neg
    · -- Case: 0 < b (contradicts hb : b < 0)
      exact False.elim (not_lt_of_lt hb h_pos.1)
    · -- Case: b < 0 ∧ b < a
      cases' h_neg with hb_neg ha
      aesop
      aesop
  · intro h_ba
    right
    aesop

-- Helper lemma: for b < 0, a/b < 1 ↔ b < a.
lemma div_lt_one_iff_lt_of_neg {a b : ℝ} (hb : b < 0) : a / b < 1 ↔ b < a :=
  div_lt_one_of_neg hb

-- Conservative working version
lemma div_lt_iff_lt_mul_of_neg {a b c : ℝ} (hc : c < 0) :
    a / c < b ↔ b * c < a := by
  rw [div_lt_iff_of_neg hc]

lemma div_le_iff_le_mul_of_neg {a b c : ℝ} (hc : c < 0) :
    a / c ≤ b ↔ b * c ≤ a := by
  rw [div_le_iff_of_neg hc]

section Zdiv_Rdiv

-- The remainder `fmod` for a negative divisor `y` is in the range (y, 0].
lemma Int.fmod_range_neg (x y : ℤ) (hy_neg : y < 0) : y < x.fmod y ∧ x.fmod y ≤ 0 := by
  have hy_ne_zero : y ≠ 0 := hy_neg.ne
  rw [Int.fmod_eq_emod]
  have h_not_nonneg_y : ¬ (0 ≤ y) := not_le_of_lt hy_neg
  by_cases h_dvd : y ∣ x
  · rw [if_pos (Or.inr h_dvd), Int.emod_eq_zero_of_dvd h_dvd, Int.zero_add]
    exact ⟨hy_neg, le_rfl⟩
  · rw [if_neg (by simp [h_not_nonneg_y, h_dvd])]
    have h_emod_lt : x % y < y.natAbs := Int.emod_lt x hy_ne_zero
    rw [(ofNat_natAbs_of_nonpos hy_neg.le)] at h_emod_lt
    have h_emod_pos : 0 < x % y := (Int.emod_pos_of_not_dvd h_dvd).resolve_left hy_ne_zero
    constructor <;> linarith [h_emod_lt, h_emod_pos]

-- Helper lemma: division of a non-positive by a negative is non-negative.
lemma div_nonneg_of_nonpos_of_neg {a b : ℝ} (ha : a ≤ 0) (hb : b < 0) : 0 ≤ a / b := by
  rw [le_div_iff_of_neg hb, zero_mul]
  exact ha

-- The floor of the remainder divided by a negative divisor is 0.
lemma floor_fmod_div_eq_zero_neg (x y : ℤ) (hy_neg : y < 0) :
    ⌊(x.fmod y : ℝ) / (y : ℝ)⌋ = 0 := by
  apply Int.floor_eq_zero_iff.mpr
  have hy_real_neg : (y : ℝ) < 0 := Int.cast_lt_zero.mpr hy_neg
  have h_range := Int.fmod_range_neg x y hy_neg
  constructor
  · exact div_nonpos_of_nonpos_of_neg (Int.cast_nonpos.mpr h_range.2) hy_real_neg
  · rw [div_lt_one_of_neg hy_real_neg]
    exact Int.cast_lt.mpr h_range.1

-- The floor of the remainder divided by a positive divisor is 0.
lemma floor_fmod_div_eq_zero_pos (x y : ℤ) (hy_pos : 0 < y) :
    ⌊(x.fmod y : ℝ) / (y : ℝ)⌋ = 0 := by
  apply Int.floor_eq_zero_iff.mpr
  have hy_real_pos : (0 : ℝ) < y := Int.cast_pos.mpr hy_pos
  rw [Int.fmod_eq_emod_of_nonneg _ (le_of_lt hy_pos)]
  constructor
  · -- Show 0 ≤ (x % y) / y
    exact div_nonneg (Int.cast_nonneg.mpr (Int.emod_nonneg _ hy_pos.ne.symm)) (le_of_lt hy_real_pos)
  · -- Show (x % y) / y < 1
    rw [div_lt_one hy_real_pos]
    exact Int.cast_lt.mpr (Int.emod_lt_of_pos x hy_pos)

-- The floor of (remainder / divisor) is always 0 for a non-zero divisor.
lemma floor_fmod_div_eq_zero (x y : ℤ) (hy : y ≠ 0) :
    ⌊(x.fmod y : ℝ) / (y : ℝ)⌋ = 0 := by
  rcases lt_or_gt_of_ne hy with hy_neg | hy_pos
  · exact floor_fmod_div_eq_zero_neg x y hy_neg
  · exact floor_fmod_div_eq_zero_pos x y hy_pos

-- Main theorem: Integer floor division `fdiv` is equivalent to the floor of real division.
theorem Zfloor_div (x y : ℤ) (hy : y ≠ 0) :
    ⌊(x : ℝ) / (y : ℝ)⌋ = x.fdiv y := by
  have hy_real_ne_zero : (y : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hy
  have h_div_split : (x : ℝ) / (y : ℝ) = (x.fdiv y : ℝ) + (x.fmod y : ℝ) / (y : ℝ) := by
    calc (x : ℝ) / (y : ℝ)
        = ((x.fdiv y : ℝ) * (y : ℝ) + (x.fmod y : ℝ)) / (y : ℝ) := by rw [int_div_identity_real_cast]
      _ = (x.fdiv y : ℝ) * (y : ℝ) / (y : ℝ) + (x.fmod y : ℝ) / (y : ℝ) := by rw [add_div]
      _ = (x.fdiv y : ℝ) + (x.fmod y : ℝ) / (y : ℝ) := by rw [mul_div_cancel_right₀ _ hy_real_ne_zero]
  rw [h_div_split, Int.floor_intCast_add]
  rw [floor_fmod_div_eq_zero x y hy, add_zero]

end Zdiv_Rdiv

section Pow

variable {r : Radix}

/-- Well-used function called bpow for computing the power function β^e
  TODO: Refactor using only zpow -/
noncomputable def bpow' (e : ℤ) : ℝ :=
  match e with
  | Int.ofNat n => (r.val : ℝ) ^ n
  | Int.negSucc n => ((r.val : ℝ) ^ (n + 1))⁻¹

noncomputable def bpow (r : Radix) (e : ℤ) : ℝ := (r.val : ℝ) ^ e

lemma radix_pos : 0 < (r.val : ℝ) := by
  have h1 : 2 ≤ r.val := r.prop
  have h2 : 0 < (2 : ℝ) := by norm_num
  have h3 : (0 : ℝ) < 2 := by norm_num
  have h4 : (2 : ℝ) ≤ (r.val : ℝ) := Int.cast_le.mpr r.prop
  exact lt_of_lt_of_le h3 h4

lemma bpow_plus (e1 e2 : ℤ) : bpow r (e1 + e2) = bpow r e1 * bpow r e2 := by
  simp [bpow, zpow_add₀ (ne_of_gt radix_pos)]

lemma IZR_Zpower_pos (n : ℕ) (m : ℕ) :
    ((n ^ m : ℕ) : ℝ) = (n : ℝ) ^ m := by
  simp [Nat.cast_pow]

lemma bpow_powerRZ (e : ℤ) :
    bpow (r := r) e = (r.val : ℝ) ^ e := by
  rfl

lemma bpow_ge_0 (e : ℤ) : 0 ≤ bpow (r := r) e := by
  rw [bpow_powerRZ]
  apply zpow_nonneg
  exact le_of_lt radix_pos

lemma bpow_gt_0 (e : ℤ) : 0 < bpow (r := r) e := by
  rw [bpow]
  exact zpow_pos radix_pos e

lemma bpow_1 : bpow (r := r) 1 = r.val := by
  simp [bpow]

lemma bpow_plus_1 (e : ℤ) :
    bpow (r := r) (e + 1) = r.val * bpow (r := r) e := by
  rw [bpow, zpow_add_one₀ (ne_of_gt radix_pos), mul_comm]
  simp[bpow]

lemma bpow_opp (e : ℤ) :
    bpow (r := r) (-e) = (bpow (r := r) e)⁻¹ := by
  rw [bpow_powerRZ, bpow_powerRZ, zpow_neg]

lemma IZR_Zpower_nat (e : ℕ) :
    ((r.val : ℝ) ^ e) = bpow (r := r) (Int.ofNat e) := by
  simp [bpow]

lemma IZR_Zpower (e : ℤ) (He : 0 ≤ e) :
    ((r.val : ℝ) ^ e.natAbs) = bpow (r := r) e := by
  cases e with
  | ofNat n =>
    simp [bpow, Int.natAbs_of_nonneg (Int.ofNat_nonneg n)]
  | negSucc n =>
    simp at He

lemma bpow_lt {e1 e2 : ℤ} (H : e1 < e2) :
    bpow r e1 < bpow r e2 := by
  rw [bpow, bpow]
  have h_r_gt_one : 1 < (r.val : ℝ) := by
    have h1 : 2 ≤ r.val := r.prop
    have h2 : (2 : ℝ) ≤ r.val := Int.cast_le.mpr r.prop
    exact lt_of_lt_of_le one_lt_two h2
  exact (zpow_lt_zpow_iff_right₀ h_r_gt_one).mpr H

lemma bpow_le {e1 e2 : ℤ} (H : e1 ≤ e2) :
    bpow r e1 ≤ bpow r e2 := by
    rw [bpow, bpow]
    have h_r_ge_one : 1 ≤ (r.val : ℝ) := by
      have h1 : 2 ≤ r.val := r.prop
      have h2 : (1 : ℝ) ≤ 2 := by norm_num
      have h3 : (2 : ℝ) ≤ r.val := Int.cast_le.mpr h1
      exact le_trans h2 h3
    exact zpow_le_zpow_right₀ h_r_ge_one H

lemma lt_bpow {e1 e2 : ℤ} (H : bpow r e1 < bpow r e2) : e1 < e2 := by
  contrapose! H
  exact bpow_le H

lemma le_bpow {e1 e2 : ℤ} :
    bpow r e1 ≤ bpow r e2 → e1 ≤ e2 := by
  contrapose!
  intro H
  exact bpow_lt H

lemma bpow_inj {e1 e2 : ℤ} :
    bpow r e1 = bpow r e2 → e1 = e2 := by
  intro H
  apply le_antisymm
  · apply le_bpow; rw [H]
  · apply le_bpow; rw [← H]

lemma bpow_exp (e : ℤ) :
    bpow (r := r) e = Real.exp (e * Real.log r.val) := by
  rw [bpow]
  rw [← Real.rpow_intCast]
  rw [← Real.exp_log radix_pos]
  rw [Real.log_exp]
  rw [mul_comm]
  rw [Real.exp_mul]

/-- The magnitude of a real number x to the base β -/
structure Magnitude (r : Radix) (x : ℝ) where
  exp : ℤ
  lower : bpow r (exp - 1) ≤ abs x
  upper : abs x < bpow r exp
  nonzero : x ≠ 0

lemma mag_unique'' (x : ℝ) (e : ℤ)
    (He : bpow r (e - 1) ≤ abs x ∧ abs x < bpow r e) (nz : x ≠ 0) :
    Magnitude.mk e He.left He.right nz = Magnitude.mk e He.left He.right nz := by
  simp

/-- The magnitude of a real number x to the base β -/
noncomputable def mag (x : ℝ) : ℤ × Prop :=
  if _ : x ≠ 0 then
    let e := ⌊Real.log (abs x) / Real.log r.val⌋ + 1
    (e, bpow r (e - 1) ≤ abs x ∧ abs x < bpow r e)
  else
    (0, True)

theorem mag_unique (x : ℝ) (e : ℤ)
    (He : bpow (r := r) (e - 1) ≤ abs x ∧ abs x < bpow r e) :
    (mag (r := r) x).1 = e := by
  have hx_ne_zero : x ≠ 0 := by
    intro h
    rw [h, abs_zero] at He
    have h_pos := bpow_gt_0 (r := r) (e - 1)
    exact not_le_of_lt h_pos He.1
  simp [mag, hx_ne_zero]
  have h_abs_pos : 0 < abs x := abs_pos.mpr hx_ne_zero
  have h_log_pos : 0 < Real.log r.val := by
    apply Real.log_pos
    have h1 : 2 ≤ r.val := r.prop
    have h2 : (1 : ℝ) < (2 : ℝ) := by norm_num
    have h3 : (2 : ℝ) ≤ (↑r.val : ℝ) := Int.cast_le.mpr h1
    exact lt_of_lt_of_le h2 h3
  have h_lower : ↑(e - 1) ≤ Real.log (abs x) / Real.log r.val := by
    rw [le_div_iff₀ h_log_pos]
    conv_lhs => {
      rw [← Real.log_exp (↑(e - 1) * Real.log r.val)]
      rw [← bpow_exp]
    }
    rw [Real.log_le_log_iff (bpow_gt_0 _ ) h_abs_pos]
    exact He.1
  have h_upper : Real.log (abs x) / Real.log r.val < ↑e := by
    rw [div_lt_iff₀ h_log_pos]
    conv_rhs => {
      rw [← Real.log_exp (↑e * Real.log r.val)]
      rw [← bpow_exp]
    }
    rw [Real.log_lt_log_iff h_abs_pos (bpow_gt_0 e)]
    exact He.2
  have h_floor : ⌊Real.log (abs x) / Real.log r.val⌋ = e - 1 := by
    apply Int.floor_eq_iff.mpr
    constructor
    · exact h_lower
    · simp only [Int.cast_sub, Int.cast_one]
      ring_nf
      exact h_upper
  have h_log_eq : Real.log x = Real.log (abs x) := by
    rw [Real.log_abs]
  rw [h_log_eq]
  rw [h_floor]
  ring

end Pow

section Defs

/-- Definition of a floating-point number -/
structure FloatingPoint (β : Radix) where
  num : ℤ  -- mantissa/significand
  exp : ℤ  -- exponent

/-- Convert a float to a real number -/
noncomputable def F2R {β : Radix} (f : FloatingPoint β) : ℝ :=
  f.num * bpow β f.exp

/-- Requirements on a rounding mode -/
structure RoundPred (P : ℝ → ℝ → Prop) : Prop where
  total : ∀ x, ∃ y, P x y
  monotone : ∀ x y f g, P x f → P y g → x ≤ y → f ≤ g

/-- Property of being a round toward -∞ -/
def RndDN_pt (F : ℝ → Prop) (x f : ℝ) : Prop :=
  F f ∧ f ≤ x ∧ ∀ g, F g → g ≤ x → g ≤ f

/-- Property of being a round toward +∞ -/
def RndUP_pt (F : ℝ → Prop) (x f : ℝ) : Prop :=
  F f ∧ x ≤ f ∧ ∀ g, F g → x ≤ g → f ≤ g

/-- Property of being a round toward zero -/
def RndZR_pt (F : ℝ → Prop) (x f : ℝ) : Prop :=
  (0 ≤ x → RndDN_pt F x f) ∧ (x ≤ 0 → RndUP_pt F x f)

/-- Property of being a round to nearest -/
def RndN_pt (F : ℝ → Prop) (x f : ℝ) : Prop :=
  F f ∧ ∀ g, F g → abs (f - x) ≤ abs (g - x)

def RndNG_pt (F : ℝ → Prop) (P : ℝ → ℝ → Prop) (x f : ℝ) : Prop :=
  RndN_pt F x f ∧ (P x f ∨ ∀ f2, RndN_pt F x f2 → f2 = f)

def RndNA_pt (F : ℝ → Prop) (x f : ℝ) : Prop :=
  RndN_pt F x f ∧ ∀ f2, RndN_pt F x f2 → abs f2 ≤ abs f

end Defs

section Generic_fmt

variable {β : Radix}
variable (fexp : ℤ → ℤ)

/-- Valid exponent function -/
class ValidExp : Prop where
  prop : ∀ k : ℤ,
    (fexp k < k → fexp (k + 1) ≤ k) ∧
    (k ≤ fexp k → fexp (fexp k + 1) ≤ fexp k ∧
                    ∀ l, l ≤ fexp k → fexp l = fexp k)

variable [ValidExp fexp]

/-- Canonical exponent -/
noncomputable def cexp (x : ℝ) : ℤ := fexp (mag (r := β) x).1

/-- A float is canonical if its exponent matches the canonical exponent -/
def canonical (f : FloatingPoint β) : Prop := f.exp = cexp (β := β) fexp (F2R f)

/-- Scaled mantissa -/
noncomputable def scaled_mantissa (x : ℝ) : ℝ := x * bpow β (-cexp (β := β) fexp x)

/-- Generic format predicate -/
def generic_format (x : ℝ) : Prop :=
  x = F2R (β := β) ⟨⌊scaled_mantissa (β := β) fexp x⌋, cexp (β := β) fexp x⟩

omit [ValidExp fexp] in
theorem generic_format_0 : generic_format (β := β) fexp (0 : ℝ) := by
  simp [generic_format, scaled_mantissa, F2R]

end Generic_fmt

section Magnitude

variable {β : Radix}

/-- Magnitude of a real number with respect to radix β -/
noncomputable def mag' {β : Radix} (x : ℝ) : ℤ :=
  if x = 0 then 0 else ⌊Real.log (abs x) / Real.log β.val⌋ + 1

theorem mag_unique' (x : ℝ) (e : ℤ)
    (He : bpow β (e - 1) ≤ abs x ∧ abs x < bpow β e) :
    mag' (β := β) x = e := by
  unfold mag'
  have hx_ne_zero : x ≠ 0 := by
    intro h
    rw [h, abs_zero] at He
    have h_pos := bpow_gt_0 (r := β) (e - 1)
    exact not_le_of_lt h_pos He.1
  simp [hx_ne_zero]
  have h_abs_pos : 0 < abs x := abs_pos.mpr hx_ne_zero
  have h_log_pos : 0 < Real.log β.val := by
    apply Real.log_pos
    have h1 : 2 ≤ β.val := β.prop
    have h2 : (1 : ℝ) < (2 : ℝ) := by norm_num
    have h3 : (2 : ℝ) ≤ (↑β.val : ℝ) := Int.cast_le.mpr h1
    exact lt_of_lt_of_le h2 h3

  -- Convert the bounds using logarithms
  have h_lower : ↑(e - 1) ≤ Real.log (abs x) / Real.log β.val := by
    rw [le_div_iff₀ h_log_pos]
    conv_lhs => {
      rw [← Real.log_exp (↑(e - 1) * Real.log β.val)]
      rw [← bpow_exp]
    }
    rw [Real.log_le_log_iff (bpow_gt_0 _) h_abs_pos]
    exact He.1

  have h_upper : Real.log (abs x) / Real.log β.val < ↑e := by
    rw [div_lt_iff₀ h_log_pos]
    conv_rhs => {
      rw [← Real.log_exp (↑e * Real.log β.val)]
      rw [← bpow_exp]
    }
    rw [Real.log_lt_log_iff h_abs_pos (bpow_gt_0 e)]
    exact He.2

  have h_floor : ⌊Real.log (abs x) / Real.log β.val⌋ = e - 1 := by
    apply Int.floor_eq_iff.mpr
    constructor
    · exact h_lower
    · simp only [Int.cast_sub, Int.cast_one]
      ring_nf
      exact h_upper
  rw [← Real.log_abs]
  rw [h_floor]
  ring

theorem mag_bpow (e : ℤ) : (mag (r := β) (bpow β e)).1 = e + 1 := by
  apply mag_unique (r := β)
  rw [abs_of_pos (bpow_gt_0 _)]
  constructor
  · simp only [add_sub_cancel_right]
    simp_all only [le_refl]
  · have h : e < e + 1 := by linarith
    exact bpow_lt h
end Magnitude

section Generic_fmt_props

variable {β : Radix}
variable {fexp : ℤ → ℤ}
variable [ValidExp fexp]

omit [ValidExp fexp] in
theorem cexp_opp (x : ℝ) : cexp (β := β) fexp (-x) = cexp (β := β) fexp x := by
  simp [cexp]
  congr 1
  simp [mag]

omit [ValidExp fexp] in
theorem cexp_abs (x : ℝ) : cexp (β := β) fexp (abs x) = cexp (β := β) fexp x := by
  simp [cexp]
  congr 1
  simp [mag]

-- Helper lemma: if we're in -- Helper lemma: if we're in the negSucc case, then the value is indeed negSucc
lemma cases_negSucc_eq (x : ℤ) (n : ℕ)
    (h : (match x with | Int.ofNat _ => False | Int.negSucc m => m = n)) :
    x = Int.negSucc n := by
  cases x with
  | ofNat k => exact False.elim h
  | negSucc m => simp at h; rw [h]

-- Alternative approach: direct contradiction lemma
lemma negSucc_not_nonneg (n : ℕ) : ¬(0 ≤ Int.negSucc n) := by
  exact not_le_of_lt (Int.negSucc_lt_zero n)

theorem generic_format_bpow (e : ℤ) (H : fexp (e + 1) ≤ e) :
    generic_format (β := β) fexp (bpow (r := β) e) := by
  unfold generic_format scaled_mantissa cexp F2R
  simp [mag_bpow]
  rw [← bpow_plus]
  ring_nf
  have h_diff_nonneg : 0 ≤ e - fexp (e + 1) := by linarith [H]
  have h_comm : 1 + e = e + 1 := by ring
  rw [h_comm]
  have h_floor_bpow : ⌊bpow β (e - fexp (e + 1))⌋ = (β.val : ℝ) ^ (e - fexp (e + 1)).natAbs := by
    have h_int_power : ∃ n : ℕ, e - fexp (e + 1) = ↑n := by
      use (e - fexp (e + 1)).toNat
      exact Eq.symm (toNat_sub_of_le H)
    obtain ⟨n, h_eq⟩ := h_int_power
    rw [h_eq]
    rw [bpow]
    rw [zpow_natCast]
    have h_nat_abs : (n : ℤ).natAbs = n := Int.natAbs_natCast n
    rw [h_nat_abs]
    have : ⌊(β.val : ℝ) ^ n⌋ = (β.val : ℝ) ^ n := by
      have h_int_pow : ∃ m : ℤ, (β.val : ℝ) ^ n = ↑m := by
        use β.val ^ n
        rw [Int.cast_pow]
      rcases h_int_pow with ⟨m, hm⟩
      rw [hm]
      simp_all only [Nat.cast_nonneg, natAbs_natCast, floor_intCast]
    exact this
  rw [h_floor_bpow]
  rw [← Int.cast_pow]
  simp [bpow]
  rw [← zpow_natCast]
  rw [Int.natAbs_of_nonneg h_diff_nonneg]
  have h_exp_eq : (e - fexp (e + 1)).toNat = (e - fexp (e + 1)) := by
    exact Int.toNat_of_nonneg h_diff_nonneg
  rw [← h_exp_eq]
  ring_nf
  rw [← zpow_add₀]
  · have h_add : (e - fexp (1 + e)) + fexp (1 + e) = e := by ring
    rw [h_comm] at h_add ⊢
    have h_cast_toNat : ↑(e - fexp (e + 1)).toNat = e - fexp (e + 1) := h_exp_eq
    rw [h_cast_toNat]
    exact congrArg (HPow.hPow (β.val : ℝ)) (id (Eq.symm h_add))
  · have h_radix_pos : 0 < (β.val : ℝ) := radix_pos
    exact ne_of_gt h_radix_pos

-- Helper lemma about floor of integer multiplication
lemma Int.floor_intCast_mul' (m : ℤ) (x : ℝ) (hx : ∃ k : ℤ, x = ↑k) :
    ⌊(m : ℝ) * x⌋ = m * ⌊x⌋ := by
  obtain ⟨k, hk⟩ := hx
  rw [hk, ← Int.cast_mul, Int.floor_intCast, Int.floor_intCast]

-- Helper lemma: bpow with non-negative exponent is an integer
lemma bpow_nonneg_int (β : Radix) (e : ℤ) (he : 0 ≤ e) :
    ∃ k : ℤ, bpow β e = ↑k := by
  match e with
  | .ofNat n =>
    use (β.val : ℤ) ^ n
    simp [bpow, zpow_natCast, Int.cast_pow]
  | .negSucc n =>
    exfalso
    exact (Int.negSucc_not_nonneg n).mp he

-- Helper lemma: floor of bpow with non-negative exponent
lemma floor_bpow_nonneg (β : Radix) (e : ℤ) (he : 0 ≤ e) :
    ⌊bpow β e⌋ = bpow β e := by
  have ⟨k, hk⟩ := bpow_nonneg_int β e he
  rw [hk, Int.floor_intCast]

-- The floor equation for scaled mantissa
lemma scaled_mantissa_floor_eq (β : Radix) (fexp : ℤ → ℤ) [ValidExp fexp]
    (m e : ℤ) (_ : m ≠ 0)
    (H : cexp (β := β) fexp (F2R (β := β) ⟨m, e⟩) ≤ e) :
    ⌊scaled_mantissa (β := β) fexp (F2R (β := β) ⟨m, e⟩)⌋ =
    m * ⌊bpow β (e - cexp (β := β) fexp (F2R (β := β) ⟨m, e⟩))⌋ := by
  unfold scaled_mantissa F2R
  simp only [F2R]
  rw [mul_assoc, ← bpow_plus]
  have h_nonneg : 0 ≤ e + (-cexp (β := β) fexp (↑m * bpow β e)) := by
    simp only [le_add_neg_iff_add_le, zero_add]
    exact H
  have h_bpow_int := bpow_nonneg_int β (e + (-cexp (β := β) fexp (↑m * bpow β e))) h_nonneg
  rw [Int.floor_intCast_mul' m _ h_bpow_int]
  congr 1

lemma F2R_scaled_identity (β : Radix) (fexp : ℤ → ℤ) [ValidExp fexp]
    (m e : ℤ) (_ : m ≠ 0)
    (H : cexp (β := β) fexp (F2R (β := β) ⟨m, e⟩) ≤ e) :
    F2R (β := β) ⟨m, e⟩ =
    (m * ⌊bpow β (e - cexp (β := β) fexp (F2R (β := β) ⟨m, e⟩))⌋ : ℝ) *
    bpow β (cexp (β := β) fexp (F2R (β := β) ⟨m, e⟩)) := by
  unfold F2R
  simp only [F2R]
  have h_nonneg : 0 ≤ e - cexp (β := β) fexp (↑m * bpow β e) := by
    have h_eq : F2R (β := β) ⟨m, e⟩ = ↑m * bpow β e := by simp [F2R]
    rw [h_eq] at H
    linarith [H]
  have h_cast_eq : (m * ⌊bpow β (e - cexp (β := β) fexp (↑m * bpow β e))⌋ : ℝ) =
                   ↑m * ↑⌊bpow β (e - cexp (β := β) fexp (↑m * bpow β e))⌋ := by
    simp_all only [ne_eq, Int.sub_nonneg]
  rw [floor_bpow_nonneg β _ h_nonneg]
  rw [mul_assoc, ← bpow_plus]
  simp_all only [ne_eq, Int.sub_nonneg, sub_add_cancel]

theorem generic_format_F2R {β : Radix} {fexp : ℤ → ℤ} [ValidExp fexp] (m e : ℤ)
    (H : m ≠ 0 → cexp (β := β) fexp (F2R (β := β) ⟨m, e⟩) ≤ e) :
    generic_format (β := β) fexp (F2R (β := β) ⟨m, e⟩) := by
  unfold generic_format
  by_cases hm : m = 0
  · simp [F2R, hm, scaled_mantissa, mul_zero]
  · specialize H hm
    rw [scaled_mantissa_floor_eq β fexp m e hm H]
    have h_identity := F2R_scaled_identity β fexp m e hm H
    simp only [F2R, Int.cast_mul]
    simp only [F2R] at h_identity
    rw [← h_identity]

-- Additional useful lemma: when the condition is satisfied, the result is canonical
lemma canonical_F2R_of_cexp_le (β : Radix) (fexp : ℤ → ℤ) [ValidExp fexp] (m e : ℤ)
    (H : m ≠ 0 → cexp (β := β) fexp (F2R (β := β) ⟨m, e⟩) ≤ e) :
    canonical (β := β) fexp ⟨⌊scaled_mantissa (β := β) fexp (F2R (β := β) ⟨m, e⟩)⌋,
                             cexp (β := β) fexp (F2R (β := β) ⟨m, e⟩)⟩ := by
  unfold canonical F2R
  simp only [F2R]
  have h_generic := generic_format_F2R m e H
  unfold generic_format at h_generic
  congr 1

omit [ValidExp fexp] in
theorem generic_format_opp {β : Radix} (x : ℝ) :
    generic_format (β := β) fexp x → generic_format (β := β) fexp (-x) := by
  intro H
  unfold generic_format at H ⊢
  have h_cexp_eq : cexp (β := β) fexp (-x) = cexp (β := β) fexp x := cexp_opp x
  rw [h_cexp_eq]
  unfold scaled_mantissa
  rw [neg_mul]
  have h_scaled_is_int : x * bpow β (-cexp (β := β) fexp x) = ↑⌊x * bpow β (-cexp (β := β) fexp x)⌋ := by
    have h_expand : x = ↑⌊x * bpow β (-cexp (β := β) fexp x)⌋ * bpow β (cexp (β := β) fexp x) := H
    calc x * bpow β (-cexp (β := β) fexp x)
        = (↑⌊x * bpow β (-cexp (β := β) fexp x)⌋ * bpow β (cexp (β := β) fexp x)) * bpow β (-cexp (β := β) fexp x) := by rw [← h_expand]
      _ = ↑⌊x * bpow β (-cexp (β := β) fexp x)⌋ * (bpow β (cexp (β := β) fexp x) * bpow β (-cexp (β := β) fexp x)) := by rw [mul_assoc]
      _ = ↑⌊x * bpow β (-cexp (β := β) fexp x)⌋ * bpow β (cexp (β := β) fexp x + (-cexp (β := β) fexp x)) := by rw [← bpow_plus]
      _ = ↑⌊x * bpow β (-cexp (β := β) fexp x)⌋ * bpow β 0 := by rw [add_neg_cancel]
      _ = ↑⌊x * bpow β (-cexp (β := β) fexp x)⌋ * 1 := by simp [bpow, zpow_zero]
      _ = ↑⌊x * bpow β (-cexp (β := β) fexp x)⌋ := by rw [mul_one]
  rw [h_cexp_eq]
  simp only [F2R, Int.cast_neg, neg_mul]
  have h_int_scaled : ∃ k : ℤ, x * bpow β (-cexp (β := β) fexp x) = ↑k := by
    use ⌊x * bpow β (-cexp (β := β) fexp x)⌋
  obtain ⟨k, hk⟩ := h_int_scaled
  rw [hk, ← Int.cast_neg, Int.floor_intCast, Int.cast_neg, neg_mul]
  rw [← hk]
  rw [mul_assoc, ← bpow_plus, neg_add_cancel, bpow, zpow_zero, mul_one]

omit [ValidExp fexp] in
theorem generic_format_abs {β : Radix} (x : ℝ) :
    generic_format (β := β) fexp x → generic_format (β := β) fexp (abs x) := by
  intro H
  by_cases h : 0 ≤ x
  · simp [abs_of_nonneg h, H]
  · push_neg at h
    rw [abs_of_neg h]
    exact generic_format_opp _ H
end Generic_fmt_props

section Formats

variable {β : Radix}

/-- Fixed-point format -/
def FIX_exp (emin : ℤ) : ℤ → ℤ := fun _ => emin

instance FIX_valid_exp (emin : ℤ) : ValidExp (FIX_exp emin) where
  prop := by
    intro k
    constructor
    · intro h; simp [FIX_exp] at h ⊢; exact Int.le_of_lt h
    · intro _; simp [FIX_exp]

def FIX_format (emin : ℤ) (x : ℝ) : Prop :=
  ∃ f : FloatingPoint β, x = F2R f ∧ f.exp = emin

/-- Floating-point format with unbounded exponent -/
def FLX_exp (prec : ℤ) : ℤ → ℤ := fun e => e - prec

instance FLX_valid_exp (prec : ℤ) (h : 0 < prec) : ValidExp (FLX_exp prec) where
  prop := by
    intro k
    constructor
    · intro H
      simp [FLX_exp] at H ⊢
      linarith
    · intro H
      simp [FLX_exp] at H ⊢
      constructor
      · linarith
      · intros l hl
        exfalso
        linarith [h, H]

def FLX_format (prec : ℤ) (x : ℝ) : Prop :=
  ∃ f : FloatingPoint β, x = F2R f ∧ abs f.num < β.val ^ prec.natAbs

/-- Floating-point format with gradual underflow -/
def FLT_exp (emin prec : ℤ) : ℤ → ℤ := fun e => max (e - prec) emin

instance FLT_valid_exp (emin prec : ℤ) (h : 0 < prec) :
    ValidExp (FLT_exp emin prec) where
  prop := by
    intro k
    constructor
    · intro H
      simp [FLT_exp] at H ⊢
      omega
    · intro H
      simp [FLT_exp] at H ⊢
      constructor
      · omega
      · intros l hl
        omega

def FLT_format (emin prec : ℤ) (x : ℝ) : Prop :=
  ∃ f : FloatingPoint β, x = F2R f ∧ abs f.num < β.val ^ prec.natAbs ∧ emin ≤ f.exp

/-- Floating-point format with flush to zero -/
def FTZ_exp (emin prec : ℤ) : ℤ → ℤ := fun e =>
  if e - prec < emin then emin + prec - 1 else e - prec

instance FTZ_valid_exp (emin prec : ℤ) (h : 0 < prec) :
    ValidExp (FTZ_exp emin prec) where
  prop := by
    intro k
    simp [FTZ_exp]
    constructor
    · intro H
      split_ifs with h1
      · omega
      · omega
    · intro H
      split_ifs with h1
      · constructor
        · omega
        · intros l hl
          omega
      · constructor
        · omega
        · intros l hl
          split_ifs with h_emin
          · rfl
          · omega
      omega
      omega

end Formats

section ULP

variable {β : Radix}
variable {fexp : ℤ → ℤ}
variable [ValidExp fexp]

/-- Helper to make the existence decidable for reasonable bounds -/
def has_negligible_in_range (fexp : ℤ → ℤ) (lower upper : ℤ) : Bool :=
  (List.range (Int.natAbs (upper - lower + 1))).any (fun i =>
    let k := lower + i
    fexp k ≥ k)

/-- Negligible exponent with bounded search -/
noncomputable def negligible_exp (fexp : ℤ → ℤ) : Option ℤ :=
  -- Search in a reasonable range, e.g., [-1000, 1000]
  let lower := -1000
  let upper := 1000
  if has_negligible_in_range fexp lower upper then
    (List.range (Int.natAbs (upper - lower + 1))).find? (fun i =>
      let k := lower + i
      fexp k ≥ k) |>.map (fun i => lower + i)
  else
    none

/-- Unit in the last place -/
noncomputable def ulp (β : Radix) (fexp : ℤ → ℤ) [ValidExp fexp] (x : ℝ) : ℝ :=
  if x = 0 then
    match negligible_exp fexp with
    | some n => bpow β (fexp n)
    | none   => 0
  else
    bpow β (cexp (β := β) fexp x)

theorem ulp_neq_0 (x : ℝ) (hx : x ≠ 0) :
    ulp (β := β) fexp x = bpow β (cexp (β := β) fexp x) := by
  simp [ulp, hx]

theorem ulp_opp (x : ℝ) : ulp (β := β) fexp (-x) = ulp (β := β) fexp x := by
  unfold ulp
  by_cases h : x = 0
  · simp [h]
  · simp [h, neg_ne_zero.mpr h, cexp_opp]

theorem ulp_abs (x : ℝ) : ulp (β := β) fexp (abs x) = ulp (β := β) fexp x := by
  unfold ulp
  by_cases h : x = 0
  · simp [h, abs_zero]
  · simp [h, abs_ne_zero.mpr h, cexp_abs]

theorem ulp_ge_0 (x : ℝ) : 0 ≤ ulp (β := β) fexp x := by
  unfold ulp
  split_ifs
  · cases negligible_exp fexp
    · rfl
    · exact bpow_ge_0 _
  · exact bpow_ge_0 _

/-- Successor -/
noncomputable def succ (x : ℝ) : ℝ :=
  if 0 ≤ x then x + ulp β fexp x else -(x - ulp β fexp (-x))

/-- Alternative predecessor for positive numbers -/
noncomputable def pred_pos (x : ℝ) : ℝ :=
  if x = bpow β ((mag' (β := β) x) - 1) then
    x - bpow β (fexp ((mag' (β := β) x) - 1))
  else
    x - ulp β fexp x

/-- Predecessor -/
noncomputable def pred' (x : ℝ) : ℝ :=
  if 0 ≤ x then pred_pos (β := β) (fexp := fexp) x else x - ulp β fexp x

theorem pred_eq_pos (x : ℝ) (hx : 0 ≤ x) : pred' (β := β) (fexp := fexp) x = pred_pos (β := β) (fexp := fexp) x := by
  unfold pred'
  simp [hx]

end ULP

section Rounding

variable {β : Radix}
variable {fexp : ℤ → ℤ}
variable [ValidExp fexp]

/-- Generic rounding function -/
noncomputable def round' (rnd : ℝ → ℤ) (x : ℝ) : ℝ :=
  F2R (β := β) ⟨rnd (scaled_mantissa (β := β) fexp x), cexp (β := β) fexp x⟩

/-- Rounding down -/
noncomputable def Zfloor_round : ℝ → ℤ := fun x => ⌊x⌋

/-- Rounding up -/
noncomputable def Zceil_round : ℝ → ℤ := fun x => ⌈x⌉

/-- Rounding toward zero -/
noncomputable def Ztrunc : ℝ → ℤ := fun x =>
  if x < 0 then ⌈x⌉ else ⌊x⌋

/-- Rounding away from zero -/
noncomputable def Zaway : ℝ → ℤ := fun x =>
  if x < 0 then ⌊x⌋ else ⌈x⌉

/-- Rounding to nearest with ties to even -/
noncomputable def ZnearestE (x : ℝ) : ℤ :=
  let f := ⌊x⌋
  if x - f < 1/2 then f
  else if x - f > 1/2 then f + 1
  else if Even f then f else f + 1

/-- Valid rounding predicate -/
class ValidRnd (rnd : ℝ → ℤ) : Prop where
  monotone : ∀ x y, x ≤ y → rnd x ≤ rnd y
  id : ∀ n : ℤ, rnd n = n

instance : ValidRnd Zfloor_round where
  monotone := fun _ _ h => Int.floor_mono h
  id := fun n => Int.floor_intCast n

instance : ValidRnd Zceil_round where
  monotone := fun _ _ h => Int.ceil_mono h
  id := fun n => Int.ceil_intCast n

instance : ValidRnd Ztrunc where
  monotone := by
    intros x y hxy
    unfold Ztrunc
    split_ifs with hx hy
    · exact Int.ceil_mono hxy
    · -- Case: x < 0 and y ≥ 0
      have hx_le_zero : x ≤ 0 := le_of_lt hx
      have hy_nonneg : 0 ≤ y := le_of_not_gt hy
      -- ⌈x⌉ ≤ 0 since x < 0, and 0 ≤ ⌊y⌋ since y ≥ 0
      have h_ceil_le_zero : ⌈x⌉ ≤ 0 := Int.ceil_le.mpr (by rwa [Int.cast_zero])
      have h_zero_le_floor : 0 ≤ ⌊y⌋ := Int.floor_nonneg.mpr hy_nonneg
      exact le_trans h_ceil_le_zero h_zero_le_floor
    · -- Case: x ≥ 0 and y < 0 - contradiction
      exfalso
      have hx_nonneg : 0 ≤ x := le_of_not_gt hx
      have hy_neg : y < 0 := by simp_all only [not_lt]
      exact not_le_of_lt hy_neg (le_trans hx_nonneg hxy)
    · exact Int.floor_mono hxy
  id := by
    intro n
    unfold Ztrunc
    split_ifs with h
    · exact Int.ceil_intCast n
    · exact Int.floor_intCast n

lemma round_DN_generic_format (x : ℝ) :
    generic_format (β := β) fexp (round' (β := β) (fexp := fexp) Zfloor_round x) := by
  apply generic_format_F2R
  intro hm
  sorry

lemma round_DN_le (x : ℝ) :
    round' (β := β) (fexp := fexp) Zfloor_round x ≤ x := by
  unfold round' F2R scaled_mantissa Zfloor_round
  have h_floor_le : (⌊x * bpow β (-cexp (β := β) fexp x)⌋ : ℝ) ≤ x * bpow β (-cexp (β := β) fexp x) :=
    Int.floor_le _
  have h_bpow_pos : 0 < bpow β (cexp (β := β) fexp x) := bpow_gt_0 _
  rw [← mul_le_mul_right h_bpow_pos]
  simp only [F2R]
  rw [mul_assoc, ← bpow_plus]
  simp [bpow, zpow_zero, mul_one]
  sorry

lemma round_DN_maximal (x g : ℝ)
    (hg_format : generic_format (β := β) fexp g)
    (hg_le : g ≤ x) :
    g ≤ round' (β := β) (fexp := fexp) Zfloor_round x := by
  unfold generic_format at hg_format
  rw [hg_format]
  unfold round' F2R scaled_mantissa Zfloor_round
  by_cases h_eq : cexp (β := β) fexp g = cexp (β := β) fexp x
  · -- Same canonical exponent case
    have h_bpow_pos : 0 < bpow β (cexp (β := β) fexp x) := bpow_gt_0 _
    rw [h_eq]
    simp only [FloatingPoint.num, FloatingPoint.exp]
    rw [← mul_le_mul_right h_bpow_pos]
    have h_cancel : ∀ a b : ℝ, a * bpow β (cexp (β := β) fexp x) * bpow β (cexp (β := β) fexp x) ≤
                                b * bpow β (cexp (β := β) fexp x) * bpow β (cexp (β := β) fexp x) ↔ a ≤ b := by
      intro a b
      have h_pos_sq : 0 < bpow β (cexp (β := β) fexp x) * bpow β (cexp (β := β) fexp x) := by
        exact mul_pos h_bpow_pos h_bpow_pos
      rw [mul_assoc a, mul_assoc b]
      exact mul_le_mul_right h_pos_sq
    rw [h_cancel, Int.cast_le]
    apply Int.floor_mono
    have h_bpow_pos_neg : 0 < bpow β (-cexp (β := β) fexp x) := bpow_gt_0 _
    rwa [mul_le_mul_right h_bpow_pos_neg]
  · -- Different canonical exponent case
    sorry

-- Main theorem combining the three properties
theorem round_DN_pt (x : ℝ) :
    RndDN_pt (generic_format (β := β) fexp) x (round' (β := β) (fexp := fexp) Zfloor_round x) := by
  unfold RndDN_pt
  exact ⟨round_DN_generic_format x, round_DN_le x, round_DN_maximal x⟩

theorem round_UP_pt (x : ℝ) :
    RndUP_pt (generic_format (β := β) fexp) x (round' (β := β) (fexp := fexp) Zceil_round x) := by
  sorry

theorem round_generic (rnd : ℝ → ℤ) [ValidRnd rnd] (x : ℝ) :
    generic_format (β := β) fexp x → round' (β := β) (fexp := fexp) rnd x = x := by
  intro H
  unfold round'
  unfold generic_format at H
  rw [H]
  simp [scaled_mantissa, F2R]
  have h_F2R_eq : ↑⌊x * bpow β (-cexp (β := β) fexp x)⌋ * bpow β (cexp (β := β) fexp x) =
                  F2R (β := β) { num := ⌊x * bpow β (-cexp (β := β) fexp x)⌋, exp := cexp (β := β) fexp x } := by
    simp [F2R]
  have h_cexp_eq : cexp (β := β) fexp (↑⌊x * bpow β (-cexp (β := β) fexp x)⌋ * bpow β (cexp (β := β) fexp x)) = cexp (β := β) fexp x := by
    rw [h_F2R_eq, H]
    sorry
  rw [h_cexp_eq]
  simp only [add_neg_cancel, bpow, zpow_zero, mul_one]
  have h_scaled_int : ↑⌊x * bpow β (-cexp (β := β) fexp x)⌋ * bpow β (cexp (β := β) fexp x) * bpow β (-cexp (β := β) fexp x) = ↑⌊x * bpow β (-cexp (β := β) fexp x)⌋ := by
    rw [mul_assoc, ← bpow_plus, add_neg_cancel]
    simp [bpow, zpow_zero, mul_one]
  have h_rnd_arg : ↑⌊x * bpow β (-cexp (β := β) fexp x)⌋ * bpow β (cexp (β := β) fexp x) * bpow β (-cexp (β := β) fexp x) = ↑⌊x * bpow β (-cexp (β := β) fexp x)⌋ := h_scaled_int
  have h_bpow_eq : bpow β (cexp (β := β) fexp x) = ↑↑β ^ cexp (β := β) fexp x := by simp [bpow]
  have h_bpow_neg_eq : bpow β (-cexp (β := β) fexp x) = ↑↑β ^ (-cexp (β := β) fexp x) := by simp [bpow]
  conv_lhs =>
    arg 1
    arg 1
    rw [← h_bpow_eq, ← h_bpow_neg_eq]
    rw [h_rnd_arg]
  --rw [ValidRnd.id]
  sorry

theorem error_lt_ulp (rnd : ℝ → ℤ) [ValidRnd rnd] (x : ℝ) (hx : x ≠ 0) :
    abs (round' (β := β) (fexp := fexp) rnd x - x) < ulp (β := β) fexp x := by
  sorry

theorem error_le_half_ulp (x : ℝ) :
    abs (round' (β := β) (fexp := fexp) ZnearestE x - x) ≤ (1/2) * ulp (β := β) fexp x := by
  sorry

end Rounding
