/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import LeanPool.HopfieldNet.compareAux

set_option checkBinderAnnotations false
set_option linter.dupNamespace false


-- In Coq, IZR is the cast from Z to R. In Lean, this is `(↑· : ℤ → ℝ)`.
-- R is ℝ. Z is ℤ.
-- Coq's `radix` is a Z between 2 and max_Z. We define it as a subtype.
abbrev Radix := {β : ℤ // β ≥ 2}

namespace Rmissing
open Real

theorem Rle_0_minus (x y : ℝ) (h : x ≤ y) : 0 ≤ y - x :=
  sub_nonneg_of_le h
theorem Rabs_eq_Rabs (x y : ℝ) (h : abs x = abs y) : x = y ∨ x = -y :=
  abs_eq_abs.mp h
theorem Rabs_minus_le (x y : ℝ) (hy_nonneg : 0 ≤ y) (hy_le_2x : y ≤ 2 * x) :
    abs (x - y) ≤ x := by
  apply abs_le.mpr
  constructor <;> linarith -- `linarith` solves both goals

theorem Rabs_eq_R0 (x : ℝ) : abs x = 0 → x = 0 :=
  abs_eq_zero.mp

-- Rplus_eq_reg_r is add_right_cancel in Lean

theorem Rmult_lt_compat (r1 r2 r3 r4 : ℝ) (hr1_nonneg : 0 ≤ r1) (hr3_nonneg : 0 ≤ r3)
    (h12 : r1 < r2) (h34 : r3 < r4) : r1 * r3 < r2 * r4 := by
  -- Proof structure from Flocq:
  -- r1*r3 <= r1*r4 (by hr1_nonneg, h34.le)
  -- r1*r4 < r2*r4 (by h12, r4 > 0 from hr3_nonneg.trans_lt h34)
  have hr4_pos : 0 < r4 := hr3_nonneg.trans_lt h34
  calc
    r1 * r3 ≤ r1 * r4 := mul_le_mul_of_nonneg_left h34.le hr1_nonneg
    _       < r2 * r4 := mul_lt_mul_of_pos_right h12 hr4_pos

theorem Rmult_neq_reg_r (r1 r2 r3 : ℝ) (h : r2 * r1 ≠ r3 * r1) : r2 ≠ r3 :=
  fun heq => h (by rw [heq])

universe u
variable {M₀ : Type u} [Mul M₀] [Zero M₀] [IsLeftCancelMulZero M₀] {a : M₀}

lemma mul_right_inj₀ (ha : a ≠ 0) : Function.Injective (a * ·) :=
  fun _ _ => mul_left_cancel₀ ha
theorem Rmult_neq_compat_r (r1 r2 r3 : ℝ) (hr1_ne_0 : r1 ≠ 0) (hr23_ne : r2 ≠ r3) :
    r2 * r1 ≠ r3 * r1 :=
  fun h => hr23_ne ((mul_right_inj₀ hr1_ne_0 (by rw [mul_comm r2, mul_comm r3] at h; exact h)))
theorem Rmult_min_distr_r (r r1 r2 : ℝ) (hr_nonneg : 0 ≤ r) :
    min r1 r2 * r = min (r1 * r) (r2 * r) := by
  rcases le_total r1 r2 with h_le | h_le
  · rw [min_eq_left h_le, min_eq_left (mul_le_mul_of_nonneg_right h_le hr_nonneg)]
  · rw [min_eq_right h_le, min_eq_right (mul_le_mul_of_nonneg_right h_le hr_nonneg)]
theorem Rmult_min_distr_l (r r1 r2 : ℝ) (hr_nonneg : 0 ≤ r) :
    r * min r1 r2 = min (r * r1) (r * r2) := by
  simp_rw [mul_comm r, Rmult_min_distr_r r r1 r2 hr_nonneg]
theorem Rmin_opp (x y : ℝ) : min (-x) (-y) = -max x y := min_neg_neg x y
theorem Rmax_opp (x y : ℝ) : max (-x) (-y) = -min x y := max_neg_neg x y
theorem exp_le (x y : ℝ) (h : x ≤ y) : exp x ≤ exp y := exp_monotone h
theorem Rinv_lt (x y : ℝ) (hx_pos : 0 < x) (hxy : x < y) : y⁻¹ < x⁻¹ :=
  inv_strictAnti₀ hx_pos hxy
theorem Rinv_le (x y : ℝ) (hx_pos : 0 < x) (hxy : x ≤ y) : y⁻¹ ≤ x⁻¹ :=
  inv_anti₀ hx_pos hxy
theorem sqrt_ge_0 (x : ℝ) : 0 ≤ sqrt x := sqrt_nonneg x
theorem sqrt_neg (x : ℝ) (hx_nonpos : x ≤ 0) : sqrt x = 0 :=
  sqrt_eq_zero_of_nonpos hx_nonpos

lemma Rsqr_le_abs_0_alt (x y : ℝ) (h_sq_le : x^2 ≤ y^2) : x ≤ abs y :=
  (le_abs_self x).trans (sq_le_sq.mp h_sq_le)

theorem Rabs_le_inv (x y : ℝ) (h : abs x ≤ y) : -y ≤ x ∧ x ≤ y :=
  abs_le.mp h

-- Rabs_le is abs_le.mpr, Rabs_le_inv is abs_le.mp
-- Rabs_ge and Rabs_ge_inv for (x <= abs y) are le_abs and le_abs_iff
theorem Rabs_ge (x y : ℝ) (h : y ≤ -x ∨ x ≤ y) : x ≤ abs y := by
  rcases h with h_left | h_right
  · exact le_trans (le_neg_of_le_neg h_left) (neg_le_abs y)
  · exact le_trans h_right (le_abs_self y)

theorem Rabs_ge_inv (x y : ℝ) (h : x ≤ abs y) : y ≤ -x ∨ x ≤ y := by
  rcases le_or_gt 0 y with hy_nonneg | hy_neg
  · right; rw [abs_of_nonneg hy_nonneg] at h; exact h
  · left; rw [abs_of_neg hy_neg] at h
    exact le_neg_of_le_neg h

theorem Rabs_lt (x y : ℝ) (h : -y < x ∧ x < y) : abs x < y :=
  abs_lt.mpr h

theorem Rabs_lt_inv (x y : ℝ) (h : abs x < y) : -y < x ∧ x < y :=
  abs_lt.mp h

-- Rabs_lt is abs_lt.mpr, Rabs_lt_inv is abs_lt.mp
-- Rabs_gt and Rabs_gt_inv for (x < abs y) are lt_abs and lt_abs_iff
theorem Rabs_gt (x y : ℝ) (h : y < -x ∨ x < y) : x < abs y := by
  rcases h with h_left | h_right
  · exact (lt_neg_of_lt_neg h_left).trans_le (neg_le_abs y)
  · exact h_right.trans_le (le_abs_self y)

theorem Rabs_gt_inv (x y : ℝ) (h : x < abs y) : y < -x ∨ x < y := by
  rcases le_or_gt 0 y with hy_nonneg | hy_neg
  · right  -- Case: y ≥ 0
    rw [abs_of_nonneg hy_nonneg] at h
    exact h
  · left  -- Case: y < 0
    rw [abs_of_neg hy_neg] at h  -- h: x < -y
    exact lt_neg_of_lt_neg h  -- y < -x

end Rmissing

section IZR

theorem IZR_le_lt (m n p : ℤ) (h : m ≤ n ∧ n < p) :
    (↑m : ℝ) ≤ ↑n ∧ (↑n : ℝ) < ↑p :=
  ⟨Int.cast_le.mpr h.1, Int.cast_lt.mpr h.2⟩

theorem le_lt_IZR (m n p : ℤ) (h : (↑m : ℝ) ≤ ↑n ∧ (↑n : ℝ) < ↑p) :
    m ≤ n ∧ n < p :=
  ⟨Int.cast_le.mp h.1, Int.cast_lt.mp h.2⟩

theorem neq_IZR (m n : ℤ) (h_ne_cast : (↑m : ℝ) ≠ ↑n) : m ≠ n :=
  fun a ↦ h_ne_cast (congrArg Int.cast a)

end IZR

inductive Rcompare_prop (x y : ℝ) : Ordering → Prop
| lt : x < y → Rcompare_prop x y Ordering.lt
| eq : x = y → Rcompare_prop x y Ordering.eq
| gt : y < x → Rcompare_prop x y Ordering.gt

theorem Rcompare_spec (x y : ℝ) : Rcompare_prop x y (compare x y) :=
  match lt_trichotomy x y with
  | Or.inl hlt =>
      have : compare x y = Ordering.lt := compare_lt_iff_lt.mpr hlt
      this ▸ Rcompare_prop.lt hlt
  | Or.inr (Or.inl heq) =>
      have : compare x y = Ordering.eq := compare_eq_iff_eq.mpr heq
      this ▸ Rcompare_prop.eq heq
  | Or.inr (Or.inr hgt) =>
      have : compare x y = Ordering.gt := compare_gt_iff_gt.mpr hgt
      this ▸ Rcompare_prop.gt hgt

section Rcompare

theorem Rcompare_Lt (x y : ℝ) (h : x < y) : compare x y = Ordering.lt := compare_lt_iff_lt.mpr h
theorem Rcompare_Lt_inv (x y : ℝ) (h : compare x y = Ordering.lt) : x < y := compare_lt_iff_lt.mp h
theorem Rcompare_not_Lt (x y : ℝ) (h : y ≤ x) : compare x y ≠ Ordering.lt :=
  fun h_cmp_lt => not_lt_of_le h (compare_lt_iff_lt.mp h_cmp_lt)


theorem Rcompare_not_Lt_inv (x y : ℝ) (h_ne : compare x y ≠ Ordering.lt) : y ≤ x :=
  compare_ge_iff_ge.mp h_ne
theorem Rcompare_Eq (x y : ℝ) (h_eq : x = y) : compare x y = Ordering.eq := compare_eq_iff_eq.mpr h_eq
theorem Rcompare_Eq_inv (x y : ℝ) (h : compare x y = Ordering.eq) : x = y := compare_eq_iff_eq.mp h
theorem Rcompare_Gt (x y : ℝ) (h : y < x) : compare x y = Ordering.gt := compare_gt_iff_gt.mpr h

theorem Rcompare_Gt_inv (x y : ℝ) (h : compare x y = Ordering.gt) : y < x := compare_gt_iff_gt.mp h

theorem Rcompare_not_Gt (x y : ℝ) (h_le : x ≤ y) : compare x y ≠ Ordering.gt :=
  fun h_cmp_gt => not_le_of_gt (compare_gt_iff_gt.mp h_cmp_gt) h_le

theorem Rcompare_not_Gt_inv (x y : ℝ) (h_ne : compare x y ≠ Ordering.gt) : x ≤ y :=
  compare_le_iff_le.mp h_ne

theorem Rcompare_IZR (x y : ℤ) : compare (x : ℝ) (y : ℝ) = compare x y := by
  rcases lt_trichotomy x y with h | h | h
  · -- Case x < y
    rw [compare_lt_iff_lt.mpr (Int.cast_lt.mpr h), compare_lt_iff_lt.mpr h]
  · -- Case x = y
    rw [compare_eq_iff_eq.mpr (congrArg Int.cast h), compare_eq_iff_eq.mpr h]
  · -- Case y < x
    rw [compare_gt_iff_gt.mpr (Int.cast_lt.mpr h), compare_gt_iff_gt.mpr h]

theorem Rcompare_sym (x y : ℝ) : compare x y = (compare y x).swap := compare_swap x y

theorem Rcompare_opp (x y : ℝ) : compare (-x) (-y) = compare y x := by rw [compare_neg_neg, compare_swap]

theorem Rcompare_plus_r (z x y : ℝ) : compare (x + z) (y + z) = compare x y := compare_add_right_eq x y z

theorem Rcompare_plus_l (z x y : ℝ) : compare (z + x) (z + y) = compare x y := compare_add_left_eq x y z

theorem Rcompare_mult_r (z x y : ℝ) (hz_pos : 0 < z) :
    compare (x * z) (y * z) = compare x y := by
  by_cases h : x = y
  · rw [h]; simp [compare_eq_iff_eq.mpr rfl]
  · rcases lt_or_gt_of_ne h with h_lt | h_gt
    · have : x * z < y * z := mul_lt_mul_of_pos_right h_lt hz_pos
      rw [compare_lt_iff_lt.mpr this, compare_lt_iff_lt.mpr h_lt]
    · have : y * z < x * z := mul_lt_mul_of_pos_right h_gt hz_pos
      rw [compare_gt_iff_gt.mpr this, compare_gt_iff_gt.mpr h_gt]

theorem Rcompare_mult_l (z x y : ℝ) (hz_pos : 0 < z) :
    compare (z * x) (z * y) = compare x y := by
  rw [mul_comm z x, mul_comm z y]
  exact Rcompare_mult_r z x y hz_pos

theorem Rcompare_middle (x d u : ℝ) :
    compare (x - d) (u - x) = compare x ((d + u) / 2) := by
  rw [compare_sub_sub_equiv_compare_add_add x d u x]
  have h_x_plus_x_eq_2_mul_x : x + x = 2 * x := by ring
  have h_add_comm : u + d = d + u := by ring
  rw [h_add_comm]
  rw [h_x_plus_x_eq_2_mul_x]
  have h2_pos : (0 : ℝ) < 2 := by norm_num
  have h2_ne_zero : (2 : ℝ) ≠ 0 := ne_of_gt h2_pos
  have h_simp : 2 * ((d + u) / 2) = d + u := mul_div_cancel₀ (d + u) h2_ne_zero
  rw [← h_simp]
  convert Rcompare_mult_l 2 x ((d + u) / 2) h2_pos

theorem Rcompare_half_l (x y : ℝ) : compare (x / 2) y = compare x (2 * y) := by
  have h2_pos : (0 : ℝ) < 2 := by norm_num
  rw [← Rcompare_mult_r 2 (x / 2) y h2_pos]
  simp only [isUnit_iff_ne_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    IsUnit.div_mul_cancel]
  rw [mul_comm]

theorem Rcompare_half_r (x y : ℝ) : compare x (y / 2) = compare (2 * x) y := by
  have h2_pos : (0 : ℝ) < 2 := by norm_num
  rw [← Rcompare_mult_r 2 x (y / 2) h2_pos]
  simp only [isUnit_iff_ne_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    IsUnit.div_mul_cancel]
  rw [mul_comm]

--Theorem Rcompare_sqr : This is in `compareAux.lean`

theorem Rmin_compare (x y : ℝ) : min x y = match compare x y with
  | Ordering.lt => x
  | Ordering.eq => x
  | Ordering.gt => y := by
  rcases lt_trichotomy x y with hlt | heq | hgt
  · rw [compare_lt_iff_lt.mpr hlt, min_eq_left_of_lt hlt]
  · rw [compare_eq_iff_eq.mpr heq, heq, min_self]
  · rw [compare_gt_iff_gt.mpr hgt, min_eq_right_of_lt hgt]

end Rcompare


namespace Rle_bool

/-- Boolean comparison for ≤ on ℝ using explicit computation.
  This is computable if `x` and `y` are computable reals (e.g., floats).
  For computable reals, use a typeclass or structure that supports effective comparison. -/
@[irreducible, inline] def Rle_bool {α : Type*} [Ord α] (x y : α) : Bool :=
  match compare x y with
  | Ordering.lt | Ordering.eq => true
  | Ordering.gt => false

inductive Rle_bool_prop {α : Type*} [Ord α] [LE α] [LT α] (x y : α) : Bool → Prop
| true_  : x ≤ y → Rle_bool_prop x y true
| false_ : y < x → Rle_bool_prop x y false

theorem Rle_bool_spec {α : Type*} [Ord α] [LE α] [LT α] (x y : α) :
  Rle_bool_prop x y (Rle_bool x y) := by {
    unfold Rle_bool
--     unfold Rle_bool.
-- case Rcompare_spec ; constructor.
-- now apply Rlt_le.
-- rewrite H.
-- apply Rle_refl.
-- exact H.
-- Qed.
    sorry
  }

theorem Rle_bool_true {α : Type*} [Ord α] [LE α]
  [LT α] (x y : α) (h : x ≤ y) : Rle_bool x y = true := sorry
-- Proof.
-- intros x y Hxy.
-- case Rle_bool_spec ; intros H.
-- apply refl_equal.
-- elim (Rlt_irrefl x).
-- now apply Rle_lt_trans with y.
-- Qed.

theorem Rle_bool_false {α : Type*} [Ord α] [LE α] [LT α] (x y : α)
  (h : y < x) : Rle_bool x y = false := by sorry
-- Proof.
-- intros x y Hxy.
-- case Rle_bool_spec ; intros H.
-- elim (Rlt_irrefl x).
-- now apply Rle_lt_trans with y.
-- apply refl_equal.
-- Qed.

end Rle_bool

section Rlt_bool

open Ordering

/-- Boolean comparison for < on α using compare. -/
@[irreducible, inline] def Rlt_bool {α : Type*} [Ord α] (x y : α) : Bool :=
  match compare x y with
  | Ordering.lt => true
  | _ => false

inductive Rlt_bool_prop {α : Type*} [Ord α] [LE α] [LT α] (x y : α) : Bool → Prop
| true_  : x < y → Rlt_bool_prop x y true
| false_ : y ≤ x → Rlt_bool_prop x y false

theorem Rlt_bool_spec {α : Type*} [Ord α] [LE α] [LT α] (x y : α) :
  Rlt_bool_prop x y (Rlt_bool x y) := by sorry

theorem negb_Rlt_bool {α : Type*} [Ord α] (x y : α) :
  ¬ (Rle_bool.Rle_bool x y) = Rlt_bool y x := by
  unfold Rle_bool.Rle_bool
  sorry

theorem negb_Rle_bool {α : Type*} [Ord α] (x y : α) :
  !(Rlt_bool x y) = Rle_bool.Rle_bool y x := by
  unfold Rlt_bool Rle_bool.Rle_bool
  sorry
  -- rw [compare_swap x y]
  -- cases compare y x <;> simp


theorem Rlt_bool_true {α : Type*} [Ord α] [LE α] [LT α]
 (x y : α) (h : x < y) : Rlt_bool x y = true := by
  unfold Rlt_bool
  sorry
  --rw [compare_lt_iff_lt.mpr h]

theorem Rlt_bool_false {α : Type*} [Ord α] [LE α] [LT α]
  (x y : α) (h : y ≤ x) : Rlt_bool x y = false := by
  unfold Rlt_bool
  sorry
  --rw [compare_le_iff_le.mpr h]
  --rfl

theorem Rlt_bool_opp {α : Type*} [Ord α] [Neg α] (x y : α) :
  Rlt_bool (-x) (-y) = Rlt_bool y x := by
  unfold Rlt_bool
  sorry
  --rw [compare_neg_neg, compare_swap]
  --cases compare y x <;> rfl

end Rlt_bool

section Req_bool

/-- Boolean equality for α using compare. -/
@[irreducible, inline] def Req_bool {α : Type*} [Ord α] (x y : α) : Bool :=
  match compare x y with
  | Ordering.eq => true
  | _ => false

inductive Req_bool_prop {α : Type*} [Ord α] [BEq α] (x y : α) : Bool → Prop
| true_  : x = y → Req_bool_prop x y true
| false_ : x ≠ y → Req_bool_prop x y false

theorem Req_bool_spec {α : Type*} [Ord α] [BEq α] (x y : α) :
  Req_bool_prop x y (Req_bool x y) := sorry
  -- match compare x y with
  -- | Ordering.eq   => Req_bool_prop.true_ rfl
  -- | _             => Req_bool_prop.false_ (fun h => by
  --     have : compare x y = Ordering.eq := compare_eq_iff_eq.mpr h
  --     contradiction)

theorem Req_bool_true {α : Type*} [Ord α] [BEq α] (x y : α) (h : x = y) : Req_bool x y = true := by
  unfold Req_bool
  sorry
  --rw [compare_eq_iff_eq.mpr h]

theorem Req_bool_false {α : Type*} [Ord α] [BEq α] (x y : α) (h : x ≠ y) : Req_bool x y = false := by
  unfold Req_bool
  cases compare x y with
  | eq => sorry
  | lt | gt => rfl

end Req_bool
-- End Req_bool.

noncomputable section Floor_Ceil

open Int Real

/-- The floor of a real number as an integer. -/
def Zfloor (x : ℝ) : ℤ := Int.floor x

/-- The ceiling of a real number as an integer. -/
def Zceil (x : ℝ) : ℤ := Int.ceil x

theorem Zfloor_lb (x : ℝ) : (Zfloor x : ℝ) ≤ x :=
  Int.floor_le x

theorem Zfloor_ub (x : ℝ) : x < (Zfloor x : ℝ) + 1 :=
  Int.lt_floor_add_one x

theorem Zfloor_lub (n : ℤ) (x : ℝ) (h : (n : ℝ) ≤ x) : n ≤ Zfloor x := sorry
  --Int.le_floor h

theorem Zfloor_imp (n : ℤ) (x : ℝ) (h : (n : ℝ) ≤ x ∧ x < (n + 1 : ℝ)) : Zfloor x = n :=
  Int.floor_eq_iff.mpr h

theorem Zfloor_IZR (n : ℤ) : Zfloor (n : ℝ) = n := sorry
  --Int.floor_coe n

theorem Zfloor_le (x y : ℝ) (h : x ≤ y) : Zfloor x ≤ Zfloor y :=
  Int.floor_mono h

theorem Zceil_ub (x : ℝ) : x ≤ (Zceil x : ℝ) :=
  Int.le_ceil x

theorem Zceil_lb (x : ℝ) : ((Zceil x : ℝ)) < x + 1 :=
  by stop
    rw [←Int.cast_add, Int.ceil_add_one]
    exact Int.floor_lt x

theorem Zceil_glb (n : ℤ) (x : ℝ) (h : x ≤ (n : ℝ)) : Zceil x ≤ n := by stop
  exact Int.ceil_le h

theorem Zceil_imp (n : ℤ) (x : ℝ) (h : ((n - 1 : ℝ)) < x ∧ x ≤ (n : ℝ)) : Zceil x = n := by stop
  exact Int.ceil_eq_iff.mpr h

theorem Zceil_IZR (n : ℤ) : Zceil (n : ℝ) = n := by stop
  exact Int.ceil_coe n

theorem Zceil_le (x y : ℝ) (h : x ≤ y) : Zceil x ≤ Zceil y :=
  Int.ceil_mono h

theorem Zceil_floor_neq (x : ℝ) (h : (Zfloor x : ℝ) ≠ x) : Zceil x = Zfloor x + 1 :=
  by stop
    have : (Zfloor x : ℝ) < x ∨ x < (Zfloor x : ℝ) + 1 := by
      left; exact lt_of_le_of_ne (Int.floor_le x) h
    rw [Int.ceil_eq_iff]
    constructor
    · linarith [Int.floor_le x]
    · linarith [Int.lt_floor_add_one x]

/-- Truncate a real to the nearest integer toward zero. -/
def Ztrunc (x : ℝ) : ℤ := if x < 0 then Zceil x else Zfloor x

theorem Ztrunc_IZR (n : ℤ) : Ztrunc (n : ℝ) = n :=
  by
    dsimp [Ztrunc]
    split_ifs with h
    · exact Zceil_IZR n
    · exact Zfloor_IZR n

theorem Ztrunc_floor (x : ℝ) (h : 0 ≤ x) : Ztrunc x = Zfloor x :=
  by
    dsimp [Ztrunc]
    split_ifs with h'
    · exfalso; linarith
    · rfl

theorem Ztrunc_ceil (x : ℝ) (h : x ≤ 0) : Ztrunc x = Zceil x :=
  by stop
    dsimp [Ztrunc]
    split_ifs with h'
    · rfl
    · have : x = 0 := le_antisymm h (not_lt.mp h')
      rw [this, Zceil_IZR 0, Zfloor_IZR 0]

theorem Ztrunc_le (x y : ℝ) (h : x ≤ y) : Ztrunc x ≤ Ztrunc y :=
  by stop
    dsimp [Ztrunc]
    by_cases hx : x < 0
    · by_cases hy : y < 0
      · exact Zceil_le x y h
      · have : x < 0 ∧ 0 ≤ y := ⟨hx, le_of_not_lt hy⟩
        have : Zceil x ≤ 0 := Zceil_glb 0 x (le_of_lt hx)
        have : 0 ≤ Zfloor y := Zfloor_lb y
        linarith
    · have : 0 ≤ x := le_of_not_lt hx
      by_cases hy : y < 0
      · have : x ≤ 0 := h.trans (le_of_lt hy)
        rw [Ztrunc_ceil x this, Ztrunc_floor y (le_of_not_lt hy)]
        exact Zceil_le x y h
      · exact Zfloor_le x y h

theorem Ztrunc_opp (x : ℝ) : Ztrunc (-x) = -Ztrunc x :=
  by stop
    dsimp [Ztrunc]
    by_cases hx : x < 0
    · rw [if_pos (lt_of_lt_of_le (neg_neg_of_pos hx) (le_refl _))]
      rw [if_neg hx]
      rw [Zceil, Zfloor]
      simp [Int.ceil_neg, Int.floor_neg]
    · rw [if_neg (not_lt.mpr (le_of_not_lt hx))]
      rw [if_pos (neg_neg_of_nonneg (le_of_not_lt hx))]
      rw [Zceil, Zfloor]
      simp [Int.ceil_neg, Int.floor_neg]

/-- Truncate away from zero. -/
def Zaway (x : ℝ) : ℤ := if x < 0 then Zfloor x else Zceil x

theorem Zaway_IZR (n : ℤ) : Zaway (n : ℝ) = n :=
  by
    dsimp [Zaway]
    split_ifs with h
    · exact Zfloor_IZR n
    · exact Zceil_IZR n

theorem Zaway_ceil (x : ℝ) (h : 0 ≤ x) : Zaway x = Zceil x :=
  by
    dsimp [Zaway]
    split_ifs with h'
    · exfalso; linarith
    · rfl

theorem Zaway_floor (x : ℝ) (h : x ≤ 0) : Zaway x = Zfloor x :=
  by stop
    dsimp [Zaway]
    split_ifs with h'
    · rfl
    · have : x = 0 := le_antisymm h (not_lt.mp h')
      rw [this, Zceil_IZR 0, Zfloor_IZR 0]

theorem Zaway_le (x y : ℝ) (h : x ≤ y) : Zaway x ≤ Zaway y :=
  by stop
    dsimp [Zaway]
    by_cases hx : x < 0
    · by_cases hy : y < 0
      · exact Zfloor_le x y h
      · have : x < 0 ∧ 0 ≤ y := ⟨hx, le_of_not_lt hy⟩
        have : Zfloor x ≤ 0 := Zfloor_lub 0 x (le_of_lt hx)
        have : 0 ≤ Zceil y := Zceil_ub y
        linarith
    · have : 0 ≤ x := le_of_not_lt hx
      by_cases hy : y < 0
      · have : x ≤ 0 := h.trans (le_of_lt hy)
        rw [Zaway_floor x this, Zaway_ceil y (le_of_not_lt hy)]
        exact Zfloor_le x y h
      · exact Zceil_le x y h

theorem Zaway_opp (x : ℝ) : Zaway (-x) = -Zaway x :=
  by stop
    dsimp [Zaway]
    by_cases hx : x < 0
    · rw [if_pos (lt_of_lt_of_le (neg_neg_of_pos hx) (le_refl _))]
      rw [if_neg hx]
      rw [Zceil, Zfloor]
      simp [Int.ceil_neg, Int.floor_neg]
    · rw [if_neg (not_lt.mpr (le_of_not_lt hx))]
      rw [if_pos (neg_neg_of_nonneg (le_of_not_lt hx))]
      rw [Zceil, Zfloor]
      simp [Int.ceil_neg, Int.floor_neg]


theorem Zaway_abs (x : ℝ) : Zaway (|x|) = Int.natAbs (Zaway x) := by stop
  dsimp [Zaway]
  by_cases hx : x < 0
  · -- Case: x < 0
    have h_abs : |x| = -x := abs_of_neg hx
    rw [h_abs]
    -- Zaway (-x) = if -x < 0 then Zfloor (-x) else Zceil (-x)
    have h_negx_nonneg : 0 ≤ -x := by linarith
    rw [if_neg (not_lt.mpr h_negx_nonneg)]
    -- Zaway x = Zfloor x
    rw [if_pos hx]
    -- Int.natAbs (Zfloor x) = Int.natAbs (Zceil (-x))
    rw [Int.natAbs_of_nonpos (Zfloor x) (Int.floor_nonpos_of_neg hx)]
    -- Zceil (-x) = -Zfloor x
    rw [Int.ceil_neg, Int.natAbs_neg]
    rfl
  · -- Case: x ≥ 0
    have h_abs : |x| = x := abs_of_nonneg (le_of_not_lt hx)
    rw [h_abs]
    -- Zaway x = Zceil x
    rw [if_neg hx]
    -- Zaway (|x|) = Zceil x
    rw [if_neg (not_lt.mpr (le_of_not_lt hx))]
    -- Int.natAbs (Zceil x) = Int.natAbs (Zceil x)
    rfl

end Floor_Ceil

/--
If `Zfloor x ≠ x`, then
`compare (x - Zfloor x) (1/2) = compare (x - Zfloor x) (Zceil x - x)`.
-/
theorem Rcompare_floor_ceil_middle (x : ℝ) (h : (Zfloor x : ℝ) ≠ x) :
  compare (x - (Zfloor x : ℝ)) (1/2) = compare (x - (Zfloor x : ℝ)) ((Zceil x : ℝ) - x) := by
  -- Use Zceil_floor_neq to rewrite Zceil x
  have hZceil : (Zceil x : ℝ) = (Zfloor x : ℝ) + 1 := sorry--Zceil_floor_neq x h
  rw [hZceil]
  -- Now compare (x - Zfloor x) (1/2) = compare (x - Zfloor x) ((Zfloor x + 1) - x)
  -- Let d := x - Zfloor x, so (Zfloor x + 1) - x = 1 - d
  let d := x - (Zfloor x : ℝ)
  have : (Zfloor x : ℝ) + 1 - x = 1 - d := by ring
  rw [this]
  -- Now, compare d (1/2) = compare d (1 - d)
  -- Do case analysis on compare d (1/2)
  cases compare d (1/2) with
  | lt =>
    -- d < 1/2, so 2*d < 1, so d < 1 - d
    have : d < 1 - d := by sorry
    rw [Rcompare_Lt d (1 - d) this]
  | eq =>
    -- d = 1/2, so 1 - d = 1/2, so compare d (1 - d) = eq
    have heq : d = 1 - d := by sorry--linarith
    rw [Rcompare_Eq d (1 - d) heq]
  | gt =>
    -- d > 1/2, so d > 1 - d
    have : 1 - d < d := by sorry --linarith
    rw [Rcompare_Gt d (1 - d) this]

/--
If `Zfloor x ≠ x`, then
`compare ((Zceil x : ℝ) - x) (1/2) = compare ((Zceil x : ℝ) - x) (x - (Zfloor x : ℝ))`.
-/
theorem Rcompare_ceil_floor_middle (x : ℝ) (h : (Zfloor x : ℝ) ≠ x) :
  compare ((Zceil x : ℝ) - x) (1/2) = compare ((Zceil x : ℝ) - x) (x - (Zfloor x : ℝ)) := by
  -- Use Zceil_floor_neq to rewrite Zceil x
  have hZceil : (Zceil x : ℝ) = (Zfloor x : ℝ) + 1 := by
    -- This is true by Zceil_floor_neq
    sorry
  rw [hZceil]
  -- Let d := (Zfloor x : ℝ) + 1 - x
  let d := (Zfloor x : ℝ) + 1 - x
  -- x - (Zfloor x : ℝ) = 1 - d
  have h_sub : x - (Zfloor x : ℝ) = 1 - d := by ring
  rw [h_sub]
  -- Now, compare d (1/2) = compare d (1 - d)
  cases compare d (1/2) with
  | lt =>
    -- d < 1/2 → d < 1 - d
    have : d < 1 - d := by sorry--linarith
    rw [Rcompare_Lt d (1 - d) this]
  | eq =>
    -- d = 1/2 → 1 - d = 1/2
    have : d = 1 - d := by sorry--linarith
    rw [Rcompare_Eq d (1 - d) this]
  | gt =>
    -- d > 1/2 → 1 - d < d
    have : 1 - d < d := by sorry--linarith
    rw [Rcompare_Gt d (1 - d) this]

/--
For integers `x` and nonzero `y`, the floor of `x / y` as a real is the integer quotient.
-/
theorem Zfloor_div (x y : ℤ) (hy : y ≠ 0) : Zfloor ((x : ℝ) / (y : ℝ)) = x / y := by sorry
  -- -- Use division with remainder: x = (x / y) * y + (x % y)
  -- have hdiv : x = (x / y) * y + (x % y) := sorry--Int.ediv_add_emod x y
  -- -- (x : ℝ) / (y : ℝ) = (x / y : ℝ) + (x % y : ℝ) / (y : ℝ)
  -- have hyR : (y : ℝ) ≠ 0 := by exact_mod_cast hy
  -- have : ((x : ℝ) / (y : ℝ)) = (x / y : ℝ) + (x % y : ℝ) / (y : ℝ) := by sorry
  --   --rw [← Int.cast_add, ← Int.cast_mul, hdiv, add_div, mul_div_cancel_left _ hyR]
  -- rw [this]
  -- -- Now, show that (x / y : ℝ) ≤ (x / y : ℝ) + (x % y : ℝ) / (y : ℝ) < (x / y : ℝ) + 1
  -- apply Zfloor_imp
  -- constructor
  -- · -- Lower bound: (x / y : ℝ) ≤ (x / y : ℝ) + (x % y : ℝ) / (y : ℝ)
  --   apply le_add_of_nonneg_right
  --   -- 0 ≤ (x % y : ℝ) / (y : ℝ) if y > 0, or (x % y : ℝ) / (y : ℝ) ≤ 0 if y < 0
  --   cases lt_or_gt_of_ne hy with hlt hgt
  --   · -- y < 0
  --     have hy_neg : (y : ℝ) < 0 := by exact_mod_cast hlt
  --     have hmod_le_0 : (x % y : ℝ) ≤ 0 := by
  --       have := Int.emod_lt x y hlt
  --       rw [Int.emod_def] at this
  --       -- emod always has same sign as y, so ≤ 0
  --       exact_mod_cast Int.emod_nonpos x y hlt
  --     have hdiv_nonneg : (x % y : ℝ) / (y : ℝ) ≥ 0 := by
  --       rw [div_nonneg_iff]
  --       left; constructor
  --       · exact hmod_le_0
  --       · exact le_of_lt hy_neg
  --     exact hdiv_nonneg
  --   · -- y > 0
  --     have hy_pos : (0 : ℤ) < y := hgt
  --     have hmod_ge_0 : 0 ≤ (x % y : ℝ) := by
  --       have := Int.emod_nonneg x y hy_pos
  --       exact_mod_cast this
  --     have hyR_pos : (0 : ℝ) < (y : ℝ) := by exact_mod_cast hy_pos
  --     have hdiv_nonneg : 0 ≤ (x % y : ℝ) / (y : ℝ) := by
  --       apply div_nonneg hmod_ge_0 (le_of_lt hyR_pos)
  --     exact hdiv_nonneg
  -- · -- Upper bound: (x / y : ℝ) + (x % y : ℝ) / (y : ℝ) < (x / y : ℝ) + 1
  --   -- So, (x % y : ℝ) / (y : ℝ) < 1
  --   cases lt_or_gt_of_ne hy with hlt hgt
  --   · -- y < 0
  --     have hy_neg : (y : ℝ) < 0 := by exact_mod_cast hlt
  --     have hmod_gt_y : (y : ℝ) < (x % y : ℝ) := by
  --       have := Int.emod_lt x y hlt
  --       exact_mod_cast this
  --     have hdiv_lt_1 : (x % y : ℝ) / (y : ℝ) < 1 := by
  --       -- (x % y) < 0, y < 0, so (x % y) / y > 1? Actually, (x % y) ∈ (y, 0], so (x % y) / y ∈ [0,1)
  --       -- But since y < 0, (x % y) ≤ 0, (x % y) > y
  --       -- So (x % y) / y > 1? Actually, (x % y) / y > 1 if (x % y) < y, but (x % y) > y
  --       -- Let's use that (x % y) > y, so (x % y) / y > 1, but (x % y) ≤ 0, so (x % y) / y ≥ 0
  --       -- But in fact, for y < 0, (x % y) ∈ (y, 0], so (x % y) / y ∈ [0,1)
  --       have hy_neg' : (y : ℝ) < 0 := by exact_mod_cast hlt
  --       have hmod_le_0 : (x % y : ℝ) ≤ 0 := by exact_mod_cast Int.emod_nonpos x y hlt
  --       have hmod_gt_y : (y : ℝ) < (x % y : ℝ) := by exact_mod_cast Int.emod_lt x y hlt
  --       have : (x % y : ℝ) / (y : ℝ) < 1 := by
  --         -- (x % y) < 0, y < 0, so (x % y) / y > 0
  --         -- (x % y) < 0, y < 0, so (x % y) / y > 0
  --         -- But (x % y) > y, so (x % y) / y > 1
  --         -- Actually, since y < 0, (x % y) ∈ (y, 0], so (x % y) / y ∈ [0,1)
  --         -- Let's show (x % y : ℝ) / (y : ℝ) < 1
  --         have h : (x % y : ℝ) < (y : ℝ) * 1 := by
  --           rw [mul_one]
  --           exact hmod_gt_y
  --         rw [div_lt_one hy_neg']
  --         exact h
  --       exact this
  --     exact hdiv_lt_1
  --   · -- y > 0
  --     have hy_pos : (0 : ℤ) < y := hgt
  --     have hmod_lt_y : (x % y : ℝ) < (y : ℝ) := by
  --       have := Int.emod_lt x y hy_pos
  --       exact_mod_cast this
  --     have hyR_pos : (0 : ℝ) < (y : ℝ) := by exact_mod_cast hy_pos
  --     have hdiv_lt_1 : (x % y : ℝ) / (y : ℝ) < 1 := by
  --       rw [div_lt_one hyR_pos]
  --       exact hmod_lt_y
  --     exact hdiv_lt_1

/--
For integers `x` and nonzero `y`, truncating `x / y` toward zero as a real gives the integer quotient.
-/
theorem Ztrunc_div (x y : ℤ) (hy : y ≠ 0) : Ztrunc ((x : ℝ) / (y : ℝ)) = x / y := by
sorry
-- Proof.
--   destruct y; [easy | |]; destruct x; intros _.
--   - rewrite Z.quot_0_l; [| easy]. unfold Rdiv. rewrite Rmult_0_l.
--     rewrite Ztrunc_floor; [| apply Rle_refl]. now rewrite Zfloor_IZR.
--   - rewrite Z.quot_div_nonneg; [| easy | easy]. rewrite <-Zfloor_div; [| easy].
--     unfold Ztrunc. rewrite Rlt_bool_false; [reflexivity |].
--     apply Rle_mult_inv_pos; [now apply IZR_le | now apply IZR_lt].
--   - rewrite <-Pos2Z.opp_pos. rewrite Z.quot_opp_l; [| easy].
--     rewrite Z.quot_div_nonneg; [| easy | easy]. rewrite <-Zfloor_div; [| easy].
--     rewrite Ropp_Ropp_IZR. rewrite Ropp_div. unfold Ztrunc. rewrite Rlt_bool_true.
--     + unfold Zceil. now rewrite Ropp_involutive.
--     + apply Ropp_lt_gt_0_contravar. apply Rdiv_lt_0_compat; now apply IZR_lt.
--   - rewrite Z.quot_0_l; [| easy]. unfold Rdiv. rewrite Rmult_0_l.
--     rewrite Ztrunc_floor; [| apply Rle_refl]. now rewrite Zfloor_IZR.
--   - rewrite <-Pos2Z.opp_pos. rewrite Z.quot_opp_r; [| easy].
--     rewrite Z.quot_div_nonneg; [| easy | easy]. rewrite <-Zfloor_div; [| easy].
--     rewrite Ropp_Ropp_IZR. rewrite Ropp_div_den; [| easy]. unfold Ztrunc.
--     rewrite Rlt_bool_true.
--     + unfold Zceil. now rewrite Ropp_involutive.
--     + apply Ropp_lt_gt_0_contravar. apply Rdiv_lt_0_compat; now apply IZR_lt.
--   - rewrite <-2Pos2Z.opp_pos. rewrite Z.quot_opp_l; [| easy]. rewrite Z.quot_opp_r;
  --  [| easy].
--     rewrite Z.quot_div_nonneg; [| easy | easy]. rewrite <-Zfloor_div; [| easy].
--     rewrite 2Ropp_Ropp_IZR. rewrite Ropp_div. rewrite Ropp_div_den; [| easy].
--     rewrite Z.opp_involutive. rewrite Ropp_involutive.
--     unfold Ztrunc. rewrite Rlt_bool_false; [reflexivity |].
--     apply Rle_mult_inv_pos; [now apply IZR_le | now apply IZR_lt].
-- Qed.

section pow

variable (r : Radix)

theorem radix_pos : (0 : ℝ) < (r.val : ℝ) := by {
  cases' r with v Hr
  simp only [Int.cast_pos]
  linarith}

end pow

-- (** Well-used function called bpow for computing the power function #&beta;#^e *)
-- Definition bpow e :=
--   match e with
--   | Zpos p => IZR (Zpower_pos r p)
--   | Zneg p => Rinv (IZR (Zpower_pos r p))
--   | Z0 => 1%R
--   end.

/-- Well-used function called `bpow` for computing the power function β^e. -/
noncomputable def bpow (r : Radix) (e : ℤ) : ℝ :=
  match e with
  | Int.ofNat n => (r.val : ℝ) ^ n
  | Int.negSucc n => ((r.val : ℝ) ^ (n + 1))⁻¹


/--
For positive `m`, `↑(n ^ m) = (↑n : ℝ) ^ m`.
This matches Coq's `IZR (Zpower_pos n m) = powerRZ (IZR n) (Zpos m)`.
-/
theorem IZR_Zpower_pos (n : ℤ) (m : ℕ) (hm : 0 < m) :
  (↑(n ^ m) : ℝ) = (↑n : ℝ) ^ m := by
  induction m with
  | zero =>
    exfalso; exact Nat.not_lt_zero _ hm
  | succ m ih =>
    cases m with
    | zero => simp
    | succ m' =>
      simp only [pow_succ, Int.cast_mul, ih (Nat.succ_pos _)]
      simp only [Int.cast_pow]

-- Theorem IZR_Zpower_pos :
--   forall n m,
--   IZR (Zpower_pos n m) = powerRZ (IZR n) (Zpos m).
-- Proof.
-- intros.
-- rewrite Zpower_pos_nat.
-- simpl.
-- induction (nat_of_P m).
-- apply refl_equal.
-- unfold Zpower_nat.
-- simpl.
-- rewrite mult_IZR.
-- apply Rmult_eq_compat_l.
-- exact IHn0.
-- Qed.

/--
For all exponents `e`, `bpow r e = (r.val : ℝ) ^ e`.
This matches Coq's `bpow e = powerRZ (IZR r) e`.
-/
theorem bpow_powerRZ (r : Radix) (e : ℤ) : bpow r e = (r.val : ℝ) ^ e := by
  cases e with
  | ofNat n =>
    -- e = n : ℕ
    simp [bpow, Int.ofNat_eq_coe, Int.cast_ofNat]
  | negSucc n =>
    simp only [zpow_negSucc]
    rfl


-- Theorem bpow_powerRZ :
--   forall e,
--   bpow e = powerRZ (IZR r) e.
-- Proof.
-- destruct e ; unfold bpow.
-- reflexivity.
-- now rewrite IZR_Zpower_pos.
-- now rewrite IZR_Zpower_pos.
-- Qed.

-- Theorem  bpow_ge_0 :
--   forall e : Z, (0 <= bpow e)%R.
-- Proof.
-- intros.
-- rewrite bpow_powerRZ.
-- apply powerRZ_le.
-- apply radix_pos.
-- Qed.

theorem bpow_ge_0 (r : Radix) (e : ℤ) : 0 ≤ bpow r e := by
  rw [bpow_powerRZ]
  apply zpow_nonneg
  rw [le_iff_lt_or_eq]
  left
  apply radix_pos

theorem bpow_gt_0 (r : Radix) (e : ℤ) : 0 < bpow r e := by
  rw [bpow_powerRZ]
  apply zpow_pos
  apply radix_pos


-- Theorem bpow_gt_0 :
--   forall e : Z, (0 < bpow e)%R.
-- Proof.
-- intros.
-- rewrite bpow_powerRZ.
-- apply powerRZ_lt.
-- apply radix_pos.
-- Qed.

-- Theorem bpow_plus :
--   forall e1 e2 : Z, (bpow (e1 + e2) = bpow e1 * bpow e2)%R.
-- Proof.
-- intros.
-- repeat rewrite bpow_powerRZ.
-- apply powerRZ_add.
-- apply Rgt_not_eq.
-- apply radix_pos.
-- Qed.

/--
For all exponents `e1` and `e2`, `bpow r (e1 + e2) = bpow r e1 * bpow r e2`.
This matches Coq's `bpow (e1 + e2) = bpow e1 * bpow e2`.
-/
theorem bpow_plus (r : Radix) (e1 e2 : ℤ) :
    bpow r (e1 + e2) = bpow r e1 * bpow r e2 := by
  rw [bpow_powerRZ, bpow_powerRZ, bpow_powerRZ]
  have hr : (r : ℝ) ≠ 0 := by {aesop}
  have := Real.rpow_add_intCast hr e1 e2
  exact zpow_add₀ hr e1 e2

/-- `bpow r 1 = r.val` as a real. -/
theorem bpow_1 (r : Radix) : bpow r 1 = (r.val : ℝ) := by
  simp only [bpow, pow_one]

-- Theorem bpow_1 :
--   bpow 1 = IZR r.
-- Proof.
-- unfold bpow, Zpower_pos. simpl.
-- now rewrite Zmult_1_r.
-- Qed.

/-- For all exponents `e`, `bpow r (e + 1) = (r.val : ℝ) * bpow r e`. -/
theorem bpow_plus_1 (r : Radix) (e : ℤ) : bpow r (e + 1) = (r.val : ℝ) * bpow r e := by
  rw [← bpow_1, ← bpow_plus, add_comm]

-- Theorem bpow_plus_1 :
--   forall e : Z, (bpow (e + 1) = IZR r * bpow e)%R.
-- Proof.
-- intros.
-- rewrite <- bpow_1.
-- rewrite <- bpow_plus.
-- now rewrite Zplus_comm.
-- Qed.

-- Theorem bpow_opp :
--   forall e : Z, (bpow (-e) = /bpow e)%R.
-- Proof.
-- intros [|p|p].
-- apply eq_sym, Rinv_1.
-- now change (-Zpos p)%Z with (Zneg p).
-- change (-Zneg p)%Z with (Zpos p).
-- simpl; rewrite Rinv_involutive; trivial.
-- apply Rgt_not_eq.
-- apply (bpow_gt_0 (Zpos p)).
-- Qed.

/-- For all exponents `e`, `bpow r (-e) = (bpow r e)⁻¹`. -/
theorem bpow_opp (r : Radix) (e : ℤ) : bpow r (-e) = (bpow r e)⁻¹ := by
  rw [bpow_powerRZ, bpow_powerRZ]
  exact zpow_neg _ _

/--
For all natural numbers `e`, `↑(r.val ^ e) = bpow r e`.
This matches Coq's `IZR (Zpower_nat r e) = bpow (Z_of_nat e)`.
-/
theorem IZR_Zpower_nat (r : Radix) (e : ℕ) :
  (↑(r.val ^ e) : ℝ) = bpow r (e : ℤ) := by
  simp [bpow, Int.ofNat_eq_coe, Int.cast_ofNat]

-- Theorem IZR_Zpower_nat :
--   forall e : nat,
--   IZR (Zpower_nat r e) = bpow (Z_of_nat e).
-- Proof.
-- intros [|e].
-- split.
-- rewrite <- nat_of_P_o_P_of_succ_nat_eq_succ.
-- rewrite <- Zpower_pos_nat.
-- now rewrite <- Zpos_eq_Z_of_nat_o_nat_of_P.
-- Qed.

/--
For all nonnegative exponents `e`, `↑(r.val ^ e) = bpow r e`.
This matches Coq's `IZR (Zpower r e) = bpow e` for `e ≥ 0`.
-/
theorem IZR_Zpower (r : Radix) (e : ℤ) (he : 0 ≤ e) :
  (↑(r.val ^ (Int.toNat e)) : ℝ) = bpow r e := by
  rw [bpow.eq_def]
  simp [Int.ofNat_eq_coe, Int.cast_ofNat]
  aesop

-- Theorem IZR_Zpower :
--   forall e : Z,
--   (0 <= e)%Z ->
--   IZR (Zpower r e) = bpow e.
-- Proof.
-- intros [|e|e] H.
-- split.
-- split.
-- now elim H.
-- Qed.

-- Theorem bpow_lt :
--   forall e1 e2 : Z,
--   (e1 < e2)%Z -> (bpow e1 < bpow e2)%R.
-- Proof.
-- intros e1 e2 H.
-- replace e2 with (e1 + (e2 - e1))%Z by ring.
-- rewrite <- (Rmult_1_r (bpow e1)).
-- rewrite bpow_plus.
-- apply Rmult_lt_compat_l.
-- apply bpow_gt_0.
-- assert (0 < e2 - e1)%Z by lia.
-- destruct (e2 - e1)%Z ; try discriminate H0.
-- clear.
-- rewrite <- IZR_Zpower by easy.
-- apply IZR_lt.
-- now apply Zpower_gt_1.
-- Qed.

/--
If `e1 < e2`, then `bpow r e1 < bpow r e2`.
-/
theorem bpow_lt (r : Radix) (e1 e2 : ℤ) (h : e1 < e2) : bpow r e1 < bpow r e2 := by
  -- e2 = e1 + (e2 - e1)
  have : e2 = e1 + (e2 - e1) := by ring
  rw [this, bpow_plus, ← mul_one (bpow r e1)]
  -- bpow r (e2 - e1) > 1 for e2 - e1 > 0 and r.val ≥ 2
  have hdiff_pos : 0 < e2 - e1 := sub_pos.mpr h
  have hr : 2 ≤ r.val := r.prop
  nth_rw 2 [mul_one]
  rw [mul_lt_mul_left]
  · rw [← IZR_Zpower]
    cases'  e2 - e1 with h1 h2
    sorry
    sorry
    sorry
  · exact bpow_gt_0 r e1

/--
If `bpow r e1 < bpow r e2`, then `e1 < e2`.
-/
theorem lt_bpow (r : Radix) (e1 e2 : ℤ) (h : bpow r e1 < bpow r e2) : e1 < e2 := by
  by_contra hle
  -- hle : ¬ (e1 < e2) → e2 ≤ e1
  have hle' : e2 ≤ e1 := not_lt.mp hle
  -- Then bpow r e2 ≤ bpow r e1 by monotonicity
  have hle_bpow : bpow r e2 ≤ bpow r e1 := by
    rw [le_iff_eq_or_lt]
    right
    sorry

  -- Contradicts h : bpow r e1 < bpow r e2
  exact not_le_of_lt h hle_bpow

-- Theorem lt_bpow :
--   forall e1 e2 : Z,
--   (bpow e1 < bpow e2)%R -> (e1 < e2)%Z.
-- Proof.
-- intros e1 e2 H.
-- apply Z.gt_lt.
-- apply Znot_le_gt.
-- intros H'.
-- apply Rlt_not_le with (1 := H).
-- destruct (Zle_lt_or_eq _ _ H').
-- apply Rlt_le.
-- now apply bpow_lt.
-- rewrite H0.
-- apply Rle_refl.
-- Qed.

-- Theorem bpow_le :
--   forall e1 e2 : Z,
--   (e1 <= e2)%Z -> (bpow e1 <= bpow e2)%R.
-- Proof.
-- intros e1 e2 H.
-- apply Rnot_lt_le.
-- intros H'.
-- apply Zle_not_gt with (1 := H).
-- apply Z.lt_gt.
-- now apply lt_bpow.
-- Qed.

-- Theorem le_bpow :
--   forall e1 e2 : Z,
--   (bpow e1 <= bpow e2)%R -> (e1 <= e2)%Z.
-- Proof.
-- intros e1 e2 H.
-- apply Znot_gt_le.
-- intros H'.
-- apply Rle_not_lt with (1 := H).
-- apply bpow_lt.
-- now apply Z.gt_lt.
-- Qed.

-- Theorem bpow_inj :
--   forall e1 e2 : Z,
--   bpow e1 = bpow e2 -> e1 = e2.
-- Proof.
-- intros.
-- apply Zle_antisym.
-- apply le_bpow.
-- now apply Req_le.
-- apply le_bpow.
-- now apply Req_le.
-- Qed.

-- Theorem bpow_exp :
--   forall e : Z,
--   bpow e = exp (IZR e * ln (IZR r)).
-- Proof.
-- (* positive case *)
-- assert (forall e, bpow (Zpos e) = exp (IZR (Zpos e) * ln (IZR r))).
-- intros e.
-- unfold bpow.
-- rewrite Zpower_pos_nat.
-- rewrite <- positive_nat_Z.
-- rewrite <- INR_IZR_INZ.
-- induction (nat_of_P e).
-- rewrite Rmult_0_l.
-- now rewrite exp_0.
-- rewrite Zpower_nat_S.
-- rewrite S_INR.
-- rewrite Rmult_plus_distr_r.
-- rewrite exp_plus.
-- rewrite Rmult_1_l.
-- rewrite exp_ln.
-- rewrite <- IHn.
-- rewrite <- mult_IZR.
-- now rewrite Zmult_comm.
-- apply radix_pos.
-- (* general case *)
-- intros [|e|e].
-- rewrite Rmult_0_l.
-- now rewrite exp_0.
-- apply H.
-- unfold bpow.
-- change (IZR (Zpower_pos r e)) with (bpow (Zpos e)).
-- rewrite H.
-- rewrite <- exp_Ropp.
-- rewrite <- Ropp_mult_distr_l_reverse.
-- now rewrite <- opp_IZR.
-- Qed.

-- Lemma sqrt_bpow :
--   forall e,
--   sqrt (bpow (2 * e)) = bpow e.
-- Proof.
-- intro e.
-- change 2%Z with (1 + 1)%Z; rewrite Z.mul_add_distr_r, Z.mul_1_l, bpow_plus.
-- apply sqrt_square, bpow_ge_0.
-- Qed.

-- Lemma sqrt_bpow_ge :
--   forall e,
--   (bpow (e / 2) <= sqrt (bpow e))%R.
-- Proof.
-- intro e.
-- rewrite <- (sqrt_square (bpow _)); [|now apply bpow_ge_0].
-- apply sqrt_le_1_alt; rewrite <- bpow_plus; apply bpow_le.
-- now replace (_ + _)%Z with (2 * (e / 2))%Z by ring; apply Z_mult_div_ge.
-- Qed.

-- (** Another well-used function for having the magnitude of a real number x to the base #&beta;# *)
-- Record mag_prop x := {
--   mag_val :> Z ;
--   _ : (x <> 0)%R -> (bpow (mag_val - 1)%Z <= Rabs x < bpow mag_val)%R
-- }.

-- Definition mag :
--   forall x : R, mag_prop x.
-- Proof.
-- intros x.
-- set (fact := ln (IZR r)).
-- (* . *)
-- assert (0 < fact)%R.
-- apply exp_lt_inv.
-- rewrite exp_0.
-- unfold fact.
-- rewrite exp_ln.
-- apply IZR_lt.
-- apply radix_gt_1.
-- apply radix_pos.
-- (* . *)
-- exists (Zfloor (ln (Rabs x) / fact) + 1)%Z.
-- intros Hx'.
-- generalize (Rabs_pos_lt _ Hx'). clear Hx'.
-- generalize (Rabs x). clear x.
-- intros x Hx.
-- rewrite 2!bpow_exp.
-- fold fact.
-- pattern x at 2 3 ; replace x with (exp (ln x * / fact * fact)).
-- split.
-- rewrite minus_IZR.
-- apply exp_le.
-- apply Rmult_le_compat_r.
-- now apply Rlt_le.
-- unfold Rminus.
-- rewrite plus_IZR.
-- rewrite Rplus_assoc.
-- rewrite Rplus_opp_r, Rplus_0_r.
-- apply Zfloor_lb.
-- apply exp_increasing.
-- apply Rmult_lt_compat_r.
-- exact H.
-- rewrite plus_IZR.
-- apply Zfloor_ub.
-- rewrite Rmult_assoc.
-- rewrite Rinv_l.
-- rewrite Rmult_1_r.
-- now apply exp_ln.
-- now apply Rgt_not_eq.
-- Qed.

-- Theorem bpow_lt_bpow :
--   forall e1 e2,
--   (bpow (e1 - 1) < bpow e2)%R ->
--   (e1 <= e2)%Z.
-- Proof.
-- intros e1 e2 He.
-- rewrite (Zsucc_pred e1).
-- apply Zlt_le_succ.
-- now apply lt_bpow.
-- Qed.

-- Theorem bpow_unique :
--   forall x e1 e2,
--   (bpow (e1 - 1) <= x < bpow e1)%R ->
--   (bpow (e2 - 1) <= x < bpow e2)%R ->
--   e1 = e2.
-- Proof.
-- intros x e1 e2 (H1a,H1b) (H2a,H2b).
-- apply Zle_antisym ;
--   apply bpow_lt_bpow ;
--   apply Rle_lt_trans with x ;
--   assumption.
-- Qed.

-- Theorem mag_unique :
--   forall (x : R) (e : Z),
--   (bpow (e - 1) <= Rabs x < bpow e)%R ->
--   mag x = e :> Z.
-- Proof.
-- intros x e1 He.
-- destruct (Req_dec x 0) as [Hx|Hx].
-- elim Rle_not_lt with (1 := proj1 He).
-- rewrite Hx, Rabs_R0.
-- apply bpow_gt_0.
-- destruct (mag x) as (e2, Hx2).
-- simpl.
-- apply bpow_unique with (2 := He).
-- now apply Hx2.
-- Qed.

-- Theorem mag_opp :
--   forall x,
--   mag (-x) = mag x :> Z.
-- Proof.
-- intros x.
-- destruct (Req_dec x 0) as [Hx|Hx].
-- now rewrite Hx, Ropp_0.
-- destruct (mag x) as (e, He).
-- simpl.
-- specialize (He Hx).
-- apply mag_unique.
-- now rewrite Rabs_Ropp.
-- Qed.

-- Theorem mag_abs :
--   forall x,
--   mag (Rabs x) = mag x :> Z.
-- Proof.
-- intros x.
-- unfold Rabs.
-- case Rcase_abs ; intros _.
-- apply mag_opp.
-- apply refl_equal.
-- Qed.

-- Theorem mag_unique_pos :
--   forall (x : R) (e : Z),
--   (bpow (e - 1) <= x < bpow e)%R ->
--   mag x = e :> Z.
-- Proof.
-- intros x e1 He1.
-- rewrite <- mag_abs.
-- apply mag_unique.
-- rewrite 2!Rabs_pos_eq.
-- exact He1.
-- apply Rle_trans with (2 := proj1 He1).
-- apply bpow_ge_0.
-- apply Rabs_pos.
-- Qed.

-- Theorem mag_le_abs :
--   forall x y,
--   (x <> 0)%R -> (Rabs x <= Rabs y)%R ->
--   (mag x <= mag y)%Z.
-- Proof.
-- intros x y H0x Hxy.
-- destruct (mag x) as (ex, Hx).
-- destruct (mag y) as (ey, Hy).
-- simpl.
-- apply bpow_lt_bpow.
-- specialize (Hx H0x).
-- apply Rle_lt_trans with (1 := proj1 Hx).
-- apply Rle_lt_trans with (1 := Hxy).
-- apply Hy.
-- intros Hy'.
-- apply Rlt_not_le with (1 := Rabs_pos_lt _ H0x).
-- apply Rle_trans with (1 := Hxy).
-- rewrite Hy', Rabs_R0.
-- apply Rle_refl.
-- Qed.

-- Theorem mag_le :
--   forall x y,
--   (0 < x)%R -> (x <= y)%R ->
--   (mag x <= mag y)%Z.
-- Proof.
-- intros x y H0x Hxy.
-- apply mag_le_abs.
-- now apply Rgt_not_eq.
-- rewrite 2!Rabs_pos_eq.
-- exact Hxy.
-- apply Rle_trans with (2 := Hxy).
-- now apply Rlt_le.
-- now apply Rlt_le.
-- Qed.

-- Lemma lt_mag :
--   forall x y,
--   (0 < y)%R ->
--   (mag x < mag y)%Z -> (x < y)%R.
-- Proof.
-- intros x y Py.
-- case (Rle_or_lt x 0); intros Px.
-- intros H.
-- now apply Rle_lt_trans with 0%R.
-- destruct (mag x) as (ex, Hex).
-- destruct (mag y) as (ey, Hey).
-- simpl.
-- intro H.
-- destruct Hex as (_,Hex); [now apply Rgt_not_eq|].
-- destruct Hey as (Hey,_); [now apply Rgt_not_eq|].
-- rewrite Rabs_right in Hex; [|now apply Rle_ge; apply Rlt_le].
-- rewrite Rabs_right in Hey; [|now apply Rle_ge; apply Rlt_le].
-- apply (Rlt_le_trans _ _ _ Hex).
-- apply Rle_trans with (bpow (ey - 1)); [|exact Hey].
-- now apply bpow_le; lia.
-- Qed.

-- Theorem mag_bpow :
--   forall e, (mag (bpow e) = e + 1 :> Z)%Z.
-- Proof.
-- intros e.
-- apply mag_unique.
-- rewrite Rabs_right.
-- replace (e + 1 - 1)%Z with e by ring.
-- split.
-- apply Rle_refl.
-- apply bpow_lt.
-- apply Zlt_succ.
-- apply Rle_ge.
-- apply bpow_ge_0.
-- Qed.

-- Theorem mag_mult_bpow :
--   forall x e, x <> 0%R ->
--   (mag (x * bpow e) = mag x + e :>Z)%Z.
-- Proof.
-- intros x e Zx.
-- destruct (mag x) as (ex, Ex) ; simpl.
-- specialize (Ex Zx).
-- apply mag_unique.
-- rewrite Rabs_mult.
-- rewrite (Rabs_pos_eq (bpow e)) by apply bpow_ge_0.
-- split.
-- replace (ex + e - 1)%Z with (ex - 1 + e)%Z by ring.
-- rewrite bpow_plus.
-- apply Rmult_le_compat_r.
-- apply bpow_ge_0.
-- apply Ex.
-- rewrite bpow_plus.
-- apply Rmult_lt_compat_r.
-- apply bpow_gt_0.
-- apply Ex.
-- Qed.

-- Theorem mag_le_bpow :
--   forall x e,
--   x <> 0%R ->
--   (Rabs x < bpow e)%R ->
--   (mag x <= e)%Z.
-- Proof.
-- intros x e Zx Hx.
-- destruct (mag x) as (ex, Ex) ; simpl.
-- specialize (Ex Zx).
-- apply bpow_lt_bpow.
-- now apply Rle_lt_trans with (Rabs x).
-- Qed.

-- Theorem mag_gt_bpow :
--   forall x e,
--   (bpow e <= Rabs x)%R ->
--   (e < mag x)%Z.
-- Proof.
-- intros x e Hx.
-- destruct (mag x) as (ex, Ex) ; simpl.
-- apply lt_bpow.
-- apply Rle_lt_trans with (1 := Hx).
-- apply Ex.
-- intros Zx.
-- apply Rle_not_lt with (1 := Hx).
-- rewrite Zx, Rabs_R0.
-- apply bpow_gt_0.
-- Qed.

-- Theorem mag_ge_bpow :
--   forall x e,
--   (bpow (e - 1) <= Rabs x)%R ->
--   (e <= mag x)%Z.
-- Proof.
-- intros x e H.
-- destruct (Rlt_or_le (Rabs x) (bpow e)) as [Hxe|Hxe].
-- - (* Rabs x w bpow e *)
--   assert (mag x = e :> Z) as Hln.
--   now apply mag_unique; split.
--   rewrite Hln.
--   now apply Z.le_refl.
-- - (* bpow e <= Rabs x *)
--   apply Zlt_le_weak.
--   now apply mag_gt_bpow.
-- Qed.

-- Theorem bpow_mag_gt :
--   forall x,
--   (Rabs x < bpow (mag x))%R.
-- Proof.
-- intros x.
-- destruct (Req_dec x 0) as [Zx|Zx].
-- rewrite Zx, Rabs_R0.
-- apply bpow_gt_0.
-- destruct (mag x) as (ex, Ex) ; simpl.
-- now apply Ex.
-- Qed.

-- Theorem bpow_mag_le :
--   forall x, (x <> 0)%R ->
--     (bpow (mag x-1) <= Rabs x)%R.
-- Proof.
-- intros x Hx.
-- destruct (mag x) as (ex, Ex) ; simpl.
-- now apply Ex.
-- Qed.


-- Theorem mag_le_Zpower :
--   forall m e,
--   m <> Z0 ->
--   (Z.abs m < Zpower r e)%Z->
--   (mag (IZR m) <= e)%Z.
-- Proof.
-- intros m e Zm Hm.
-- apply mag_le_bpow.
-- now apply IZR_neq.
-- destruct (Zle_or_lt 0 e).
-- rewrite <- abs_IZR, <- IZR_Zpower with (1 := H).
-- now apply IZR_lt.
-- elim Zm.
-- cut (Z.abs m < 0)%Z.
-- now case m.
-- clear -Hm H.
-- now destruct e.
-- Qed.

-- Theorem mag_gt_Zpower :
--   forall m e,
--   m <> Z0 ->
--   (Zpower r e <= Z.abs m)%Z ->
--   (e < mag (IZR m))%Z.
-- Proof.
-- intros m e Zm Hm.
-- apply mag_gt_bpow.
-- rewrite <- abs_IZR.
-- destruct (Zle_or_lt 0 e).
-- rewrite <- IZR_Zpower with (1 := H).
-- now apply IZR_le.
-- apply Rle_trans with (bpow 0).
-- apply bpow_le.
-- now apply Zlt_le_weak.
-- apply IZR_le.
-- clear -Zm.
-- lia.
-- Qed.

-- Lemma mag_mult :
--   forall x y,
--   (x <> 0)%R -> (y <> 0)%R ->
--   (mag x + mag y - 1 <= mag (x * y) <= mag x + mag y)%Z.
-- Proof.
-- intros x y Hx Hy.
-- destruct (mag x) as (ex, Hx2).
-- destruct (mag y) as (ey, Hy2).
-- simpl.
-- destruct (Hx2 Hx) as (Hx21,Hx22); clear Hx2.
-- destruct (Hy2 Hy) as (Hy21,Hy22); clear Hy2.
-- assert (Hxy : (bpow (ex + ey - 1 - 1) <= Rabs (x * y))%R).
-- { replace (ex + ey -1 -1)%Z with (ex - 1 + (ey - 1))%Z; [|ring].
--   rewrite bpow_plus.
--   rewrite Rabs_mult.
--   now apply Rmult_le_compat; try apply bpow_ge_0. }
-- assert (Hxy2 : (Rabs (x * y) < bpow (ex + ey))%R).
-- { rewrite Rabs_mult.
--   rewrite bpow_plus.
--   apply Rmult_le_0_lt_compat; try assumption.
--   now apply Rle_trans with (bpow (ex - 1)); try apply bpow_ge_0.
--   now apply Rle_trans with (bpow (ey - 1)); try apply bpow_ge_0. }
-- split.
-- - now apply mag_ge_bpow.
-- - apply mag_le_bpow.
--   + now apply Rmult_integral_contrapositive_currified.
--   + assumption.
-- Qed.

-- Lemma mag_plus :
--   forall x y,
--   (0 < y)%R -> (y <= x)%R ->
--   (mag x <= mag (x + y) <= mag x + 1)%Z.
-- Proof.
-- assert (Hr : (2 <= r)%Z).
-- { destruct r as (beta_val,beta_prop).
--   now apply Zle_bool_imp_le. }
-- intros x y Hy Hxy.
-- assert (Hx : (0 < x)%R) by apply (Rlt_le_trans _ _ _ Hy Hxy).
-- destruct (mag x) as (ex,Hex); simpl.
-- destruct Hex as (Hex0,Hex1); [now apply Rgt_not_eq|].
-- assert (Haxy : (Rabs (x + y) < bpow (ex + 1))%R).
-- { rewrite bpow_plus_1.
--   apply Rlt_le_trans with (2 * bpow ex)%R.
--   - rewrite Rabs_pos_eq.
--     apply Rle_lt_trans with (2 * Rabs x)%R.
--     + rewrite Rabs_pos_eq.
--       replace (2 * x)%R with (x + x)%R by ring.
--       now apply Rplus_le_compat_l.
--       now apply Rlt_le.
--     + apply Rmult_lt_compat_l with (2 := Hex1).
--       exact Rlt_0_2.
--     + rewrite <- (Rplus_0_l 0).
--       now apply Rlt_le, Rplus_lt_compat.
--   - apply Rmult_le_compat_r.
--     now apply bpow_ge_0.
--     now apply IZR_le. }
-- assert (Haxy2 : (bpow (ex - 1) <= Rabs (x + y))%R).
-- { apply (Rle_trans _ _ _ Hex0).
--   rewrite Rabs_right; [|now apply Rgt_ge].
--   apply Rabs_ge; right.
--   rewrite <- (Rplus_0_r x) at 1.
--   apply Rplus_le_compat_l.
--   now apply Rlt_le. }
-- split.
-- - now apply mag_ge_bpow.
-- - apply mag_le_bpow.
--   + now apply tech_Rplus; [apply Rlt_le|].
--   + exact Haxy.
-- Qed.

-- Lemma mag_minus :
--   forall x y,
--   (0 < y)%R -> (y < x)%R ->
--   (mag (x - y) <= mag x)%Z.
-- Proof.
-- intros x y Py Hxy.
-- assert (Px : (0 < x)%R) by apply (Rlt_trans _ _ _ Py Hxy).
-- apply mag_le.
-- - now apply Rlt_Rminus.
-- - rewrite <- (Rplus_0_r x) at 2.
--   apply Rplus_le_compat_l.
--   rewrite <- Ropp_0.
--   now apply Ropp_le_contravar; apply Rlt_le.
-- Qed.

-- Lemma mag_minus_lb :
--   forall x y,
--   (0 < x)%R -> (0 < y)%R ->
--   (mag y <= mag x - 2)%Z ->
--   (mag x - 1 <= mag (x - y))%Z.
-- Proof.
-- assert (Hbeta : (2 <= r)%Z).
-- { destruct r as (beta_val,beta_prop).
--   now apply Zle_bool_imp_le. }
-- intros x y Px Py Hln.
-- assert (Oxy : (y < x)%R); [apply lt_mag;[assumption|lia]|].
-- destruct (mag x) as (ex,Hex).
-- destruct (mag y) as (ey,Hey).
-- simpl in Hln |- *.
-- destruct Hex as (Hex,_); [now apply Rgt_not_eq|].
-- destruct Hey as (_,Hey); [now apply Rgt_not_eq|].
-- assert (Hbx : (bpow (ex - 2) + bpow (ex - 2) <= x)%R).
-- { ring_simplify.
--   apply Rle_trans with (bpow (ex - 1)).
--   - replace (ex - 1)%Z with (ex - 2 + 1)%Z by ring.
--     rewrite bpow_plus_1.
--     apply Rmult_le_compat_r; [now apply bpow_ge_0|].
--     now apply IZR_le.
--   - now rewrite Rabs_right in Hex; [|apply Rle_ge; apply Rlt_le]. }
-- assert (Hby : (y < bpow (ex - 2))%R).
-- { apply Rlt_le_trans with (bpow ey).
--   now rewrite Rabs_right in Hey; [|apply Rle_ge; apply Rlt_le].
--   now apply bpow_le. }
-- assert (Hbxy : (bpow (ex - 2) <= x - y)%R).
-- { apply Ropp_lt_contravar in Hby.
--   apply Rlt_le in Hby.
--   replace (bpow (ex - 2))%R with (bpow (ex - 2) + bpow (ex - 2)
--                                                   - bpow (ex - 2))%R by ring.
--   now apply Rplus_le_compat. }
-- apply mag_ge_bpow.
-- replace (ex - 1 - 1)%Z with (ex - 2)%Z by ring.
-- now apply Rabs_ge; right.
-- Qed.

-- Theorem mag_plus_ge :
--   forall x y,
--   (x <> 0)%R ->
--   (mag y <= mag x - 2)%Z ->
--   (mag x - 1 <= mag (x + y))%Z.
-- Proof.
-- intros x y Zx.
-- destruct (Req_dec y 0) as [Zy|Zy].
-- { intros _.
--   rewrite Zy, Rplus_0_r.
--   lia. }
-- rewrite <- (mag_abs x), <- (mag_abs y).
-- intros Hm.
-- assert (H: Rabs x <> Rabs y).
-- { intros H.
--   apply Zlt_not_le with (2 := Hm).
--   rewrite H.
--   lia. }
-- apply mag_minus_lb in Hm ; try now apply Rabs_pos_lt.
-- apply Z.le_trans with (1 := Hm).
-- apply mag_le_abs.
-- now apply Rminus_eq_contra.
-- rewrite <- (Ropp_involutive y).
-- rewrite Rabs_Ropp.
-- apply Rabs_triang_inv2.
-- Qed.

-- Lemma mag_div :
--   forall x y : R,
--   x <> 0%R -> y <> 0%R ->
--   (mag x - mag y <= mag (x / y) <= mag x - mag y + 1)%Z.
-- Proof.
-- intros x y Px Py.
-- destruct (mag x) as (ex,Hex).
-- destruct (mag y) as (ey,Hey).
-- simpl.
-- unfold Rdiv.
-- assert (Heiy : (bpow (- ey) < Rabs (/ y) <= bpow (- ey + 1))%R).
-- { rewrite Rabs_Rinv by easy.
--   split.
--   - rewrite bpow_opp.
--     apply Rinv_lt_contravar.
--     + apply Rmult_lt_0_compat.
--       now apply Rabs_pos_lt.
--       now apply bpow_gt_0.
--     + now apply Hey.
--   - replace (_ + _)%Z with (- (ey - 1))%Z by ring.
--     rewrite bpow_opp.
--     apply Rinv_le; [now apply bpow_gt_0|].
--     now apply Hey. }
-- split.
-- - apply mag_ge_bpow.
--   replace (_ - _)%Z with (ex - 1 - ey)%Z by ring.
--   unfold Zminus at 1; rewrite bpow_plus.
--   rewrite Rabs_mult.
--   apply Rmult_le_compat.
--   + now apply bpow_ge_0.
--   + now apply bpow_ge_0.
--   + now apply Hex.
--   + now apply Rlt_le; apply Heiy.
-- - apply mag_le_bpow.
--   + apply Rmult_integral_contrapositive_currified.
--     exact Px.
--     now apply Rinv_neq_0_compat.
--   + replace (_ + 1)%Z with (ex + (- ey + 1))%Z by ring.
--     rewrite bpow_plus.
--     apply Rlt_le_trans with (bpow ex * Rabs (/ y))%R.
--     * rewrite Rabs_mult.
--       apply Rmult_lt_compat_r.
--       apply Rabs_pos_lt.
--       now apply Rinv_neq_0_compat.
--       now apply Hex.
--     * apply Rmult_le_compat_l; [now apply bpow_ge_0|].
--       apply Heiy.
-- Qed.

-- Lemma mag_sqrt :
--   forall x,
--   (0 < x)%R ->
--   mag (sqrt x) = Z.div2 (mag x + 1) :> Z.
-- Proof.
-- intros x Px.
-- apply mag_unique.
-- destruct mag as [e He].
-- simpl.
-- specialize (He (Rgt_not_eq _ _ Px)).
-- rewrite Rabs_pos_eq in He by now apply Rlt_le.
-- split.
-- - rewrite <- (Rabs_pos_eq (bpow _)) by apply bpow_ge_0.
--   apply Rsqr_le_abs_0.
--   rewrite Rsqr_sqrt by now apply Rlt_le.
--   apply Rle_trans with (2 := proj1 He).
--   unfold Rsqr ; rewrite <- bpow_plus.
--   apply bpow_le.
--   generalize (Zdiv2_odd_eqn (e + 1)).
--   destruct Z.odd ; intros ; lia.
-- - rewrite <- (Rabs_pos_eq (bpow _)) by apply bpow_ge_0.
--   apply Rsqr_lt_abs_0.
--   rewrite Rsqr_sqrt by now apply Rlt_le.
--   apply Rlt_le_trans with (1 := proj2 He).
--   unfold Rsqr ; rewrite <- bpow_plus.
--   apply bpow_le.
--   generalize (Zdiv2_odd_eqn (e + 1)).
--   destruct Z.odd ; intros ; lia.
-- Qed.

-- Lemma mag_1 : mag 1 = 1%Z :> Z.
-- Proof.
-- apply mag_unique_pos; rewrite bpow_1; simpl; split; [now right|apply IZR_lt].
-- assert (H := Zle_bool_imp_le _ _ (radix_prop r)); revert H.
-- now apply Z.lt_le_trans.
-- Qed.

-- End pow.

-- Section Bool.

-- Theorem eqb_sym :
--   forall x y, Bool.eqb x y = Bool.eqb y x.
-- Proof.
-- now intros [|] [|].
-- Qed.

-- Theorem eqb_false :
--   forall x y, x = negb y -> Bool.eqb x y = false.
-- Proof.
-- now intros [|] [|].
-- Qed.

-- Theorem eqb_true :
--   forall x y, x = y -> Bool.eqb x y = true.
-- Proof.
-- now intros [|] [|].
-- Qed.

-- End Bool.

-- Section cond_Ropp.

-- Definition cond_Ropp (b : bool) m := if b then Ropp m else m.

-- Theorem IZR_cond_Zopp :
--   forall b m,
--   IZR (cond_Zopp b m) = cond_Ropp b (IZR m).
-- Proof.
-- intros [|] m.
-- apply opp_IZR.
-- apply refl_equal.
-- Qed.

-- Theorem abs_cond_Ropp :
--   forall b m,
--   Rabs (cond_Ropp b m) = Rabs m.
-- Proof.
-- intros [|] m.
-- apply Rabs_Ropp.
-- apply refl_equal.
-- Qed.

-- Theorem cond_Ropp_Rlt_bool :
--   forall m,
--   cond_Ropp (Rlt_bool m 0) m = Rabs m.
-- Proof.
-- intros m.
-- apply sym_eq.
-- case Rlt_bool_spec ; intros Hm.
-- now apply Rabs_left.
-- now apply Rabs_pos_eq.
-- Qed.

-- Theorem Rlt_bool_cond_Ropp :
--   forall x sx, (0 < x)%R ->
--   Rlt_bool (cond_Ropp sx x) 0 = sx.
-- Proof.
--   intros x sx Hx. destruct sx; simpl.
--   - apply Rlt_bool_true. now apply Ropp_lt_gt_0_contravar.
--   - apply Rlt_bool_false. now left.
-- Qed.

-- Theorem cond_Ropp_involutive :
--   forall b x,
--   cond_Ropp b (cond_Ropp b x) = x.
-- Proof.
-- intros [|] x.
-- apply Ropp_involutive.
-- apply refl_equal.
-- Qed.

-- Theorem cond_Ropp_inj :
--   forall b x y,
--   cond_Ropp b x = cond_Ropp b y -> x = y.
-- Proof.
-- intros b x y H.
-- rewrite <- (cond_Ropp_involutive b x), H.
-- apply cond_Ropp_involutive.
-- Qed.

-- Theorem cond_Ropp_mult_l :
--   forall b x y,
--   cond_Ropp b (x * y) = (cond_Ropp b x * y)%R.
-- Proof.
-- intros [|] x y.
-- apply sym_eq.
-- apply Ropp_mult_distr_l_reverse.
-- apply refl_equal.
-- Qed.

-- Theorem cond_Ropp_mult_r :
--   forall b x y,
--   cond_Ropp b (x * y) = (x * cond_Ropp b y)%R.
-- Proof.
-- intros [|] x y.
-- apply sym_eq.
-- apply Ropp_mult_distr_r_reverse.
-- apply refl_equal.
-- Qed.

-- Theorem cond_Ropp_plus :
--   forall b x y,
--   cond_Ropp b (x + y) = (cond_Ropp b x + cond_Ropp b y)%R.
-- Proof.
-- intros [|] x y.
-- apply Ropp_plus_distr.
-- apply refl_equal.
-- Qed.

-- End cond_Ropp.


-- (** LPO taken from Coquelicot *)

-- Theorem LPO_min :
--   forall P : nat -> Prop, (forall n, P n \/ ~ P n) ->
--   {n : nat | P n /\ forall i, (i < n)%nat -> ~ P i} + {forall n, ~ P n}.
-- Proof.
-- assert (Hi: forall n, (0 < INR n + 1)%R).
--   intros N.
--   rewrite <- S_INR.
--   apply lt_0_INR.
--   apply Nat.lt_0_succ.
-- intros P HP.
-- set (E y := exists n, (P n /\ y = / (INR n + 1))%R \/ (~ P n /\ y = 0)%R).
-- assert (HE: forall n, P n -> E (/ (INR n + 1))%R).
--   intros n Pn.
--   exists n.
--   left.
--   now split.
-- assert (BE: is_upper_bound E 1).
--   intros x [y [[_ ->]|[_ ->]]].
--   rewrite <- Rinv_1 at 2.
--   apply Rinv_le.
--   exact Rlt_0_1.
--   rewrite <- S_INR.
--   apply (le_INR 1), le_n_S, le_0_n.
--   exact Rle_0_1.
-- destruct (completeness E) as [l [ub lub]].
--   now exists 1%R.
--   destruct (HP O) as [H0|H0].
--   exists 1%R.
--   exists O.
--   left.
--   apply (conj H0).
--   rewrite Rplus_0_l.
--   apply sym_eq, Rinv_1.
--   exists 0%R.
--   exists O.
--   right.
--   now split.
-- destruct (Rle_lt_dec l 0) as [Hl|Hl].
--   right.
--   intros n Pn.
--   apply Rle_not_lt with (1 := Hl).
--   apply Rlt_le_trans with (/ (INR n + 1))%R.
--   now apply Rinv_0_lt_compat.
--   apply ub.
--   now apply HE.
-- left.
-- set (N := Z.abs_nat (up (/l) - 2)).
-- exists N.
-- assert (HN: (INR N + 1 = IZR (up (/ l)) - 1)%R).
--   unfold N.
--   rewrite INR_IZR_INZ.
--   rewrite inj_Zabs_nat.
--   replace (IZR (up (/ l)) - 1)%R with (IZR (up (/ l) - 2) + 1)%R.
--   apply (f_equal (fun v => IZR v + 1)%R).
--   apply Z.abs_eq.
--   apply Zle_minus_le_0.
--   apply (Zlt_le_succ 1).
--   apply lt_IZR.
--   apply Rle_lt_trans with (/l)%R.
--   apply Rmult_le_reg_r with (1 := Hl).
--   rewrite Rmult_1_l, Rinv_l by now apply Rgt_not_eq.
--   apply lub.
--   exact BE.
--   apply archimed.
--   rewrite minus_IZR.
--   simpl.
--   ring.
-- assert (H: forall i, (i < N)%nat -> ~ P i).
--   intros i HiN Pi.
--   unfold is_upper_bound in ub.
--   refine (Rle_not_lt _ _ (ub (/ (INR i + 1))%R _) _).
--   now apply HE.
--   rewrite <- (Rinv_involutive l) by now apply Rgt_not_eq.
--   apply Rinv_1_lt_contravar.
--   rewrite <- S_INR.
--   apply (le_INR 1).
--   apply le_n_S.
--   apply le_0_n.
--   apply Rlt_le_trans with (INR N + 1)%R.
--   apply Rplus_lt_compat_r.
--   now apply lt_INR.
--   rewrite HN.
--   apply Rplus_le_reg_r with (-/l + 1)%R.
--   ring_simplify.
--   apply archimed.
-- destruct (HP N) as [PN|PN].
--   now split.
-- exfalso.
-- refine (Rle_not_lt _ _ (lub (/ (INR (S N) + 1))%R _) _).
--   intros x [y [[Py ->]|[_ ->]]].
--   destruct (eq_nat_dec y N) as [HyN|HyN].
--   elim PN.
--   now rewrite <- HyN.
--   apply Rinv_le.
--   apply Hi.
--   apply Rplus_le_compat_r.
--   apply Rnot_lt_le.
--   intros Hy.
--   refine (H _ _ Py).
--   apply INR_lt in Hy.
--   clear -Hy HyN ; lia.
--   now apply Rlt_le, Rinv_0_lt_compat.
-- rewrite S_INR, HN.
-- ring_simplify (IZR (up (/ l)) - 1 + 1)%R.
-- rewrite <- (Rinv_involutive l) at 2 by now apply Rgt_not_eq.
-- apply Rinv_1_lt_contravar.
-- rewrite <- Rinv_1.
-- apply Rinv_le.
-- exact Hl.
-- now apply lub.
-- apply archimed.
-- Qed.

-- Theorem LPO :
--   forall P : nat -> Prop, (forall n, P n \/ ~ P n) ->
--   {n : nat | P n} + {forall n, ~ P n}.
-- Proof.
-- intros P HP.
-- destruct (LPO_min P HP) as [[n [Pn _]]|Pn].
-- left.
-- now exists n.
-- now right.
-- Qed.


-- Lemma LPO_Z : forall P : Z -> Prop, (forall n, P n \/ ~P n) ->
--   {n : Z| P n} + {forall n, ~ P n}.
-- Proof.
-- intros P H.
-- destruct (LPO (fun n => P (Z.of_nat n))) as [J|J].
-- intros n; apply H.
-- destruct J as (n, Hn).
-- left; now exists (Z.of_nat n).
-- destruct (LPO (fun n => P (-Z.of_nat n)%Z)) as [K|K].
-- intros n; apply H.
-- destruct K as (n, Hn).
-- left; now exists (-Z.of_nat n)%Z.
-- right; intros n; case (Zle_or_lt 0 n); intros M.
-- rewrite <- (Z.abs_eq n); trivial.
-- rewrite <- Zabs2Nat.id_abs.
-- apply J.
-- rewrite <- (Z.opp_involutive n).
-- rewrite <- (Z.abs_neq n).
-- rewrite <- Zabs2Nat.id_abs.
-- apply K.
-- lia.
-- Qed.



-- (** A little tactic to simplify terms of the form [bpow a * bpow b]. *)
-- Ltac bpow_simplify :=
--   (* bpow ex * bpow ey ~~> bpow (ex + ey) *)
--   repeat
--     match goal with
--       | |- context [(bpow _ _ * bpow _ _)] =>
--         rewrite <- bpow_plus
--       | |- context [(?X1 * bpow _ _ * bpow _ _)] =>
--         rewrite (Rmult_assoc X1); rewrite <- bpow_plus
--       | |- context [(?X1 * (?X2 * bpow _ _) * bpow _ _)] =>
--         rewrite <- (Rmult_assoc X1 X2); rewrite (Rmult_assoc (X1 * X2));
--         rewrite <- bpow_plus
