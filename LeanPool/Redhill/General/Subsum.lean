/-
Copyright (c) 2026 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/

import Mathlib.Algebra.Order.Archimedean.Basic
import LeanPool.Redhill.Common.MaxAbs
import LeanPool.Redhill.General.Defs
import LeanPool.Redhill.ToMathlib.NatAbs

/-!
# Subsum condition for the general case
-/

namespace GeneralCase

open Fin Finset Nat

variable {n : ℕ} {F : Finset ℕ} {h : ℕ}

/-- The embedding for the first subsum block reduction. -/
def redEmb1 : Fin 4 ↪ Fin (n + 6) :=
  ⟨fun i ↦ (i.natAdd 2).natAdd n, fun i j h ↦ by simpa [natAdd_inj 2] using h⟩

variable (n F) in
/-- The sum of `tup n F h`'s first `n + 2` elements, not depending on `h`. -/
def tailK : ℕ := (VW n F).v + (VW n F).w + ∑ i ∈ range n, primeChain (100 * Y F ^ 6) i

lemma sum_redEmb1_compl : ∑ i ∉ univ.map redEmb1, (tup n F h i).natAbs = tailK n F := by
  have cnn (i : Fin n) (j : Fin 6) : castAdd 6 i ≠ natAdd n j := ne_of_lt (by grind)
  have s₁ : univ.map (@castAddEmb n 6) ⊆ (univ.map redEmb1)ᶜ := fun i mi ↦ by
    simp_rw [mem_map, mem_univ, true_and, coe_castAddEmb] at mi
    obtain ⟨j, rfl⟩ := mi
    simp_rw [redEmb1, mem_compl, mem_map, mem_univ, true_and, Function.Embedding.coeFn_mk,
      not_exists]
    grind
  simp_rw [← sum_sdiff s₁, sum_map, castAddEmb_apply, tup_castAdd, Int.natAbs_natCast]
  have s₂ : (univ.map redEmb1)ᶜ \ univ.map (castAddEmb 6) = {natAdd n 0, natAdd n 1} := by
    ext i
    simp_rw [mem_sdiff, mem_compl, mem_map, mem_univ, true_and, castAddEmb_apply, not_exists]
    cases i using addCases with
    | left i => grind [castAdd_inj]
    | right j =>
      simp_rw [cnn, not_false_eq_true, implies_true, and_true, redEmb1, Function.Embedding.coeFn_mk,
        mem_insert, mem_singleton, natAdd_inj]
      decide +revert
  rw [s₂, sum_pair (by grind), tup_natAdd_zero, tup_natAdd_one, Int.natAbs_natCast,
    Int.natAbs_neg, Int.natAbs_natCast, sum_univ_eq_sum_range, tailK]

section Inequalities

lemma tailK_lower_bound : 196 * Y F ^ 6 ≤ tailK n F :=
  calc
    _ = 2 * (98 * Y F * Y F ^ 5) := by ring
    _ ≤ 2 * ((100 * Y F - 2) * Y F ^ 5) := by gcongr; grind [Y_pos]
    _ ≤ _ := by grind [U, tailK, (VW n F).eq_add, (VW n F).m_lt_v]

variable (hh : tailK n F < X F h)

include hh

lemma Y6_le_X : 196 * Y F ^ 6 ≤ X F h :=
  tailK_lower_bound.trans hh.le

lemma b₁_upper_bound : ((X F h ^ 2 + 10 * Y F ^ 3 : ℤ) ^ 2).natAbs ≤ 4 * X F h ^ 4 := by
  norm_cast
  calc
    _ ≤ (X F h ^ 2 + X F h) ^ 2 := by
      gcongr
      apply (Y6_le_X hh).trans'
      gcongr
      · decide
      · exact Y_pos
      · decide
    _ ≤ _ := by
      rw [show 4 * X F h ^ 4 = (X F h ^ 2 + X F h ^ 2) ^ 2 by ring]
      gcongr
      exact le_pow zero_lt_two

lemma b₃_lower_bound : 12 * Y F * X F h ^ 4 ≤ ((X F h - Y F : ℤ) ^ 5).natAbs := by
  rw [Int.natAbs_pow, ← cast_sub (by grind [Y_lt_X]), Int.natAbs_natCast,
    ← Nat.mul_le_mul_left_iff (show 0 < 16 by decide),
    show 16 * (12 * Y F * X F h ^ 4) = 192 * Y F * X F h ^ 4 by ring,
    show 16 * (X F h - Y F) ^ 5 = (X F h - Y F) * (2 * (X F h - Y F)) ^ 4 by ring]
  have : 193 * Y F ≤ X F h := by
    apply (Y6_le_X hh).trans'
    gcongr
    · decide
    · exact le_pow (by decide)
  gcongr <;> lia

lemma b₄_lower_bound : 12 * Y F * X F h ^ 4 ≤ (-(X F h + Y F : ℤ) ^ 5).natAbs := by
  apply (b₃_lower_bound hh).trans
  rw [← cast_sub (by grind [Y_lt_X]), ← cast_add]
  simp_rw [Int.natAbs_neg, Int.natAbs_pow, Int.natAbs_natCast]
  gcongr
  lia

lemma X4_le_natAbs_b4 {b₁ b₂ b₃ b₄ : SignType} (hl : b₄ < b₃) :
    X F h ^ 4 ≤ (b₁ * (X F h ^ 2 + 10 * Y F ^ 3 : ℤ) ^ 2 + b₂ * ((10 * Y F - 1) * X F h ^ 4) +
      b₃ * (X F h - Y F) ^ 5 + b₄ * -(X F h + Y F) ^ 5).natAbs :=
  calc
    _ ≤ (12 * Y F - (4 + (10 * Y F - 1))) * X F h ^ 4 := by
      nth_rw 1 [← one_mul (_ ^ 4)]
      gcongr
      grind [Y_lower_bound]
    _ ≤ (b₃ * (X F h - Y F : ℤ) ^ 5 + b₄ * -(X F h + Y F) ^ 5).natAbs -
        (4 + (10 * Y F - 1)) * X F h ^ 4 := by
      rw [tsub_mul]
      refine Nat.sub_le_sub_right ?_ _
      obtain rfl | rfl | rfl := b₃.trichotomy
      · simp at hl
      · obtain rfl : b₄ = -1 := by decide +revert
        simpa using b₄_lower_bound hh
      · obtain rfl | rfl : b₄ = 0 ∨ b₄ = -1 := by decide +revert
        · simpa using b₃_lower_bound hh
        · simp_rw [SignType.coe_neg, SignType.coe_one, neg_one_mul, neg_neg, one_mul]
          have n₁ : 0 ≤ (X F h - Y F : ℤ) ^ 5 := by
            rw [← cast_sub (by grind [Y_lt_X])]
            exact Int.zero_le_ofNat _
          have n₂ : 0 ≤ (X F h + Y F : ℤ) ^ 5 := by
            rw [← cast_add]
            exact Int.zero_le_ofNat _
          rw [Int.natAbs_add_of_nonneg n₁ n₂]
          grind [b₃_lower_bound hh]
    _ ≤ (b₃ * (X F h - Y F : ℤ) ^ 5 + b₄ * -(X F h + Y F) ^ 5).natAbs -
        (b₁ * (X F h ^ 2 + 10 * Y F ^ 3 : ℤ) ^ 2 + b₂ * ((10 * Y F - 1) * X F h ^ 4)).natAbs := by
      refine Nat.sub_le_sub_left ?_ _
      rw [add_mul]
      refine (Int.natAbs_add_le _ _).trans (Nat.add_le_add ?_ ?_)
      · rw [Int.natAbs_mul, ← one_mul (4 * _)]
        exact mul_le_mul' (by decide +revert) (b₁_upper_bound hh)
      · rw [show (10 * Y F - 1 : ℤ) = (10 * Y F - 1 : ℕ) by grind [Y_pos], ← mul_assoc]
        simp_rw [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast]
        apply Nat.mul_le_mul_right
        cases b₂ <;> simp
    _ ≤ _ := by
      rw [add_assoc (_ + _), add_comm (_ + _)]
      exact Int.sub_le_add_natAbs

omit hh in
lemma b₃_lower_bound_2 :
    5 * X F h ^ 4 ≤
    (-2 * Y F * (5 * X F h ^ 4 + 10 * X F h ^ 2 * Y F ^ 2 + Y F ^ 4 : ℤ)).natAbs := by
  simp_rw [neg_mul, Int.natAbs_neg]
  suffices 5 * X F h ^ 4 ≤ 10 * Y F * X F h ^ 4 by lia
  exact Nat.mul_le_mul_right _ (by grind [Y_pos])

lemma X4_le_natAbs_b3 {b₁ b₂ b₃ : SignType} (hl : b₃ < b₂) :
    X F h ^ 4 ≤ (b₁ * (X F h ^ 2 + 10 * Y F ^ 3 : ℤ) ^ 2 + b₂ * ((10 * Y F - 1) * X F h ^ 4) +
      b₃ * (-2 * Y F * (5 * X F h ^ 4 + 10 * X F h ^ 2 * Y F ^ 2 + Y F ^ 4))).natAbs := by
  calc
    _ = 5 * X F h ^ 4 - 4 * X F h ^ 4 := by
      rw [← tsub_mul, show 5 - 4 = 1 by decide, one_mul]
    _ ≤ 5 * X F h ^ 4 - (b₁ * (X F h ^ 2 + 10 * Y F ^ 3 : ℤ) ^ 2).natAbs := by
      refine Nat.sub_le_sub_left ?_ _
      rw [Int.natAbs_mul, ← one_mul (4 * _)]
      exact mul_le_mul' (by decide +revert) (b₁_upper_bound hh)
    _ ≤ (b₂ * ((10 * Y F - 1 : ℤ) * X F h ^ 4) +
        b₃ * (-2 * Y F * (5 * X F h ^ 4 + 10 * X F h ^ 2 * Y F ^ 2 + Y F ^ 4))).natAbs -
        (b₁ * (X F h ^ 2 + 10 * Y F ^ 3 : ℤ) ^ 2).natAbs := by
      refine Nat.sub_le_sub_right ?_ _
      obtain rfl | rfl | rfl := b₂.trichotomy
      · simp at hl
      · obtain rfl : b₃ = -1 := by decide +revert
        simpa using b₃_lower_bound_2
      · have cY : (10 * Y F - 1 : ℤ) = (10 * Y F - 1 : ℕ) := by grind [Y_pos]
        rw [SignType.coe_one, one_mul, cY]
        obtain rfl | rfl : b₃ = 0 ∨ b₃ = -1 := by decide +revert
        · rw [SignType.coe_zero, zero_mul, add_zero, Int.natAbs_mul]
          simp_rw [Int.natAbs_pow, Int.natAbs_natCast]
          exact Nat.mul_le_mul_right _ (by lia)
        · simp_rw [SignType.coe_neg, SignType.coe_one, neg_one_mul]
          have n₁ : 0 ≤ (10 * Y F - 1 : ℕ) * (X F h ^ 4 : ℤ) := by
            exact_mod_cast Nat.zero_le _
          have n₂ : 0 ≤ -(-2 * Y F * (5 * X F h ^ 4 + 10 * X F h ^ 2 * Y F ^ 2 + Y F ^ 4) : ℤ) := by
            simp_rw [neg_mul, neg_neg]
            exact_mod_cast Nat.zero_le _
          rw [Int.natAbs_add_of_nonneg n₁ n₂]
          grind [b₃_lower_bound_2]
    _ ≤ _ := by
      rw [add_rotate ((b₁ : ℤ) * _)]
      exact Int.sub_le_add_natAbs

lemma X_le_natAbs_redEmb1 {b₁ b₂ b₃ b₄ : SignType} (hb : b₁ ≠ b₂ ∨ b₂ ≠ b₃ ∨ b₃ ≠ b₄) :
    X F h ≤ (b₁ * (X F h ^ 2 + 10 * Y F ^ 3 : ℤ) ^ 2 + b₂ * ((10 * Y F - 1) * X F h ^ 4) +
      b₃ * (X F h - Y F) ^ 5 + b₄ * -(X F h + Y F) ^ 5).natAbs := by
  by_cases hb₃₄ : b₃ ≠ b₄
  · clear hb
    wlog hl : b₄ < b₃ generalizing b₁ b₂ b₃ b₄
    · have negh : -b₄ < -b₃ := by
        rw [SignType.neg_lt_neg_iff]
        exact hb₃₄.lt_or_gt.resolve_right hl
      specialize this (b₁ := -b₁) (b₂ := -b₂) (by simp_all) negh
      simp_rw [SignType.coe_neg, neg_mul, ← neg_add, Int.natAbs_neg] at this
      exact this
    exact (le_pow zero_lt_four).trans (X4_le_natAbs_b4 hh hl)
  rw [← or_assoc] at hb
  replace hb := hb.resolve_right hb₃₄
  rw [not_ne_iff] at hb₃₄
  subst hb₃₄
  rw [add_assoc, ← mul_add, show (X F h - Y F : ℤ) ^ 5 + -(X F h + Y F) ^ 5 =
    -2 * Y F * (5 * X F h ^ 4 + 10 * X F h ^ 2 * Y F ^ 2 + Y F ^ 4) by ring]
  by_cases hb₂₃ : b₂ ≠ b₃
  · clear hb
    wlog hl : b₃ < b₂ generalizing b₁ b₂ b₃
    · have negh : -b₃ < -b₂ := by
        rw [SignType.neg_lt_neg_iff]
        exact hb₂₃.lt_or_gt.resolve_right hl
      specialize this (b₁ := -b₁) (by simp_all) negh
      simp_rw [SignType.coe_neg, neg_mul, ← neg_add, Int.natAbs_neg, ← neg_mul] at this
      exact this
    exact (le_pow zero_lt_four).trans (X4_le_natAbs_b3 hh hl)
  replace hb := hb.resolve_right hb₂₃
  rw [not_ne_iff] at hb₂₃
  subst hb₂₃
  rw [show b₁ * (X F h ^ 2 + 10 * Y F ^ 3 : ℤ) ^ 2 + b₂ * ((10 * Y F - 1) * X F h ^ 4) +
    b₂ * (-2 * Y F * (5 * X F h ^ 4 + 10 * X F h ^ 2 * Y F ^ 2 + Y F ^ 4)) =
    (b₁ - b₂) * (X F h ^ 4 + 20 * X F h ^ 2 * Y F ^ 3) +
    (100 * Y F ^ 6 * b₁ - 2 * Y F ^ 5 * b₂) by ring]
  apply (le_pow zero_lt_four).trans
  calc
    _ ≤ X F h ^ 4 + 20 * X F h ^ 2 * Y F ^ 3 - X F h := by
      suffices 1 * X F h ≤ 20 * X F h * Y F ^ 3 * X F h by lia
      apply Nat.mul_le_mul_right
      exact one_le_mul (one_le_mul (by decide) (by grind [Y_lt_X])) (one_le_pow _ _ Y_pos)
    _ ≤ ((b₁ - b₂ : ℤ) * (X F h ^ 4 + 20 * X F h ^ 2 * Y F ^ 3)).natAbs - X F h := by
      refine Nat.sub_le_sub_right ?_ _
      rw [Int.natAbs_mul, ← one_mul (X F h ^ 4 + _)]
      norm_cast
      apply Nat.mul_le_mul_right
      decide +revert
    _ ≤ ((b₁ - b₂ : ℤ) * (X F h ^ 4 + 20 * X F h ^ 2 * Y F ^ 3)).natAbs -
        (100 * Y F ^ 6 * b₁ - 2 * Y F ^ 5 * b₂ : ℤ).natAbs := by
      refine Nat.sub_le_sub_left ((Y6_le_X hh).trans' ?_) _
      apply (Int.natAbs_sub_le ..).trans
      simp_rw [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast, Int.reduceAbs]
      calc
        _ ≤ 100 * Y F ^ 6 * 1 + 2 * Y F ^ 6 * 1 := by
          gcongr
          · decide +revert
          · exact Y_pos
          · decide
          · decide +revert
        _ ≤ _ := by lia
    _ ≤ _ := Int.sub_le_add_natAbs

end Inequalities

lemma eventually_X_gt (K : Finset ℕ → ℕ) : ∀ᶠ h in Filter.atTop, K F < X F h := by
  rw [Filter.eventually_atTop]
  obtain ⟨n, hn⟩ : ∃ n, K F < (Y F + 1) ^ n := add_one_pow_unbounded_of_pos _ (by grind [Y_pos])
  refine ⟨n, fun h hh ↦ hn.trans_le ?_⟩
  exact Nat.pow_le_pow_right (zero_lt_succ _) (hh.trans (self_le_factorial _))

lemma isSubsumBlock_redEmb1 :
    ∀ᶠ h in Filter.atTop, IsSubsumBlock (tup n F h) (univ.map redEmb1) := by
  filter_upwards [eventually_X_gt (F := F) (tailK n)] with h hh
  refine IsSubsumBlock.of_sum_natAbs_lt redEmb1 fun b ncb ↦ ?_
  conv_rhs => rw [redEmb1, sum_univ_four]
  simp only [Function.Embedding.coeFn_mk, reduceNatAdd, sum_redEmb1_compl,
    tup_natAdd_two, tup_natAdd_three, tup_natAdd_four, tup_natAdd_five]
  apply hh.trans_le
  suffices ∀ {b₁ b₂ b₃ b₄ : SignType}, b₁ ≠ b₂ ∨ b₂ ≠ b₃ ∨ b₃ ≠ b₄ →
      X F h ≤ (b₁ * (X F h ^ 2 + 10 * Y F ^ 3 : ℤ) ^ 2 + b₂ * ((10 * Y F - 1) * X F h ^ 4) +
        b₃ * (X F h - Y F) ^ 5 + b₄ * -(X F h + Y F) ^ 5).natAbs by
    apply this
    contrapose! ncb
    exact ⟨b 0, fun i ↦ by fin_cases i <;> lia⟩
  exact fun hb ↦ X_le_natAbs_redEmb1 hh hb

lemma tupReduce_tup {c₁ : n + 2 = n + 6 - #(univ.map redEmb1)} :
    tupReduce (tup n F h) (univ.map redEmb1) c₁ = vwTup (VW n F) := by
  ext i
  unfold tupReduce
  cases i using lastCases with
  | last =>
    simp_rw [lastCases_last, sum_map, redEmb1, Function.Embedding.coeFn_mk, sum_univ_four]
    simp only [reduceNatAdd, tup_natAdd_two, tup_natAdd_three, tup_natAdd_four, tup_natAdd_five]
    have : last (n + 2) = natAdd n (2 : Fin 3) := by ext; simp
    simp_rw [this, vwTup, addCases_right, cast_mul, cast_pow,
      show (100 * Y F - 2 : ℕ) = (100 * Y F - 2 : ℤ) by grind [Y_pos]]
    ring
  | cast i =>
    have : complRank (univ.map redEmb1) c₁ = castAdd 4 := by
      refine (orderEmbOfFin_unique _ (fun i ↦ ?_) ?_).symm
      · simp_rw [mem_compl, mem_map, mem_univ, true_and, redEmb1, Function.Embedding.coeFn_mk,
          not_exists, natAdd_natAdd, cast_eq_self, ← Fin.val_inj, val_natAdd, val_castAdd]
        omega
      · exact (castAddOrderEmb _).strictMono
    simp_rw [lastCases_castSucc, this, tup, vwTup]
    cases i using addCases with
    | left i => rw [castAdd_castAdd, cast_eq_self, addCases_left, castSucc_castAdd, addCases_left]
    | right i =>
      rw [castAdd_natAdd, cast_eq_self, addCases_right, castSucc_natAdd, addCases_right]
      fin_cases i <;> rfl

theorem strongSSC_tup : ∀ᶠ h in Filter.atTop, StrongSSC (tup n F h) := by
  filter_upwards [isSubsumBlock_redEmb1 (n := n) (F := F)] with h hh
  have c : n + 2 = n + 6 - #(univ.map (redEmb1 (n := n))) := by simp
  apply hh.strongSSC_tupReduce c
  rw [tupReduce_tup]
  refine strongSSC_vwTup ?_ ?_ le_rfl
  · exact mul_pos (by grind [Y_pos]) (pow_pos Y_pos _)
  · rw [pow_succ' _ 5, ← mul_assoc]
    exact Nat.mul_le_mul_right _ (by lia)

lemma maxAbs_tup : ∀ᶠ h in Filter.atTop, maxAbs (tup n F h) = (X F h + Y F) ^ 5 := by
  filter_upwards [eventually_X_gt (F := F) (tailK n)] with h hh
  have na5 : (tup n F h (natAdd n 5)).natAbs = (X F h + Y F) ^ 5 := by
    rw [tup_natAdd_five, Int.natAbs_neg, Int.natAbs_pow]
    lia
  rw [← na5]
  refine maxAbs_eq_of_forall_le fun i ↦ ?_
  rw [na5]
  cases i using addCases with
  | left i =>
    rw [tup_castAdd, Int.natAbs_natCast]
    calc
      _ ≤ ∑ i ∈ range n, primeChain (100 * Y F ^ 6) i := by
        rw [← sum_univ_eq_sum_range]
        exact single_le_sum_of_canonicallyOrdered
          (f := fun i : Fin n ↦ primeChain (100 * Y F ^ 6) i) (mem_univ _)
      _ ≤ X F h + Y F := by grind [tailK]
      _ ≤ _ := le_pow (by decide)
  | right i =>
    fin_cases i <;> simp only [reduceFinMk]
    · rw [tup_natAdd_zero, Int.natAbs_natCast]
      exact (le_pow (by decide)).trans' (by grind [tailK])
    · rw [tup_natAdd_one, Int.natAbs_neg, Int.natAbs_natCast]
      exact (le_pow (by decide)).trans' (by grind [tailK])
    · rw [tup_natAdd_two]
      apply (b₁_upper_bound hh).trans
      rw [pow_succ' _ 4]
      gcongr
      · grind [Y_lower_bound]
      · exact Nat.le_add_right ..
    · rw [tup_natAdd_three, show (10 * Y F - 1 : ℤ) = (10 * Y F - 1 : ℕ) by grind [Y_pos]]
      simp_rw [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast, pow_succ' _ 4]
      gcongr
      · calc
          _ ≤ 196 * Y F := by lia
          _ ≤ 196 * Y F ^ 6 := Nat.mul_le_mul_left _ (le_pow (by decide))
          _ ≤ _ := (Y6_le_X hh).trans (Nat.le_add_right ..)
      · exact Nat.le_add_right ..
    · rw [tup_natAdd_four, Int.natAbs_pow, ← cast_sub (by grind [Y_lt_X]), Int.natAbs_natCast]
      exact Nat.pow_le_pow_left (by lia) _
    · rw [tup_natAdd_five, Int.natAbs_neg]
      norm_cast

end GeneralCase
