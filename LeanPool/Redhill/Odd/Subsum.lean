/-
Copyright (c) 2026 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/

import Mathlib.Tactic.Zify
import LeanPool.Redhill.Common.MaxAbs
import LeanPool.Redhill.Odd.Defs
import LeanPool.Redhill.ToMathlib.NatAbs
import LeanPool.Redhill.ToMathlib.NatSumProd

/-!
# Subsum condition for the odd case
-/

namespace OddCase

open Fin Finset

variable {n : ℕ} {F : Finset ℕ} {x : ℤ}

/-- The embedding for the first subsum block reduction. -/
def redEmb1 : Fin 3 ↪ Fin (n + 5) :=
  ⟨fun i ↦ (i.natAdd 2).natAdd n, fun i j h ↦ by simpa [natAdd_inj 2] using h⟩

lemma sum_redEmb1_compl :
    ∑ i ∈ (univ.map redEmb1)ᶜ, (tup n F x i).natAbs =
    (VW n F).v + (VW n F).w + ∑ i ∈ range n, primeChain (max 8 (F.sup id)) i := by
  have cnn (i : Fin n) (j : Fin 5) : castAdd 5 i ≠ natAdd n j := ne_of_lt (by grind)
  have s₁ : univ.map (@castAddEmb n 5) ⊆ (univ.map redEmb1)ᶜ := fun i mi ↦ by
    simp_rw [mem_map, mem_univ, true_and, coe_castAddEmb] at mi
    obtain ⟨j, rfl⟩ := mi
    simp_rw [redEmb1, mem_compl, mem_map, mem_univ, true_and, Function.Embedding.coeFn_mk,
      not_exists]
    grind
  simp_rw [← sum_sdiff s₁, sum_map, castAddEmb_apply, tup_castAdd, Int.natAbs_natCast]
  have s₂ : (univ.map redEmb1)ᶜ \ univ.map (castAddEmb 5) = {natAdd n 0, natAdd n 1} := by
    ext i
    simp_rw [mem_sdiff, mem_compl, mem_map, mem_univ, true_and, castAddEmb_apply, not_exists]
    cases i using addCases with
    | left i => grind [castAdd_inj]
    | right j =>
      simp_rw [cnn, not_false_eq_true, implies_true, and_true, redEmb1, Function.Embedding.coeFn_mk,
        mem_insert, mem_singleton, natAdd_inj]
      decide +revert
  rw [s₂, sum_pair (by grind), tup_natAdd_zero, tup_natAdd_one, Int.natAbs_natCast,
    Int.natAbs_neg, Int.natAbs_natCast, sum_univ_eq_sum_range]

lemma sum_redEmb1_compl_lt : ∑ i ∈ (univ.map redEmb1)ᶜ, (tup n F x i).natAbs < Y n F := by
  rw [sum_redEmb1_compl]
  calc
    _ ≤ (VW n F).v + (VW n F).w + ∏ i ∈ range n, primeChain (max 8 (F.sup id)) i :=
      add_le_add_right (Nat.sum_le_prod (by grind [ten_lt_primeChain])) _
    _ < (VW n F).v * (VW n F).w * ∏ i ∈ range n, primeChain (max 8 (F.sup id)) i := by
      apply Nat.add3_lt_mul3
      · grind [U, U_lt_V]
      · grind [U, U_lt_W]
      · exact one_le_prod (by grind [ten_lt_primeChain])
    _ ≤ _ := by
      unfold Y
      set P := ∏ i ∈ range n, primeChain (max 8 (F.sup id)) i
      calc
        _ = 1 * (P * (VW n F).v * (VW n F).w) := by ring
        _ ≤ 10 * (F.erase 0).prod id * (P * (VW n F).v * (VW n F).w) := by
          gcongr
          suffices 0 < (F.erase 0).prod id by lia
          exact prod_pos (by grind)
        _ = _ := by ring

section Inequalities

lemma b₂_upper_bound (hx : 2 ≤ x.natAbs) : (10 * (x ^ 2 + 1) ^ 2).natAbs ≤ 20 * x.natAbs ^ 4 := by
  wlog nnx : 0 ≤ x
  · rw [← Int.natAbs_neg] at hx
    specialize this hx (by lia)
    rwa [Int.natAbs_neg, neg_sq] at this
  lift x to ℕ using nnx
  rw [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_add_of_nonneg (by positivity) zero_le_one,
    Int.natAbs_natCast, Int.natAbs_pow]
  simp only [Int.reduceAbs, Int.natAbs_natCast,
    show 20 * x ^ 4 = 10 * (x ^ 4 + x ^ 4) by ring,
    show (x ^ 2 + 1) ^ 2 = x ^ 4 + (2 * x ^ 2 + 1) by ring] at hx ⊢
  gcongr
  calc
    _ ≤ x * x ^ 2 + x ^ 3 := by
      gcongr
      exact Nat.one_le_pow _ _ (by lia)
    _ = 2 * x ^ 3 := by ring
    _ ≤ _ := by
      rw [pow_succ' _ 3]
      gcongr

lemma b₁_lower_bound (hx : 26 ≤ x.natAbs) : 21 * x.natAbs ^ 4 ≤ ((x - 1) ^ 5).natAbs := by
  wlog nnx : 0 ≤ x
  · rw [← Int.natAbs_neg] at hx
    specialize this hx (by lia)
    rw [Int.natAbs_neg, show (-x - 1) ^ 5 = -(x + 1) ^ 5 by ring, Int.natAbs_neg] at this
    apply this.trans
    simp_rw [Int.natAbs_pow]
    exact Nat.pow_le_pow_left (by lia) _
  lift x to ℕ using nnx
  rw [Int.natAbs_pow, Int.natAbs_sub_of_nonneg_of_le zero_le_one (by lia)]
  simp only [Int.natAbs_natCast, Int.natAbs_one] at hx ⊢
  zify [show 1 ≤ x by lia]
  rw [show (x - 1 : ℤ) ^ 5 = x ^ 5 + 10 * x ^ 3 + 5 * x - (5 * x ^ 4 + 10 * x ^ 2 + 1) by ring,
    le_sub_iff_add_le, ← add_assoc, ← add_assoc, ← add_mul, pow_succ' _ 4]
  gcongr <;> lia

lemma b₃_lower_bound (hx : 26 ≤ x.natAbs) : 21 * x.natAbs ^ 4 ≤ ((x + 1) ^ 5).natAbs := by
  rw [← Int.natAbs_neg] at hx
  have := b₁_lower_bound hx
  rwa [Int.natAbs_neg, ← neg_add', Odd.neg_pow (by decide), Int.natAbs_neg] at this

lemma natAbs_pow_le_redEmb1 {b₁ b₂ b₃ : SignType} (h : b₃ < b₁) (hx : 26 ≤ x.natAbs) :
    x.natAbs ^ 4 ≤ (b₁ * (x - 1) ^ 5 + b₂ * (10 * (x ^ 2 + 1) ^ 2) + b₃ * -(x + 1) ^ 5).natAbs := by
  rw [← one_mul (x.natAbs ^ 4), show 1 = 21 - 20 by rfl, tsub_mul, add_right_comm]
  refine (tsub_le_tsub ?_ ?_).trans Int.sub_le_add_natAbs
  · obtain rfl | rfl | rfl := b₁.trichotomy
    · simp at h
    · obtain rfl : b₃ = -1 := by decide +revert
      simp [b₃_lower_bound hx, -Int.natAbs_pow]
    · obtain rfl | rfl : b₃ = 0 ∨ b₃ = -1 := by decide +revert
      · simp [b₁_lower_bound hx, -Int.natAbs_pow]
      · simp_rw [SignType.coe_neg, SignType.coe_one, neg_one_mul, neg_neg, one_mul]
        suffices 0 ≤ (x - 1) ^ 5 * (x + 1) ^ 5 by
          rw [Int.natAbs_add_of_mul_nonneg this]
          exact le_add_right (b₁_lower_bound hx)
        rw [← mul_pow, mul_comm, ← mul_self_sub_mul_self, ← sq, ← sq, ← Int.natAbs_sq]
        apply pow_nonneg
        rw [sub_nonneg]
        exact_mod_cast Nat.pow_le_pow_left (by lia) _
  · replace hx : 2 ≤ x.natAbs := by lia
    cases b₂ <;> simp [b₂_upper_bound hx]

lemma natAbs_le_redEmb1_reduced {b₁ b₂ : SignType} (h : b₁ ≠ b₂) (hx : 8 ≤ x.natAbs) :
    x.natAbs ≤ ((b₂ - b₁) * (10 * (x ^ 2 + 1) ^ 2) + b₁ * 8).natAbs := by
  rw [← one_mul x.natAbs, show 1 = 2 - 1 by rfl, tsub_one_mul]
  refine (tsub_le_tsub ?_ ?_).trans Int.sub_le_add_natAbs
  · simp only [Int.natAbs_mul, Int.natAbs_pow, Int.reduceAbs,
      Int.natAbs_add_of_nonneg (sq_nonneg _) zero_le_one]
    have : 1 ≤ (b₂ - b₁ : ℤ).natAbs := by cases b₁ <;> cases b₂ <;> simp_all
    rw [← mul_assoc]
    apply mul_le_mul' (by lia)
    calc
      _ ≤ (x.natAbs ^ 2) ^ 2 := by
        rw [← pow_mul]
        exact Nat.le_self_pow (by simp) _
      _ ≤ _ := by
        gcongr
        lia
  · cases b₁ <;> simp [hx]

lemma Y_le_natAbs_redEmb1 {b₁ b₂ b₃ : SignType} (h : b₁ ≠ b₂ ∨ b₁ ≠ b₃) (hx : Y n F ≤ x.natAbs) :
    Y n F ≤ (b₁ * (x - 1) ^ 5 + b₂ * (10 * (x ^ 2 + 1) ^ 2) + b₃ * -(x + 1) ^ 5).natAbs := by
  by_cases hb₁₃ : b₁ ≠ b₃
  · clear h
    wlog h : b₃ < b₁ generalizing b₁ b₂ b₃
    · have negh : -b₃ < -b₁ := by
        rw [SignType.neg_lt_neg_iff]
        exact hb₁₃.lt_or_gt.resolve_right h
      specialize this (b₂ := -b₂) (by simp_all) negh
      simp_rw [SignType.coe_neg, neg_mul, ← neg_add, Int.natAbs_neg] at this
      exact this
    apply (natAbs_pow_le_redEmb1 h (by grind [Y_lower_bound])).trans'
    exact hx.trans (Nat.le_self_pow four_ne_zero _)
  replace h := h.resolve_right hb₁₃
  rw [not_ne_iff] at hb₁₃
  subst hb₁₃
  rw [show b₁ * (x - 1) ^ 5 + b₂ * (10 * (x ^ 2 + 1) ^ 2) + b₁ * -(x + 1) ^ 5 =
    (b₂ - b₁) * (10 * (x ^ 2 + 1) ^ 2) + b₁ * 8 by ring]
  exact hx.trans (natAbs_le_redEmb1_reduced h (by grind [Y_lower_bound]))

end Inequalities

lemma isSubsumBlock_redEmb1 (hx : Y n F ≤ x.natAbs) :
    IsSubsumBlock (tup n F x) (univ.map redEmb1) := by
  refine IsSubsumBlock.of_sum_natAbs_lt redEmb1 fun b ncb ↦ ?_
  conv_rhs => rw [redEmb1, sum_univ_three]
  simp only [Function.Embedding.coeFn_mk, reduceNatAdd,
    tup_natAdd_two, tup_natAdd_three, tup_natAdd_four]
  apply sum_redEmb1_compl_lt.trans_le
  suffices ∀ {b₁ b₂ b₃ : SignType}, b₁ ≠ b₂ ∨ b₁ ≠ b₃ →
      Y n F ≤ (b₁ * (x - 1) ^ 5 + b₂ * (10 * (x ^ 2 + 1) ^ 2) + b₃ * -(x + 1) ^ 5).natAbs by
    apply this
    contrapose! ncb
    exact ⟨b 0, fun i ↦ by fin_cases i <;> tauto⟩
  exact fun h ↦ Y_le_natAbs_redEmb1 h hx

lemma tupReduce_tup {c₁ : n + 2 = n + 5 - #(univ.map redEmb1)} :
    tupReduce (tup n F x) (univ.map redEmb1) c₁ = vwTup (VW n F) := by
  ext i
  unfold tupReduce
  cases i using lastCases with
  | last =>
    simp_rw [lastCases_last, sum_map, redEmb1, Function.Embedding.coeFn_mk, sum_univ_three]
    simp only [reduceNatAdd, tup_natAdd_two, tup_natAdd_three, tup_natAdd_four]
    have : last (n + 2) = natAdd n (2 : Fin 3) := by ext; simp
    simp_rw [this, vwTup, addCases_right]
    ring
  | cast i =>
    have : complRank (univ.map redEmb1) c₁ = castAdd 3 := by
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

theorem strongSSC_tup (hx : Y n F ≤ x.natAbs) : StrongSSC (tup n F x) := by
  have c : n + 2 = n + 5 - #(univ.map (redEmb1 (n := n))) := by simp
  apply (isSubsumBlock_redEmb1 hx).strongSSC_tupReduce c
  rw [tupReduce_tup]
  exact strongSSC_vwTup (by decide) (le_max_left ..) (le_max_left ..)

/-- When `Y n F ≤ x`, the maximum absolute value is `(x + 1) ^ 5`. -/
lemma maxAbs_tup {x : ℕ} (hx : Y n F ≤ x) : maxAbs (tup n F x) = (x + 1) ^ 5 := by
  have na4 : (tup n F x (natAdd n 4)).natAbs = (x + 1) ^ 5 := by
    rw [tup_natAdd_four, Int.natAbs_neg, Int.natAbs_pow]
    lia
  rw [← na4]
  refine maxAbs_eq_of_forall_le fun i ↦ ?_
  rw [tup_natAdd_four, Int.natAbs_neg]
  have y26 : 26 ≤ Y n F := by grind [Y_lower_bound]
  have xb : Y n F ≤ (x : ℤ).natAbs := by rwa [Int.natAbs_natCast]
  have key₁ : Y n F ≤ ((x + 1 : ℤ) ^ 5).natAbs := by
    refine (xb.trans ?_).trans (b₃_lower_bound (by lia))
    nth_rw 1 [Int.natAbs_natCast, Int.natAbs_natCast, show x = 1 * x ^ 1 by simp]
    gcongr <;> lia
  have key₂ :
      (VW n F).v + (VW n F).w + ∑ i ∈ range n, primeChain (max 8 (F.sup id)) i < Y n F := by
    rw [← sum_redEmb1_compl (x := x)]
    exact sum_redEmb1_compl_lt
  cases i using addCases with
  | left i =>
    rw [tup_castAdd, Int.natAbs_natCast]
    apply (key₂.le.trans key₁).trans'
    calc
      _ ≤ ∑ i ∈ range n, primeChain (max 8 (F.sup id)) i := by
        rw [← sum_univ_eq_sum_range]
        exact single_le_sum_of_canonicallyOrdered
          (f := fun i : Fin n ↦ primeChain (max 8 (F.sup id)) i) (mem_univ _)
      _ ≤ _ := Nat.le_add_left ..
  | right i =>
    fin_cases i <;> simp only [reduceFinMk]
    · rw [tup_natAdd_zero, Int.natAbs_natCast]
      exact (key₂.le.trans key₁).trans' (by lia)
    · rw [tup_natAdd_one, Int.natAbs_neg, Int.natAbs_natCast]
      exact (key₂.le.trans key₁).trans' (by lia)
    · simp_rw [tup_natAdd_two, Int.natAbs_pow]
      exact Nat.pow_le_pow_left (by lia) _
    · rw [tup_natAdd_three]
      refine ((b₂_upper_bound (by lia)).trans ?_).trans (b₃_lower_bound (by lia))
      exact mul_le_mul_left (by decide) _
    · rw [tup_natAdd_four, Int.natAbs_neg]

end OddCase
