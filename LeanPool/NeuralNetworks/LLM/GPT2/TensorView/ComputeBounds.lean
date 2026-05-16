/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import LeanPool.NeuralNetworks.LLM.GPT2.TensorView.Lemmas
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Tactic

open LLM.GPT2

namespace LLM.GPT2

-- Connects the functional definition of computeHelper with its relational counterpart.
lemma computeHelper_eq_ok_iff_rel
    {shape : Array Nat} {rank : Nat} {indices : Array Nat}
    (h_shape_size_eq_rank : shape.size = rank)
    (h_indices_size_eq_rank : indices.size = rank)
    {i fir sa res : Nat} :
    computeHelper shape rank indices i fir sa = Except.ok res ↔
    ComputeHelperRel shape rank indices i fir sa res := by
  constructor
  · -- Forward direction: computeHelper -> rel
    intro h_compute_ok_main
    induction h_fuel : rank - i generalizing i fir sa res with
    | zero =>
      -- Base case: rank - i = 0  => i >= rank
      have h_i_ge_rank : i ≥ rank := Nat.le_of_sub_eq_zero h_fuel
      unfold computeHelper at h_compute_ok_main
      simp only [h_i_ge_rank, if_true] at h_compute_ok_main
      rw [Except.ok.injEq] at h_compute_ok_main; subst res
      exact ComputeHelperRel.tc i fir sa h_i_ge_rank
    | succ current_fuel ih =>
      -- Inductive step: rank - i = current_fuel + 1 => i < rank
      have h_i_lt_rank : i < rank := Nat.lt_of_sub_eq_succ h_fuel
      have h_rank_pos_local : rank > 0 := by -- Renamed to avoid conflict with outer h_rank_pos
        apply Nat.pos_of_ne_zero
        intro h_rank_zero
        rw [h_rank_zero] at h_i_lt_rank
        exact Nat.not_lt_zero i h_i_lt_rank
      let k_val := rank - 1 - i
      have h_pred_lt_rank : rank - 1 < rank := Nat.pred_lt_self h_rank_pos_local
      have hk_val_le_pred : k_val ≤ rank - 1 := Nat.sub_le (rank - 1) i
      have hk_val_lt_rank : k_val < rank := Nat.lt_of_le_of_lt hk_val_le_pred h_pred_lt_rank
      have hk_indices_bounds : k_val < indices.size := h_indices_size_eq_rank ▸ hk_val_lt_rank
      have hk_shape_bounds : k_val < shape.size := h_shape_size_eq_rank ▸ hk_val_lt_rank
      let current_idx_val_safe : Nat := indices[k_val]'hk_indices_bounds
      let current_dim_val_safe : Nat := shape[k_val]'hk_shape_bounds
      have h_get_bang_idx_eq_safe : indices[k_val]! = current_idx_val_safe :=
        Array.getElem_eq_get! hk_indices_bounds
      have h_get_bang_shape_eq_safe : shape[k_val]! = current_dim_val_safe :=
        Array.getElem_eq_get! hk_shape_bounds
      by_cases h_idx_bang_ge_dim_bang : indices[k_val]! ≥ shape[k_val]!
      · -- Case 1: indices[k_val]! ≥ shape[k_val]! (Error case in computeHelper)
        have h_error_branch_is_taken :
            Except.error (TensorError.indexOutOfBounds indices shape) = Except.ok res := by
          simp (config := {zetaDelta := true})
            [computeHelper, h_idx_bang_ge_dim_bang] at h_compute_ok_main
          subst h_shape_size_eq_rank
          simp_all only [gt_iff_lt, tsub_lt_self_iff, Order.lt_one_iff, and_self,
            tsub_le_iff_right, le_add_iff_nonneg_right, zero_le, getElem!_pos, ge_iff_le,
            reduceCtorEq, k_val, current_idx_val_safe, current_dim_val_safe]
          split at h_compute_ok_main
          next h =>
            simp_all only [Nat.sub_eq_zero_of_le, right_eq_add, AddLeftCancelMonoid.add_eq_zero,
              one_ne_zero, and_false]
          next h => simp_all only [not_le, reduceCtorEq]
        cases h_error_branch_is_taken
      · -- Case 2: indices[k_val]! < shape[k_val]! (Recursive call case in computeHelper)
        let next_fir_val := fir + indices[k_val]! * sa
        let next_sa_val := sa * shape[k_val]!
        have h_recursive_call_eq_ok : computeHelper shape rank indices (i + 1) next_fir_val
            next_sa_val = Except.ok res := by
          unfold computeHelper at h_compute_ok_main
          simp [
            if_neg (Nat.not_le_of_lt h_i_lt_rank)] at h_compute_ok_main
          subst h_shape_size_eq_rank
          simp_all only [gt_iff_lt, tsub_lt_self_iff, Order.lt_one_iff, and_self,
            tsub_le_iff_right, le_add_iff_nonneg_right, zero_le, getElem!_pos, ge_iff_le,
            not_le, k_val, current_idx_val_safe, current_dim_val_safe, next_fir_val,
            next_sa_val]
          split at h_compute_ok_main
          next h => simp_all only [reduceCtorEq]
          next h => simp_all only [not_le]
        have h_fuel_for_rec : rank - (i + 1) = current_fuel := by
          rw [Nat.sub_succ, h_fuel]; exact Nat.pred_succ current_fuel
        have h_iff_from_ih :
            (computeHelper shape rank indices (i+1) next_fir_val next_sa_val = Except.ok res) ↔
              (ComputeHelperRel shape rank indices (i+1) next_fir_val next_sa_val res) :=
          (iff_true_right (ih h_recursive_call_eq_ok h_fuel_for_rec)).mpr h_recursive_call_eq_ok
        have h_rec_call_rel :
            ComputeHelperRel shape rank indices (i+1) next_fir_val next_sa_val res :=
          h_iff_from_ih.mp h_recursive_call_eq_ok
        have h_idx_lt_dim_safe : current_idx_val_safe < current_dim_val_safe := by
          rw [←h_get_bang_idx_eq_safe, ←h_get_bang_shape_eq_safe]
          exact Nat.lt_of_not_ge h_idx_bang_ge_dim_bang
        have h_next_fir_eq_safe : next_fir_val = fir + current_idx_val_safe * sa := by
          simp only [h_get_bang_idx_eq_safe, next_fir_val]
        have h_next_sa_eq_safe : next_sa_val = sa * current_dim_val_safe := by
          simp only [h_get_bang_shape_eq_safe, next_sa_val]
        rw [h_next_fir_eq_safe, h_next_sa_eq_safe] at h_rec_call_rel
        apply ComputeHelperRel.rs i fir sa (fir + current_idx_val_safe * sa)
          (sa * current_dim_val_safe) res
        · exact h_i_lt_rank
        · rfl
        · rfl
        · exact h_get_bang_shape_eq_safe
        · exact Nat.lt_of_lt_of_eq h_idx_lt_dim_safe (id (Eq.symm h_get_bang_shape_eq_safe))
        · exact rfl
        · exact id (Eq.symm h_next_sa_eq_safe)
        · exact h_rec_call_rel
  · -- Backward direction: rel -> computeHelper
    intro h_rel
    induction h_rel with
    | tc i fir sa h_term =>
      unfold computeHelper
      simp [h_term]
    | rs i fir sa newFir newSa res h_not_term k_val h_k_def hk_idx_lt_idx_size
        hk_idx_lt_shape_size idx_val h_idx_eq dim_val h_dim_eq h_bound h_newFir_def
        h_newSa_def h_recursive_call ih_rec =>
      unfold computeHelper
      rw [if_neg (Nat.not_le_of_lt h_not_term)]
      simp (config := {zetaDelta := true}) only [
        ←h_k_def,
        Array.getElem_eq_get! hk_idx_lt_idx_size,
        Array.getElem_eq_get! hk_idx_lt_shape_size,
        ←h_idx_eq,
        ←h_dim_eq,
        Nat.not_le_of_lt h_bound,
        if_false,
        ←h_newFir_def,
        ←h_newSa_def
      ]
      exact ih_rec

/--
This theorem proves that the `result` obtained from `computeHelper` (which calculates a flat index
iteratively) is strictly less than the total number of elements in the tensor,
represented by `shape.foldl (· * ·) 1`.

The proof is by induction on `i_rev`, which tracks the number of dimensions
processed from right-to-left (least significant to most significant).

Key hypotheses:
- `h_prev_fir_lt_prev_stride_or_i_rev_zero` (Q): An inductive hypothesis stating that the
  `flatIndexRel` (accumulated from prior, less significant dimensions) is less than the
  `stride` (product of dimension sizes from `shape[rank - i_rev]` to `shape[rank-1]`),
  if `i_rev > 0`. This ensures that the components of `flatIndexRel` were themselves in bounds.
- `h_flatIndexRel_bound_arg_main` (P): An inductive hypothesis stating that `flatIndexRel` is
  bounded by `stride * (product of remaining more significant dimensions not yet processed,
  i.e., shape[0] to shape[rank-i_rev-1])`.
  This essentially states
  `flatIndexRel < total_product_of_unprocessed_dimensions_at_this_stage_of_recursion`.
-/
theorem computeHelper_bounds
    (shape : Array Nat) (rank : Nat) (h_rank_eq_size : rank = shape.size)
    (h_dims_pos_main : ∀ (i : Fin rank),
        shape[i.val]'(by { rw [← h_rank_eq_size]; exact i.isLt }) > 0)
    (indices : Array Nat) (h_indices_size : indices.size = rank)
    (i_rev : Nat) (flatIndexRel : Nat) (stride : Nat)
    (h_fir_eq_zero_if_i_rev_eq_zero : i_rev = 0 → flatIndexRel = 0) -- Hyp for current step
    (h_i_rev_le_rank : i_rev ≤ rank)
    -- Hyp for current step
    (h_stride_def : stride = (shape.extract (rank - i_rev) rank).foldl (· * ·) 1)
    (h_prev_fir_lt_prev_stride_or_i_rev_zero : -- Inductive hypothesis for Q(i_rev)
        if _h : i_rev > 0 then
            flatIndexRel < stride
        else True)
    -- Hyp P(i_rev)
    (h_flatIndexRel_bound_arg_main :
        flatIndexRel < stride * (shape.extract 0 (rank - i_rev)).foldl (· * ·) 1)
    (result : Nat)
    (h_helper_main : computeHelper shape rank indices i_rev flatIndexRel stride =
        Except.ok result)
    : result < shape.foldl (· * ·) 1 := by
  let h_dims_pos_bang := fun (k : Fin rank) => by {
    have hk_lt_size : k.val < shape.size := by { rw [←h_rank_eq_size]; exact k.isLt };
    exact (Array.getElem_eq_get! hk_lt_size).symm ▸ (h_dims_pos_main k)
  }
  have current_fir_lt_current_stride : flatIndexRel < stride := by
    if h_i_rev_is_zero : i_rev = 0 then
      rw [h_fir_eq_zero_if_i_rev_eq_zero h_i_rev_is_zero];
      rw [h_stride_def, h_i_rev_is_zero, Nat.sub_zero, extract_empty_product shape rank];
      exact Nat.zero_lt_one;
    else
      simp only [gt_iff_lt, dite_eq_ite, if_pos (Nat.pos_of_ne_zero h_i_rev_is_zero)]
        at h_prev_fir_lt_prev_stride_or_i_rev_zero
      exact h_prev_fir_lt_prev_stride_or_i_rev_zero
  cases h_i_rev_match:i_rev with
  | zero =>
    have h_flat_is_zero_proof : flatIndexRel = 0 := by
      apply h_fir_eq_zero_if_i_rev_eq_zero; exact h_i_rev_match
    have h_helper_main_zero_i_rev_orig :
        computeHelper shape rank indices 0 flatIndexRel stride = Except.ok result := by
      rw [←h_i_rev_match]; exact h_helper_main
    if h_rank_zero : rank = 0 then
      apply computeHelper_bounds_base_rank_zero shape rank h_rank_eq_size h_rank_zero
        h_dims_pos_bang indices h_indices_size flatIndexRel stride
        (by rw [h_stride_def, h_i_rev_match])
        (by rw [h_i_rev_match] at h_flatIndexRel_bound_arg_main;
            exact h_flatIndexRel_bound_arg_main)
        result h_helper_main_zero_i_rev_orig
    else
      if h_rank_one : rank = 1 then
        apply computeHelper_bounds_base_rank_one_fixed shape rank h_rank_eq_size h_rank_one
          h_dims_pos_bang indices h_indices_size flatIndexRel stride
          (by {rw [h_stride_def, h_i_rev_match, Nat.sub_zero]})
          (by {rw[h_i_rev_match, Nat.sub_zero] at h_flatIndexRel_bound_arg_main;
               exact h_flatIndexRel_bound_arg_main})
          h_flat_is_zero_proof result h_helper_main_zero_i_rev_orig
      else
        have h_stride_is_one_case0 : stride = 1 := by
          rw [h_stride_def, h_i_rev_match, Nat.sub_zero]
          exact extract_empty_product shape rank
        have h_helper_main_zero_i_rev := h_helper_main_zero_i_rev_orig
        unfold computeHelper at h_helper_main_zero_i_rev
        simp only [h_flat_is_zero_proof, h_stride_is_one_case0, ge_iff_le,
          (show ¬(0 ≥ rank) by
            apply Nat.not_le_of_gt
            apply Nat.pos_of_ne_zero h_rank_zero),
          if_false, zero_add,
          Nat.sub_zero] at h_helper_main_zero_i_rev
        let i_for_helper := rank - 1
        let index_val_local := indices[i_for_helper]!
        let dimSize_local := shape[i_for_helper]!
        by_cases h_idx_ge_dim : indices[rank - 1]! ≥ shape[rank - 1]!
        · rw [if_pos h_idx_ge_dim] at h_helper_main_zero_i_rev
          cases h_helper_main_zero_i_rev
        · rw [if_neg h_idx_ge_dim] at h_helper_main_zero_i_rev
          let h_idx_lt_dim : index_val_local < dimSize_local := Nat.lt_of_not_ge h_idx_ge_dim
          let new_flatIndex_rec := index_val_local
          let new_stride_rec := dimSize_local
          apply computeHelper_bounds shape rank h_rank_eq_size h_dims_pos_main indices
            h_indices_size 1 new_flatIndex_rec new_stride_rec
          · intro h_one_eq_zero; cases h_one_eq_zero
          · apply Nat.one_le_iff_ne_zero.mpr h_rank_zero
          · change dimSize_local = (shape.extract (rank - 1) rank).foldl (· * ·) 1
            let h_rank_pos := Nat.pos_of_ne_zero h_rank_zero
            have h_rank_eq_km1_add_1 : rank = (rank - 1) + 1 := by omega
            rw [h_rank_eq_km1_add_1]
            let h_k_lt_size_proof : rank - 1 < shape.size := by
              rw [←h_rank_eq_size]; exact Nat.sub_lt h_rank_pos Nat.one_pos
            let h_kp1_le_size_proof : (rank - 1) + 1 ≤ shape.size := by
              rw [←h_rank_eq_size, Nat.sub_add_cancel h_rank_pos]
            erw [product_extract_single_element_eq_getElem_bang shape (rank - 1)
              h_k_lt_size_proof h_kp1_le_size_proof]
          · exact h_idx_lt_dim
          · ( {
              convert flatIndexRel_bound_for_i_rev_zero_recursive_call shape rank
                (Nat.pos_of_ne_zero h_rank_zero) h_rank_eq_size indices
                flatIndexRel stride
                (by rw [h_i_rev_match, Nat.sub_zero] at h_stride_def; exact h_stride_def)
                (by rw [h_flat_is_zero_proof, h_stride_is_one_case0, Nat.one_mul]
                    apply extract_prefix_product_positive shape rank rank h_rank_eq_size
                      (Nat.le_refl _) h_dims_pos_bang)
                h_dims_pos_bang index_val_local dimSize_local h_idx_lt_dim rfl
                h_flat_is_zero_proof
              · simp [new_flatIndex_rec, h_flat_is_zero_proof, h_stride_is_one_case0]
              · simp [new_stride_rec, h_stride_is_one_case0]
            })
          · dsimp only [new_flatIndex_rec, new_stride_rec, index_val_local, dimSize_local,
              i_for_helper]
            rw [← Nat.one_mul shape[rank - 1]!]
            simp only [Nat.mul_one] at h_helper_main_zero_i_rev
            exact h_helper_main_zero_i_rev
  | succ i_prev =>
    unfold computeHelper at h_helper_main
    split_ifs at h_helper_main with h_cond_ge_rank_from_split
    · rw [Except.ok.injEq] at h_helper_main; subst result
      have h_i_rev_eq_rank : i_rev = rank :=
        Nat.le_antisymm h_i_rev_le_rank h_cond_ge_rank_from_split
      rw [h_i_rev_eq_rank, Nat.sub_self] at h_flatIndexRel_bound_arg_main;
      rw [extract_empty_product shape 0, Nat.mul_one] at h_flatIndexRel_bound_arg_main;
      have h_stride_target_form : stride = shape.foldl (· * ·) 1 := by {
        rw [h_stride_def, h_i_rev_eq_rank, Nat.sub_self];
        exact extract_at_rank_eq_full_product shape rank (Eq.symm h_rank_eq_size);
      }
      rw [←h_stride_target_form];
      exact h_flatIndexRel_bound_arg_main
    · let h_lt_rank_bool := Nat.lt_of_not_ge h_cond_ge_rank_from_split
      let i_for_helper := rank - 1 - i_rev
      let index_val_local := indices[i_for_helper]!
      let dimSize_local := shape[i_for_helper]!
      by_cases h_cond_idx_ge_dim_manual : index_val_local ≥ dimSize_local
      · rw [if_pos h_cond_idx_ge_dim_manual] at h_helper_main; cases h_helper_main
      · rw [if_neg h_cond_idx_ge_dim_manual] at h_helper_main
        let h_idx_lt_dim := Nat.lt_of_not_ge h_cond_idx_ge_dim_manual
        let new_flatIndex_rec := flatIndexRel + index_val_local * stride
        let new_stride_rec := stride * dimSize_local
        have h_stride_pos_proof : stride > 0 := by
          rw [h_stride_def]
          apply extract_sub_array_product_positive shape rank (rank - i_rev) rank
            h_rank_eq_size (Nat.sub_le _ _) (Nat.le_refl _) h_dims_pos_bang
        apply computeHelper_bounds shape rank h_rank_eq_size h_dims_pos_main indices
          h_indices_size (i_rev + 1) new_flatIndex_rec new_stride_rec
        · intro h_succ_eq_zero; cases (Nat.succ_ne_zero i_rev h_succ_eq_zero)
        · exact Nat.succ_le_of_lt h_lt_rank_bool
        · show new_stride_rec = (shape.extract (rank - (i_rev+1)) rank).foldl (· * ·) 1
          unfold new_stride_rec; rw [h_stride_def];
          let k_idx_for_dim := rank - 1 - i_rev
          have h_prod_step_lemma :
              (shape.extract (k_idx_for_dim+1) rank).foldl (·*·) 1 * shape[k_idx_for_dim]! =
                (shape.extract k_idx_for_dim rank).foldl (·*·) 1 := by
            simp_rw [← Array.foldl_toList, ←List.prod_eq_foldl]
            rw [Nat.mul_comm]
            rw [← List.prod_cons]
            congr 1
            rw [← Array.extract_toList_eq_getElem_bang_cons_extract_toList shape k_idx_for_dim
              rank]
            · -- k_idx_for_dim < rank
              rw [show k_idx_for_dim = rank - (1 + i_rev) by rw [← Nat.sub_sub]]
              apply Nat.sub_lt_self
              · exact Nat.pos_of_neZero (1 + i_rev)
              · exact Nat.one_add_le_iff.mpr h_lt_rank_bool
            · -- k_idx_for_dim < shape.size
              rw [h_rank_eq_size]
          rw [show rank - i_rev = k_idx_for_dim + 1 by {simp[k_idx_for_dim]; omega}]
          rw [show rank - (i_rev+1) = k_idx_for_dim by {simp[k_idx_for_dim]; omega}]
          exact h_prod_step_lemma
        · rw [dif_pos (Nat.succ_pos i_rev)]
          unfold new_flatIndex_rec new_stride_rec
          rw [Nat.add_comm flatIndexRel (index_val_local * stride)]
          rw [Nat.mul_comm stride dimSize_local]
          apply flatIndex_step_bound flatIndexRel stride index_val_local dimSize_local
            current_fir_lt_current_stride
            h_idx_lt_dim
            h_stride_pos_proof
            (h_dims_pos_bang ⟨i_for_helper, by {simp[i_for_helper]; omega}⟩)
        · let P_next_prefix := (shape.extract 0 (rank - (i_rev+1))).foldl (·*·) 1
          have h_P_curr_prefix_decomp :
              (shape.extract 0 (rank-i_rev)).foldl (·*·) 1 = dimSize_local * P_next_prefix := by
            let k_dim := rank - 1 - i_rev
            have hk_lt_sh_size : k_dim < shape.size := by {simp[k_dim]; omega}
            rw [show rank - i_rev = k_dim + 1 by {simp[k_dim]; omega}]
            rw [product_extract_prefix_step shape k_dim hk_lt_sh_size]
            rw [mul_comm]
            rw [mul_comm dimSize_local _]
            apply congr_arg₂ (·*·)
            · exact Eq.symm (show P_next_prefix = (shape.extract 0 k_dim).foldl (·*·) 1 by {
                dsimp only [P_next_prefix, k_dim];
                apply congr_arg (fun arr => Array.foldl (·*·) 1 arr);
                apply congr_arg (fun stop_idx => shape.extract 0 stop_idx);
                dsimp only [k_dim];
                omega
              })
            · simp [dimSize_local, i_for_helper, k_dim]
          rw [h_P_curr_prefix_decomp] at h_flatIndexRel_bound_arg_main
          apply Nat.lt_of_lt_of_le
          · -- First subgoal: new_flatIndex_rec < new_stride_rec
            change flatIndexRel + index_val_local * stride < stride * dimSize_local
            rw [Nat.mul_comm stride dimSize_local]
            rw [Nat.add_comm flatIndexRel (index_val_local * stride)]
            apply flatIndex_step_bound flatIndexRel stride index_val_local dimSize_local
              current_fir_lt_current_stride
              h_idx_lt_dim
              h_stride_pos_proof
              -- dimSize_local > 0 (shape[i_for_helper]! > 0)
              (h_dims_pos_bang ⟨i_for_helper, by {unfold i_for_helper; omega}⟩)
          · -- Second subgoal: new_stride_rec ≤ new_stride_rec * P_next_prefix
            have h_a_pos : 0 < new_stride_rec := by
              exact Nat.mul_pos h_stride_pos_proof
                (h_dims_pos_bang ⟨i_for_helper, by {unfold i_for_helper; omega}⟩)
            have h_b_ge_one : 1 ≤ P_next_prefix := by
              suffices h : 0 < P_next_prefix from h
              dsimp only [P_next_prefix]
              let start_idx_local := 0
              let end_idx_local := rank - (i_rev + 1)
              have h_start_le_end_local : start_idx_local ≤ end_idx_local := by
                apply Nat.zero_le
              have h_end_le_rank_local : end_idx_local ≤ rank := Nat.sub_le _ _
              exact extract_sub_array_product_positive shape rank start_idx_local
                end_idx_local h_rank_eq_size h_start_le_end_local h_end_le_rank_local
                h_dims_pos_bang
            exact Nat.le_mul_of_pos_right (stride * dimSize_local) h_b_ge_one
        · exact h_helper_main

/--
Proves that if `computeFlatIndex` successfully computes a `flatIndexVal` for a tensor
defined by `shape` and `rank`, then this `flatIndexVal` is strictly less than the
total number of elements in the tensor. The total number of elements is given by
the product of all dimension sizes in `shape` (i.e., `shape.foldl (· * ·) 1`).

This theorem establishes an upper bound for the `flatIndexVal`, showing it falls
within the valid range of flat indices for the tensor. Since `flatIndexVal` is a `Nat`,
it is implicitly non-negative.
-/
theorem computeFlatIndex_bounds
    (shape : Array Nat) (rank : Nat)
    (h_rank_eq_size : rank = shape.size)
    (h_dims_pos : ∀ (i : Fin rank),
        shape[i.val]'(by { rw [← h_rank_eq_size]; exact i.isLt }) > 0)
    (indices : Array Nat)
    (flatIndexVal : Nat)
    (h_compute_main : computeFlatIndex shape rank h_rank_eq_size h_dims_pos indices =
        Except.ok flatIndexVal)
    : flatIndexVal < shape.foldl (· * ·) 1 := by
  unfold computeFlatIndex at h_compute_main
  have h_indices_size : indices.size = rank := by
    by_cases h : indices.size = rank
    · exact h
    · simp [h] at h_compute_main
  simp only [h_indices_size, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    at h_compute_main
  apply computeHelper_bounds shape rank h_rank_eq_size h_dims_pos indices h_indices_size 0 0 1
  · intro h_zero_eq_zero; rfl
  · exact Nat.zero_le rank
  · rw [Nat.sub_zero]; apply Eq.symm; exact extract_empty_product shape rank
  · simp;
  · simp only [Nat.sub_zero, Nat.one_mul]
    apply extract_prefix_product_positive shape rank rank h_rank_eq_size (Nat.le_refl rank)
      (fun k => by {
        have hk_lt_size : k.val < shape.size := by { rw [←h_rank_eq_size]; exact k.isLt };
        exact (Array.getElem_eq_get! hk_lt_size).symm ▸ (h_dims_pos k)
      })
  · exact h_compute_main

/--
Safely retrieves a `Float` value from the `TensorView` at the specified multi-dimensional `indices`.

This function performs the following steps:
1. Computes the flat (1D) index relative to the tensor view's start using `computeFlatIndex`.
  This step also validates that the rank of `indices` matches `tv.rank`.
2. Proves that the computed `flatIndexRel` is within the bounds of the tensor's `elementCount`
  using the `computeFlatIndex_bounds` lemma.
3. Calculates the absolute byte offset (`byteIndexAbs`) within the underlying storage `ByteArray`.
4. Proves that the read operation (from `byteIndexAbs` for `bytesPerFloat` bytes) is:
   a. Within the memory slice allocated to this `TensorView`
      (`tv.offsetBytes` to `tv.offsetBytes + tv.sizeBytes`).
   b. Within the total `storageSize` of the underlying `ByteArray`, using the provided
      `h_valid` proof.
5. Retrieves the `storage` `ByteArray` from `tv.storageRef`.
6. Reads the `Float` value from the `storage` at `byteIndexAbs` in Little Endian format
   using `LLM.GPT2.ByteArray.readFloatLE?`.

If any step (like index computation or bounds validation) fails, it returns a `TensorError`.
The function operates within the `ST s` monad due to access to `tv.storageRef`.

A panic occurs if `LLM.GPT2.ByteArray.readFloatLE?` returns `none` after all bounds proofs have
passed, as this would indicate an internal inconsistency (e.g., a bug in `readFloatLE?` or an
incorrect proof).
-/
def TensorView.get? {s : Type} (tv : TensorView s) (indices : Array Nat)
    (storageSize : Nat) (h_valid : tv.offsetBytes + tv.sizeBytes <= storageSize)
    : ST s (Except TensorError Float) := do
  -- Compute flat index, getting potential errors
  match h_compute_eq : computeFlatIndex tv.shape tv.rank tv.h_rank_eq_size tv.h_dims_positive
      indices with
  | Except.error e => return Except.error e
  | Except.ok flatIndexRel =>
      -- Prove that the resulting flat index is within bounds
      have h_flat_bounds : flatIndexRel < tv.elementCount :=
        computeFlatIndex_bounds tv.shape tv.rank tv.h_rank_eq_size tv.h_dims_positive indices
          flatIndexRel h_compute_eq
      -- Calculate absolute byte index
      let byteIndexAbs := tv.offsetBytes + flatIndexRel * bytesPerFloat
      -- Prove that the read is within the view's allocated slice
      have h_read_in_view : byteIndexAbs + bytesPerFloat <= tv.offsetBytes + tv.sizeBytes := by
        -- Expands to tv.offsetBytes + flatIndexRel * bytesPerFloat
        dsimp only [byteIndexAbs]
        -- tv.sizeBytes becomes tv.elementCount * bytesPerFloat
        rw [TensorView.sizeBytes]
        -- Group terms: tv.offsetBytes + (flatIndexRel * bytesPerFloat + bytesPerFloat)
        rw [Nat.add_assoc]
        -- Removes tv.offsetBytes from both sides
        simp only [Nat.add_le_add_iff_left]
        rw [← Nat.succ_mul flatIndexRel bytesPerFloat]
        have bytesPerFloat_pos : bytesPerFloat > 0 := by simp [bytesPerFloat]
        exact Nat.mul_le_mul_right bytesPerFloat h_flat_bounds
      -- Prove that the read is within the underlying storage bounds
      have h_read_in_storage : byteIndexAbs + bytesPerFloat <= storageSize := by
        exact Nat.le_trans h_read_in_view h_valid
      -- Perform the read
      let storage ← ST.Ref.get tv.storageRef
      match LLM.GPT2.ByteArray.readFloatLE? storage byteIndexAbs with
      | some val => return Except.ok val
      | none =>
          panic! "Internal error: readFloatLE? failed despite bounds proof"

/--
Sets a `Float` value at the specified `indices` within the `TensorView`.

This function first computes the flat index corresponding to the multi-dimensional `indices`.
If the indices are invalid (e.g., out of bounds, incorrect rank), it returns a `TensorError`.
Otherwise, it calculates the absolute byte offset in the underlying storage and writes the `value`
at that position using little-endian byte order.

The function includes proofs to ensure that the write operation is within the bounds of both
the `TensorView` itself (`h_write_in_view`) and the total `storageSize` (`h_write_in_storage`).
-/
def TensorView.set! {s : Type} (tv : TensorView s) (indices : Array Nat) (value : Float)
    (storageSize : Nat) (h_valid : tv.offsetBytes + tv.sizeBytes <= storageSize)
    : ST s (Except TensorError Unit) := do
  match h_compute_eq : computeFlatIndex tv.shape tv.rank tv.h_rank_eq_size tv.h_dims_positive
      indices with
  | Except.error e => return Except.error e
  | Except.ok flatIndexRel =>
      have h_flat_bounds : flatIndexRel < tv.elementCount :=
        computeFlatIndex_bounds tv.shape tv.rank tv.h_rank_eq_size tv.h_dims_positive indices
          flatIndexRel h_compute_eq
      let byteIndexAbs := tv.offsetBytes + flatIndexRel * bytesPerFloat
      have h_write_in_view : byteIndexAbs + bytesPerFloat <= tv.offsetBytes + tv.sizeBytes := by
        dsimp only [byteIndexAbs]
        rw [TensorView.sizeBytes]
        rw [Nat.add_assoc]
        simp only [Nat.add_le_add_iff_left]
        rw [← Nat.succ_mul flatIndexRel bytesPerFloat]
        have bytesPerFloat_pos : bytesPerFloat > 0 := by simp [bytesPerFloat]
        exact Nat.mul_le_mul_right bytesPerFloat h_flat_bounds
      have h_write_in_storage : byteIndexAbs + bytesPerFloat <= storageSize := by
         exact Nat.le_trans h_write_in_view h_valid
      ST.Ref.modify tv.storageRef (fun storage =>
        LLM.GPT2.ByteArray.writeFloatLE! storage byteIndexAbs value
      )
      return Except.ok ()

end LLM.GPT2
