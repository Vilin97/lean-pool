/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import LeanPool.NeuralNetworks.LLM.GPT2.TensorView.Defs

open LLM.GPT2

namespace LLM.GPT2

/-- Lemma: The empty product equals 1 -/
lemma extract_empty_product (shape : Array Nat) (i : Nat) :
  (shape.extract i i).foldl (· * ·) 1 = 1 := by
  simp only [Array.extract_empty_of_start_eq_stop, List.size_toArray, List.length_nil,
    List.foldl_toArray', List.foldl_nil]

/-- When extracting the entire array (rank = shape.size), the extract equals the original array -/
lemma extract_eq_self_of_rank_eq_size (shape : Array Nat) :
  shape.extract 0 shape.size = shape := by
  apply Array.ext_getElem?
  intro i
  by_cases h_i : i < shape.size
  · simp [h_i]
  · simp [h_i]

/-- When extracting beyond the array size (rank > shape.size), the extract equals the
original array. -/
lemma extract_eq_self_of_rank_gt_size (shape : Array Nat) (rank : Nat) (h : shape.size ≤ rank) :
  shape.extract 0 rank = shape := by
  apply Array.ext
  · show (shape.extract 0 rank).size = shape.size
    simp only [Array.size_extract, tsub_zero, inf_eq_right]
    exact h
  · intro i h_i_lt
    simp only [Array.getElem_extract]
    have h_sizes_eq : (shape.extract 0 rank).size = shape.size := by
      simp only [Array.size_extract, tsub_zero, inf_eq_right]
      exact h
    have h_i_lt_size : i < shape.size := by rw [← h_sizes_eq]; exact h_i_lt
    have h_i_lt_rank : i < rank := Nat.lt_of_lt_of_le h_i_lt_size h
    simp [h_i_lt_size]

/-- For elements within a prefix extract, the extract's element equals the original array's
element. -/
lemma getElem_bang_extract_prefix (shape : Array Nat) (rank : Nat) (i : Nat)
    (h_i_lt_rank : i < rank) (h_i_lt_size : i < shape.size) :
  (shape.extract 0 rank)[i]! = shape[i]! := by
  have h_extract_get : (shape.extract 0 rank).size > i := by
    simp only [Array.size_extract, tsub_zero]
    exact lt_min h_i_lt_rank h_i_lt_size
  have h_extract_elem : (shape.extract 0 rank)[i]'h_extract_get = shape[i]'h_i_lt_size := by
    simp only [Array.getElem_extract]
    rw [@Array.getElem_eq_iff]
    simp only [zero_add, Array.getElem?_eq_some_getElem_iff]
  rw [@Array.getElem!_eq_getD]
  rw [@Array.getD_eq_getD_getElem?]
  simp_all

/--
Helper Lemma: The list formed by mapping `shape[i]!` over `List.range rank` is equal to
the list representation of `shape.extract 0 rank`.
Requires `rank ≤ shape.size`.
-/
lemma list_map_range_eq_extract_toList (shape : Array Nat) (rank : Nat)
    (h_rank_le_size : rank ≤ shape.size) :
  List.map (fun i => shape[i]!) (List.range rank) = (shape.extract 0 rank).toList := by
  apply List.ext_getElem
  · have h_extract_size : (shape.extract 0 rank).size = rank := by
      simp only [Array.size_extract, Nat.sub_zero, min_eq_left h_rank_le_size]
    rw [List.length_map, List.length_range, Array.length_toList, h_extract_size]
  · intro n h_n_lt_map_len h_n_lt_toList_len
    rw [List.getElem_map, List.getElem_range]
    have h_n_lt_size : n < shape.size := by
      have h_extract_size : (shape.extract 0 rank).size = rank := by
        simp only [Array.size_extract, Nat.sub_zero, min_eq_left h_rank_le_size]
      have h_n_lt_rank : n < rank := by
        rw [← h_extract_size] at h_n_lt_map_len
        exact Nat.lt_of_lt_of_eq h_n_lt_toList_len h_extract_size
      exact Nat.lt_of_lt_of_le h_n_lt_rank h_rank_le_size
    rw [@Array.getElem_toList]
    have h_extract_size_eq_rank : (shape.extract 0 rank).size = rank := by
      simp only [Array.size_extract, Nat.sub_zero, min_eq_left h_rank_le_size]
    have h_n_lt_extract_size : n < (shape.extract 0 rank).size := by
      rw [h_extract_size_eq_rank]; simpa using h_n_lt_map_len
    rw [← Array.getElem_eq_get_safe (arr := shape.extract 0 rank) (i := n) h_n_lt_extract_size]
    have h_n_lt_rank : n < rank := by simpa using h_n_lt_map_len
    have h_n_lt_shape_size : n < shape.size := Nat.lt_of_lt_of_le h_n_lt_rank h_rank_le_size
    exact Eq.symm (getElem_bang_extract_prefix shape rank n h_n_lt_rank h_n_lt_size)

/--
Helper Lemma: The product of elements in `shape.extract 0 rank` is equal to the product of
the list formed by mapping `shape[i]!` over `List.range rank`.
Requires `rank ≤ shape.size`.
-/
lemma product_extract_eq_product_map_range (shape : Array Nat) (rank : Nat)
    (h_rank_le_size : rank ≤ shape.size) :
  (shape.extract 0 rank).foldl (· * ·) 1 =
    (List.map (fun i => shape[i]!) (List.range rank)).prod := by
  rw [← Array.foldl_toList, List.prod_eq_foldl.symm]
  apply congr_arg List.prod
  exact Eq.symm (list_map_range_eq_extract_toList shape rank h_rank_le_size)

/-- Helper Lemma: Given an element x in the suffix (drop rank) of a list derived from an array,
-- find its corresponding index j in the original array and prove its properties. -/
lemma array_elem_properties_from_list_drop_mem (shape : Array Nat) (rank : Nat)
    (h_rank_lt_size : rank < shape.size) (x : Nat) (hx_mem_drop : x ∈ (shape.toList.drop rank)) :
    ∃ j, j ≥ rank ∧ j < shape.size ∧ shape[j]! = x := by
  have ⟨p, hp⟩ := List.get_of_mem hx_mem_drop
  have h_p_lt_drop_len : p.val < (List.drop rank shape.toList).length := p.isLt
  have h_get_drop_p_eq_x : (List.drop rank shape.toList).get p = x := hp
  let j := p.val + rank
  have h_j_ge_rank : j ≥ rank := Nat.le_add_left rank p.val
  have h_j_lt_shape_size : j < shape.size := by
    have h_list_len_eq_shape_size : shape.toList.length = shape.size := Array.length_toList
    have h_rank_le_list_len : rank ≤ shape.toList.length := by
      rw [h_list_len_eq_shape_size]
      exact Nat.le_of_lt h_rank_lt_size
    have h_p_lt_len_minus_rank : p.val < shape.toList.length - rank := by
      rw [← List.length_drop]
      apply h_p_lt_drop_len
    have h_j_lt_list_len : j < shape.toList.length := by
      unfold j
      rw [Nat.add_comm]
      apply Nat.add_lt_of_lt_sub'
      exact h_p_lt_len_minus_rank
    rw [← h_list_len_eq_shape_size]
    exact h_j_lt_list_len
  have h_shape_j_eq_x : shape[j]! = x := by
    rw [← h_get_drop_p_eq_x]
    have h_get_drop_eq_get_orig : (shape.toList.drop rank).get ⟨p, h_p_lt_drop_len⟩ =
        shape.toList.get ⟨j, by rw [Array.length_toList]; exact h_j_lt_shape_size⟩ := by
      simp only [List.get_eq_getElem]
      rw [List.getElem_drop]
      have h_rank_p_eq_j : rank + p.val = j := by
        unfold j
        rw [Nat.add_comm]
      have h_toList_len : shape.toList.length = shape.size := by
        apply Array.length_toList
      have h_idx1_valid : rank + p.val < shape.toList.length := by
        rw [h_toList_len]
        rw [h_rank_p_eq_j]
        exact h_j_lt_shape_size
      have h_idx2_valid : j < shape.toList.length := by
        rw [h_toList_len]
        exact h_j_lt_shape_size
      have h_indices_eq :
          shape.toList[rank + p.val]'h_idx1_valid = shape.toList[j]'h_idx2_valid := by
        congr
      exact h_indices_eq
    rw [h_get_drop_eq_get_orig]
    simp only [Array.length_toList, List.get_eq_getElem, Array.getElem_toList]
    rw [Array.getElem_eq_get_safe h_j_lt_shape_size]
  exact ⟨j, h_j_ge_rank, h_j_lt_shape_size, h_shape_j_eq_x⟩

/--
Helper Lemma: The product of elements in `shape.toList.drop rank` is 1 if all corresponding
elements in the original `shape` array (from index `rank` onwards) are 1.
Requires `rank < shape.size`.
-/
lemma product_list_drop_eq_one_of_trailing_ones [CanonicallyOrderedMul ℕ] (shape : Array Nat)
    (rank : Nat) (h_rank_lt_size : rank < shape.size)
    (h_trailing_ones : ∀ i, rank ≤ i → i < shape.size → shape[i]! = 1) :
  (shape.toList.drop rank).prod = 1 := by
  apply List.prod_eq_one_iff.mpr
  intro x hx_mem_drop
  rcases array_elem_properties_from_list_drop_mem shape rank h_rank_lt_size x hx_mem_drop
    with ⟨j, h_j_ge_rank, h_j_lt_size, h_shape_j_eq_x⟩
  have h_shape_j_eq_one : shape[j]! = 1 := by
    apply h_trailing_ones
    · exact h_j_ge_rank
    · exact h_j_lt_size
  rw [← h_shape_j_eq_x]
  exact h_shape_j_eq_one
/--
Helper Lemma: The product of elements in `shape.toList.take rank` is equal to the product of
the list formed by mapping `shape[i]!` over `List.range rank`.
Requires `rank ≤ shape.size`.
-/
lemma product_list_take_eq_product_map_range (shape : Array Nat) (rank : Nat)
    (h_rank_le_size : rank ≤ shape.size) :
  (shape.toList.take rank).prod = (List.map (fun i => shape[i]!) (List.range rank)).prod := by
  have h_lists_eq : shape.toList.take rank = List.map (fun i => shape[i]!) (List.range rank) := by
    apply List.ext_getElem
    · rw [List.length_map, List.length_range]
      have h_take_length : (shape.toList.take rank).length = min rank shape.toList.length := by
        apply List.length_take
      have h_length_eq : shape.toList.length = shape.size := by apply Array.length_toList
      rw [h_take_length, h_length_eq, min_eq_left h_rank_le_size]
    · intro i h_i_lt_take h_i_lt_map
      have h_i_lt_rank : i < rank := by
        rw [List.length_map, List.length_range] at h_i_lt_map
        exact h_i_lt_map
      have h_i_lt_range_length : i < (List.range rank).length := by
        rw [List.length_range]; exact h_i_lt_rank
      rw [List.getElem_map, List.getElem_range]
      simp only [List.getElem_take, Array.getElem_toList]
      have h_i_lt_shape_size : i < shape.size := by
        apply Nat.lt_of_lt_of_le h_i_lt_rank h_rank_le_size
      have h_i_lt_shape_toList_length : i < shape.toList.length := by
        rw [Array.length_toList]; exact h_i_lt_shape_size
      have h_take_elem_eq : (shape.toList.take rank)[i] = shape.toList[i] := by
        apply List.getElem_take
      have h_list_eq_array : shape.toList[i] = shape[i]! := by
        have h_i_lt_shape_size : i < shape.size := by
          apply Nat.lt_of_lt_of_le h_i_lt_rank h_rank_le_size
        simp only [Array.getElem_toList]
        exact Eq.symm (Array.getElem_eq_get_safe h_i_lt_shape_size)
      rw [← h_list_eq_array]
      rw [← Array.getElem_eq_get_safe h_i_lt_shape_size]
      rw [h_list_eq_array]
  rw [h_lists_eq]

/--
Helper Lemma: The product of all elements in `shape` is equal to the product of the list
formed by mapping `shape[i]!` over `List.range rank`, provided that all elements from
index `rank` onwards are 1.
Requires `rank < shape.size`.
-/
lemma product_full_eq_product_map_range_of_trailing_ones [CanonicallyOrderedMul ℕ]
    (shape : Array Nat) (rank : Nat)
    (h_rank_lt_size : rank < shape.size)
    (h_trailing_ones : ∀ i, rank ≤ i → i < shape.size → shape[i]! = 1) :
  shape.foldl (· * ·) 1 = (List.map (fun i => shape[i]!) (List.range rank)).prod := by
  rw [← Array.foldl_toList]
  rw [← List.prod_eq_foldl (l := shape.toList)]
  have h_rank_le_size_list : rank ≤ shape.toList.length := by
    rw [Array.length_toList]; exact Nat.le_of_lt h_rank_lt_size
  have h_split : shape.toList = shape.toList.take rank ++ shape.toList.drop rank := by
    exact Eq.symm (List.take_append_drop rank shape.toList)
  rw [h_split, List.prod_append]
  rw [product_list_take_eq_product_map_range shape rank (Nat.le_of_lt h_rank_lt_size)]
  rw [product_list_drop_eq_one_of_trailing_ones shape rank h_rank_lt_size h_trailing_ones]
  rw [Nat.mul_one]

/--
Lemma: The product of elements in shape.extract 0 rank equals the product of all elements in shape
when one of these conditions holds:
1. rank = shape.size (extract captures the whole array)
2. rank > shape.size (extract captures the whole array)
3. For each index i where rank ≤ i < shape.size, shape[i]! = 1 (remaining elements are all 1)
-/
lemma extract_prefix_product [CanonicallyOrderedMul ℕ] (shape : Array Nat) (rank : Nat) :
  (∀ i, rank ≤ i → i < shape.size → shape[i]! = 1) →
  (shape.extract 0 rank).foldl (· * ·) 1 = shape.foldl (· * ·) 1 := by
  intro h_trailing_ones
  if h_lt : rank < shape.size then
    have h_rank_le_size : rank ≤ shape.size := Nat.le_of_lt h_lt
    have h_prod_extract : (shape.extract 0 rank).foldl (· * ·) 1 =
        (List.map (fun i => shape[i]!) (List.range rank)).prod :=
      product_extract_eq_product_map_range shape rank h_rank_le_size
    have h_prod_full : shape.foldl (· * ·) 1 =
        (List.map (fun i => shape[i]!) (List.range rank)).prod :=
      product_full_eq_product_map_range_of_trailing_ones shape rank h_lt h_trailing_ones
    rw [h_prod_extract, h_prod_full]
  else if h_eq : rank = shape.size then
    rw [h_eq, extract_eq_self_of_rank_eq_size shape]
  else
    have h_gt : rank > shape.size := by
      apply Nat.gt_of_not_le
      intro h
      have h₁ := Nat.eq_or_lt_of_le h
      cases h₁ with
      | inl h₂ => exact h_eq h₂
      | inr h₃ => exact h_lt h₃
    rw [extract_eq_self_of_rank_gt_size shape rank (Nat.le_of_lt h_gt)]

/-- Specialized lemma: When rank = shape.size, the prefix product equals the full product. -/
lemma extract_at_rank_eq_full_product (shape : Array Nat) (rank : Nat)
    (h_rank_eq_size : shape.size = rank) :
  (shape.extract 0 rank).foldl (· * ·) 1 = shape.foldl (· * ·) 1 := by
  rw [h_rank_eq_size]
  have h_extract_eq : shape.extract 0 shape.size = shape := by
    exact extract_eq_self_of_rank_eq_size shape
  rw [← h_rank_eq_size]
  simp only [Array.extract_size]

/-- Specialized lemma for the actual use case in computeFlatIndex_bounds -/
lemma extract_at_rank_empty (shape : Array Nat) (rank : Nat) (h_rank_eq_size : rank = shape.size) :
  (shape.extract 0 rank).foldl (· * ·) 1 = shape.foldl (· * ·) 1 := by
  have h_extract_eq : shape.extract 0 rank = shape := by
    rw [h_rank_eq_size]
    exact extract_eq_self_of_rank_eq_size shape
  rw [h_extract_eq]

/-- When the start index is greater than or equal to the stop index, list extraction yields
an empty list. -/
lemma _root_.List.extract_of_start_ge_end {α : Type} {l : List α} {start stop : Nat}
    (h : start ≥ stop) :
  List.extract l start stop = [] := by
  unfold List.extract
  cases Nat.le_total start (List.length l) with
  | inl h_le =>
    simp only [List.take_eq_nil_iff, List.drop_eq_nil_iff]
    rw [Nat.sub_eq_zero_of_le h]
    simp only
    simp only [true_or]
  | inr h_gt =>
    simp [h_gt]

lemma _root_.Array.extract_toList_eq_list_extract {α : Type} (arr : Array α) (start stop : Nat) :
  (arr.extract start stop).toList = List.extract arr.toList start (min stop arr.size) := by
  simp only [Array.toList_extract, List.extract_eq_take_drop, List.take_eq_take_iff,
    List.length_drop, Array.length_toList]
  rw [← @Array.extract_eq_extract_right]
  ext i hi₁ hi₂ : 1
  · simp_all only [Array.size_extract, inf_le_right, inf_of_le_left]
  · simp_all only [Array.getElem_extract]

lemma _root_.Array.extract_prefix_toList_eq_take_toList {α : Type} (arr : Array α) (i : Nat)
    (h_i_le_size : i ≤ arr.size) :
  (arr.extract 0 i).toList = arr.toList.take i := by
  rw [Array.extract_toList_eq_list_extract]
  rw [Nat.min_eq_left h_i_le_size]
  rw [@List.extract_eq_take_drop]
  exact rfl

lemma _root_.Array.extract_suffix_toList_eq_drop_toList {α : Type} (arr : Array α) (i : Nat)
    (_ : i ≤ arr.size) :
  (arr.extract i arr.size).toList = arr.toList.drop i := by
  rw [Array.extract_toList_eq_list_extract, Nat.min_self]
  simp [List.extract_eq_take_drop]

/-- Lemma: The product of the first segment and remaining segment equals the total product -/
lemma shape_extract_product_split (shape : Array Nat) (i : Nat) (h_i_le_size : i ≤ shape.size) :
  (shape.extract 0 i).foldl (· * ·) 1 * (shape.extract i shape.size).foldl (· * ·) 1 =
  shape.foldl (· * ·) 1 := by
  rw [← Array.foldl_toList, ← Array.foldl_toList, ← Array.foldl_toList]
  rw [Array.extract_prefix_toList_eq_take_toList shape i h_i_le_size]
  rw [Array.extract_suffix_toList_eq_drop_toList shape i h_i_le_size]
  rw [← List.prod_eq_foldl (l := shape.toList.take i)]
  rw [← List.prod_eq_foldl (l := shape.toList.drop i)]
  rw [List.prod_take_mul_prod_drop (shape.toList) i]
  rw [List.prod_eq_foldl (l := shape.toList)]

lemma _root_.Array.size_extract_of_start_lt_stop_le_size {α : Type} (arr : Array α)
    (start stop : Nat)
    (h_start_lt_stop : start < stop) (h_stop_le_size : stop ≤ arr.size) :
  (arr.extract start stop).size = stop - start := by
  simp only [Array.size_extract]
  have h_not_stop_le_start : ¬(stop ≤ start) := Nat.not_le_of_gt h_start_lt_stop
  simp [min_eq_left h_stop_le_size]

/-- When the start index equals or exceeds the stop index, the extract has size 0. -/
lemma _root_.Array.size_extract_of_stop_le_start {α : Type} (arr : Array α) (start stop : Nat)
    (h : stop ≤ start) : (arr.extract start stop).size = 0 := by
  simp only [Array.size_extract]
  have h_min_le : min stop arr.size ≤ start := by
    apply Nat.le_trans
    · apply min_le_left
    · exact h
  exact Nat.sub_eq_zero_of_le h_min_le

lemma _root_.Array.extract_toList_length_eq_cons_extract_toList_length {α : Type} [Inhabited α]
    (arr : Array α) (idx : Nat) (stop : Nat)
    (h_idx_lt_stop : idx < stop) (h_stop_le_arr_size : stop ≤ arr.size) :
  (arr.extract idx stop).toList.length =
    (arr[idx]! :: (arr.extract (idx + 1) stop).toList).length := by
  simp only [Array.length_toList, List.length_cons]
  rw [Array.size_extract_of_start_lt_stop_le_size arr idx stop h_idx_lt_stop h_stop_le_arr_size]
  have h_idx_plus_1_le_stop : idx + 1 ≤ stop := Nat.succ_le_of_lt h_idx_lt_stop
  by_cases h_idx_plus_1_eq_stop : idx + 1 = stop
  · rw [h_idx_plus_1_eq_stop]
    simp only [Array.size_extract_of_stop_le_start arr stop stop (Nat.le_refl stop)]
    rw [← h_idx_plus_1_eq_stop]
    simp
  · have h_idx_plus_1_lt_stop' : idx + 1 < stop :=
      Nat.lt_of_le_of_ne h_idx_plus_1_le_stop h_idx_plus_1_eq_stop
    rw [Array.size_extract_of_start_lt_stop_le_size arr (idx + 1) stop h_idx_plus_1_lt_stop'
      h_stop_le_arr_size]
    rw [Nat.sub_succ' stop idx]
    rw [Nat.add_comm]
    apply Eq.symm
    refine Nat.add_sub_of_le ?_
    exact Nat.le_sub_of_add_le' h_idx_lt_stop

/-- Base case: The first element of an array extract equals the source array element. -/
lemma _root_.Array.extract_toList_getElem_zero {α : Type} [Inhabited α]
    (arr : Array α) (idx : Nat) (stop : Nat)
    (h_idx_lt_stop : idx < stop) (h_stop_le_arr_size : stop ≤ arr.size)
    (h_0_lt_len : 0 < (arr.extract idx stop).toList.length) :
  (arr.extract idx stop).toList.get ⟨0, h_0_lt_len⟩ = arr[idx]! := by
  have h_0_lt_size : 0 < (arr.extract idx stop).size := by
    rwa [Array.length_toList] at h_0_lt_len
  rw [List.get_eq_getElem, Array.getElem_toList]
  have h_extract_getElem : (arr.extract idx stop)[0] = arr[idx + 0] := by
    apply Array.getElem_extract
  rw [h_extract_getElem]
  simp only [add_zero]
  rw [← @Array.getElem_eq_get_safe]

/-- For an array extract, the jth element in the list view equals the corresponding array element.
    Requires explicit bounds to simplify the proof. -/
lemma _root_.Array.extract_toList_getElem {α : Type} [Inhabited α]
    (arr : Array α) (idx : Nat) (stop : Nat)
    (j : Nat) (h_j_lt_len : j < (arr.extract idx stop).toList.length)
    (h_idx_lt_stop : idx < stop) (h_stop_le_size : stop ≤ arr.size) :
  (arr.extract idx stop).toList.get ⟨j, h_j_lt_len⟩ = arr[idx + j]! := by
  have h_j_lt_size : j < (arr.extract idx stop).size := by
    rwa [Array.length_toList] at h_j_lt_len
  have h_extract_size : (arr.extract idx stop).size = stop - idx := by
    apply Array.size_extract_of_start_lt_stop_le_size arr idx stop h_idx_lt_stop h_stop_le_size
  have h_idx_j_lt_stop : idx + j < stop := by
    rw [h_extract_size] at h_j_lt_size
    exact Nat.add_lt_of_lt_sub' h_j_lt_size
  have h_idx_j_lt_arr_size : idx + j < arr.size := by
    apply Nat.lt_of_lt_of_le h_idx_j_lt_stop h_stop_le_size
  rw [List.get_eq_getElem, Array.getElem_toList]
  have h_extract_elem : (arr.extract idx stop)[j]'h_j_lt_size =
      arr[idx + j]'h_idx_j_lt_arr_size := by
    rw [Array.getElem_extract]
  rw [h_extract_elem]
  exact Eq.symm (Array.getElem_eq_get_safe h_idx_j_lt_arr_size)

/-- When j > 0, extracting from index idx+1 gives the same element as from idx at position j-1. -/
lemma _root_.Array.extract_idx_succ_elem_eq {α : Type} [Inhabited α]
    (arr : Array α) (idx : Nat) (_ : Nat) (j : Nat) (h_j_gt_zero : j > 0) :
  arr[idx + j]! = arr[(idx + 1) + (j - 1)]! := by
  calc
    arr[idx + j]!
      = arr[idx + ((j - 1) + 1)]! := by
        rw [Nat.sub_add_cancel (Nat.one_le_of_lt h_j_gt_zero)]
    _ = arr[idx + (1 + (j - 1))]! := by
        rw [Nat.add_comm (j - 1) 1]
    _ = arr[(idx + 1) + (j - 1)]! := by
        rw [Nat.add_assoc]

lemma _root_.Array.extract_toList_getElem_succ {α : Type} [Inhabited α]
    (arr : Array α) (idx : Nat) (stop : Nat)
    (h_idx_succ_lt_stop : idx + 1 < stop) (h_stop_le_arr_size : stop ≤ arr.size)
    (j : Nat) (h_j_gt_zero : j > 0)
    (h_j_lt_len : j < (arr.extract idx stop).toList.length)
    (h_j_minus_1_lt_next_len : j - 1 < (arr.extract (idx + 1) stop).toList.length) :
  (arr.extract idx stop).toList.get ⟨j, h_j_lt_len⟩ =
  (arr.extract (idx + 1) stop).toList.get ⟨j - 1, h_j_minus_1_lt_next_len⟩ := by
  have h_idx_lt_stop : idx < stop := Nat.lt_of_succ_lt h_idx_succ_lt_stop
  rw [Array.extract_toList_getElem arr idx stop j h_j_lt_len h_idx_lt_stop h_stop_le_arr_size]
  rw [Array.extract_toList_getElem arr (idx + 1) stop (j - 1)
      h_j_minus_1_lt_next_len h_idx_succ_lt_stop h_stop_le_arr_size]
  exact Array.extract_idx_succ_elem_eq arr idx stop j h_j_gt_zero

/-- Local cons-list zero-getter (about `.get`, complementing Mathlib's `[0]` lemma). -/
lemma _root_.List.getElem_cons_zero_local {α : Type} (head : α) (tail : List α)
    (h_len : 0 < (head :: tail).length) :
  (head :: tail).get ⟨0, h_len⟩ = head := by
  rfl

lemma _root_.List.getElem_cons_pos {α : Type}
    (head : α) (tail : List α)
    (j : Nat) (h_j_gt_zero : j > 0)
    (h_j_lt_len : j < (head :: tail).length) :
  (head :: tail).get ⟨j, h_j_lt_len⟩ =
    tail.get ⟨j - 1, by
      rw [List.length_cons] at h_j_lt_len
      exact Nat.sub_lt_right_of_lt_add h_j_gt_zero h_j_lt_len
    ⟩ := by
  match j with
  | 0 => contradiction
  | k+1 =>
    exact rfl

/-- Main lemma using the helper lemmas -/
lemma _root_.Array.extract_toList_getElem_eq_cons_extract_toList_getElem {α : Type} [Inhabited α]
    (arr : Array α) (idx : Nat) (stop : Nat)
    (h_idx_lt_stop : idx < stop) (h_stop_le_arr_size : stop ≤ arr.size)
    (j : Nat) (h_j_lt_lhs_len : j < (arr.extract idx stop).toList.length)
    (h_j_lt_rhs_len : j < (arr[idx]! :: (arr.extract (idx + 1) stop).toList).length) :
  (arr.extract idx stop).toList.get ⟨j, h_j_lt_lhs_len⟩ =
  (arr[idx]! :: (arr.extract (idx + 1) stop).toList).get ⟨j, h_j_lt_rhs_len⟩ := by
  by_cases h_j_eq_zero : j = 0
  · subst j; rw [List.getElem_cons_zero_local]
    exact Array.extract_toList_getElem_zero arr idx stop h_idx_lt_stop h_stop_le_arr_size
      h_j_lt_lhs_len
  · have h_j_gt_zero : j > 0 := Nat.pos_of_ne_zero h_j_eq_zero
    rw [List.getElem_cons_pos (arr[idx]!) ((arr.extract (idx + 1) stop).toList) j h_j_gt_zero
      h_j_lt_rhs_len]
    have h_j_minus_1_lt_tail_len_size : j - 1 < (arr.extract (idx + 1) stop).size := by
        rw [← Array.length_toList]
        rw [List.length_cons] at h_j_lt_rhs_len
        exact Nat.sub_lt_right_of_lt_add h_j_gt_zero h_j_lt_rhs_len
    have h_idx_plus_1_lt_stop : idx + 1 < stop := by
      apply Nat.lt_of_not_ge
      intro hc_idx_plus_1_ge_stop
      have h_tail_size_zero : (arr.extract (idx + 1) stop).size = 0 :=
        Array.size_extract_of_stop_le_start arr (idx + 1) stop hc_idx_plus_1_ge_stop
      rw [h_tail_size_zero] at h_j_minus_1_lt_tail_len_size
      exact Nat.not_lt_zero (j - 1) h_j_minus_1_lt_tail_len_size
    have h_j_minus_1_lt_tail_len : j - 1 < (arr.extract (idx + 1) stop).toList.length := by
      rw [List.length_cons] at h_j_lt_rhs_len
      exact Nat.sub_lt_right_of_lt_add h_j_gt_zero h_j_lt_rhs_len
    exact Array.extract_toList_getElem_succ arr idx stop h_idx_plus_1_lt_stop h_stop_le_arr_size
      j h_j_gt_zero h_j_lt_lhs_len h_j_minus_1_lt_tail_len

-- Refactored main lemma
lemma _root_.Array.extract_toList_eq_getElem_bang_cons_extract_toList {α : Type} [Inhabited α]
    (arr : Array α) (idx : Nat) (stop : Nat)
    (h_idx_lt_stop : idx < stop) (h_stop_le_arr_size : stop ≤ arr.size) :
  (arr.extract idx stop).toList = arr[idx]! :: (arr.extract (idx + 1) stop).toList := by
  apply List.ext_getElem
  · exact Array.extract_toList_length_eq_cons_extract_toList_length arr idx stop h_idx_lt_stop
      h_stop_le_arr_size
  · intros j h_j_lt_lhs_len h_j_lt_rhs_len
    exact Array.extract_toList_getElem_eq_cons_extract_toList_getElem arr idx stop h_idx_lt_stop
      h_stop_le_arr_size j h_j_lt_lhs_len h_j_lt_rhs_len

/--
Helper Lemma for flat index bounds, proving one step of the standard inductive argument:
If `flatIndex_lower_dims < weight_current_dim`
(i.e. `flatIndex_lower_dims <= weight_current_dim - 1`),
and `index_current_dim < size_current_dim`, then
`index_current_dim * weight_current_dim + flatIndex_lower_dims <
  size_current_dim * weight_current_dim`.
This means `index_current_dim * weight_current_dim + flatIndex_lower_dims <=
  size_current_dim * weight_current_dim - 1`.
This lemma is structured for a right-to-left (least-significant to most-significant)
calculation.
-/
lemma flatIndex_step_bound (flatIndex_lower_dims : Nat) (weight_current_dim : Nat)
    (index_current_dim : Nat) (size_current_dim : Nat)
    (h_lower_bound : flatIndex_lower_dims < weight_current_dim)
    (h_index_bound : index_current_dim < size_current_dim)
    (h_weight_pos : weight_current_dim > 0)
    (h_dim_pos : size_current_dim > 0) :
  index_current_dim * weight_current_dim + flatIndex_lower_dims <
      size_current_dim * weight_current_dim := by
  calc
    index_current_dim * weight_current_dim + flatIndex_lower_dims
    _ <= (size_current_dim - 1) * weight_current_dim + flatIndex_lower_dims := by
      apply Nat.add_le_add_right
      apply Nat.mul_le_mul_right weight_current_dim (Nat.le_pred_of_lt h_index_bound)
    _ <= (size_current_dim - 1) * weight_current_dim + (weight_current_dim - 1) := by
      apply Nat.add_le_add_left
      exact Nat.le_pred_of_lt h_lower_bound
    _ = size_current_dim * weight_current_dim - weight_current_dim + weight_current_dim - 1 := by
      have h_distrib : (size_current_dim - 1) * weight_current_dim =
          size_current_dim * weight_current_dim - weight_current_dim :=
        Nat.sub_one_mul size_current_dim weight_current_dim
      rw [h_distrib]
      omega
    _ = size_current_dim * weight_current_dim - 1 := by
      have h_le : weight_current_dim ≤ size_current_dim * weight_current_dim := by
        rw [← Nat.one_mul weight_current_dim]
        exact Nat.le_mul_of_pos_left (1 * weight_current_dim) h_dim_pos
      rw [Nat.sub_add_cancel h_le] -- a - b + b = a if b <= a
    _ < size_current_dim * weight_current_dim := by
      apply Nat.sub_lt
      · exact Nat.mul_pos h_dim_pos h_weight_pos
      · exact Nat.zero_lt_one

/--
Lemma: The product of `shape.extract 0 (k_idx + 1)` can be expressed in terms of
the product of `shape.extract 0 k_idx` and `shape[k_idx]!`.
-/
lemma product_extract_prefix_step (shape : Array Nat) (k_idx : Nat)
    (h_k_idx_lt_shape_size : k_idx < shape.size)
    : (shape.extract 0 (k_idx + 1)).foldl (· * ·) 1 =
      shape[k_idx]! * (shape.extract 0 k_idx).foldl (· * ·) 1 := by
  let len_k_plus_1 := k_idx + 1
  have h_len_k_plus_1_le_size : len_k_plus_1 ≤ shape.size :=
    Nat.succ_le_of_lt h_k_idx_lt_shape_size
  have h_k_idx_le_size : k_idx ≤ shape.size := Nat.le_of_lt h_k_idx_lt_shape_size
  rw [← Array.foldl_toList, ← Array.foldl_toList]
  rw [← List.prod_eq_foldl, ← List.prod_eq_foldl]
  rw [Array.extract_prefix_toList_eq_take_toList shape len_k_plus_1 h_len_k_plus_1_le_size]
  rw [Array.extract_prefix_toList_eq_take_toList shape k_idx h_k_idx_le_size]
  have h_k_idx_lt_list_len : k_idx < shape.toList.length := by
    rw [Array.length_toList]; exact h_k_idx_lt_shape_size
  rw [List.prod_take_succ _ _ h_k_idx_lt_list_len]
  have h_list_get_eq_array_get_bang : shape.toList[k_idx] = shape[k_idx]! := by
    simp only [Array.getElem_toList]
    exact Eq.symm (Array.getElem_eq_get_safe h_k_idx_lt_shape_size)
  rw [h_list_get_eq_array_get_bang]
  exact Nat.mul_comm _ _

/--
Lemma: Given `index_val < dimSize_k` and positive `stride`,
`index_val * stride + stride - 1 ≤ dimSize_k * stride - 1`.
This is a core arithmetic step for the flat index bound.
-/
lemma weighted_sum_le_of_lt (index_val dimSize_k stride : Nat)
    (h_index_lt : index_val < dimSize_k)
    (h_stride_pos : stride > 0)
    : index_val * stride + stride - 1 ≤ dimSize_k * stride - 1 := by
  have h_intermediate_le : index_val * stride + stride ≤ dimSize_k * stride := by
    rw [← Nat.succ_mul]
    exact Nat.mul_le_mul_right stride h_index_lt
  have h_one_le_lhs_term : 1 ≤ index_val * stride + stride := by
    calc
      1 ≤ stride := h_stride_pos
      _ ≤ index_val * stride + stride := Nat.le_add_left stride (index_val * stride)
  exact Nat.sub_le_sub_right h_intermediate_le 1

/--
Lemma: The flat index bound invariant is maintained through one step of `computeHelper`'s
recursion. The invariant is
`current_sum_from_higher_dims + max_possible_sum_from_current_and_lower_dims < totalProduct`.
This simplifies to
`current_sum_from_higher_dims + Product(dims_current_to_0) - 1 < totalProduct`.

Let `k_idx = rank - 1 - i_rev` be the index of the current dimension being processed.
`flatIndexRel` is the sum from dimensions `rank-1` down to `k_idx+1`.
`stride` is `Product(shape[0]...shape[k_idx-1])`, the weight for `indices[k_idx]`.
`totalProduct` is `Product(shape[0]...shape[rank-1])`.
-/
lemma flatIndex_bound_maintained
  (shape : Array Nat) (rank : Nat) (indices : Array Nat)
  (i_rev : Nat) (flatIndexRel : Nat) (stride : Nat) (totalProduct : Nat)
  (h_i_rev : i_rev < rank)
  (h_rank_eq_size : rank = shape.size)
  (h_index_lt : indices[rank - 1 - i_rev]! < shape[rank - 1 - i_rev]!)
  (h_dims_pos : ∀ (j : Fin rank), shape[j.val]'(by
    have h1 : j.val < rank := j.isLt
    have h2 : rank = shape.size := h_rank_eq_size
    exact Nat.lt_of_lt_of_eq h1 h2
  ) > 0)
  (h_stride_pos : stride > 0)
  (h_stride_definition : stride = (shape.extract 0 (rank - 1 - i_rev)).foldl (· * ·) 1)
  :
  let k_idx_stmt := rank - 1 - i_rev
  let index_val_stmt := indices[k_idx_stmt]!
  let _dimSize_k_stmt := shape[k_idx_stmt]!
  let prod_dims_0_to_k_stmt := (shape.extract 0 (k_idx_stmt + 1)).foldl (· * ·) 1
  let prod_dims_0_to_k_minus_1_stmt := stride
  (flatIndexRel + prod_dims_0_to_k_stmt - 1 < totalProduct) →
  (flatIndexRel + index_val_stmt * stride + prod_dims_0_to_k_minus_1_stmt - 1 < totalProduct) := by
  let k_idx := rank - 1 - i_rev
  let index_val := indices[k_idx]!
  let dimSize_k := shape[k_idx]!
  let prod_dims_0_to_k := (shape.extract 0 (k_idx + 1)).foldl (· * ·) 1
  let prod_dims_0_to_k_minus_1 := stride
  have h_k_idx_lt_shape_size : k_idx < shape.size := by
    rw [← h_rank_eq_size]
    have h_rank_pos : rank > 0 := Nat.pos_of_ne_zero (fun h_r_eq_0 =>
      Nat.not_lt_zero i_rev (h_r_eq_0 ▸ h_i_rev))
    omega
  have h_prod_decomp : prod_dims_0_to_k = dimSize_k * stride := by
    rw [h_stride_definition]
    exact product_extract_prefix_step shape k_idx h_k_idx_lt_shape_size
  intro h_bound_val
  have h_bound_val := by simpa [h_prod_decomp] using h_bound_val
  apply Nat.lt_of_le_of_lt
  · have h1 := weighted_sum_le_of_lt index_val dimSize_k stride h_index_lt h_stride_pos
    calc
      flatIndexRel + index_val * stride + stride - 1
          ≤ flatIndexRel + (dimSize_k * stride - 1) := by omega
    _ = flatIndexRel + prod_dims_0_to_k - 1 := by
      rw [h_prod_decomp]
      have h_dim_k_pos : dimSize_k > 0 := by
        let fin_k_idx : Fin rank :=
          ⟨k_idx, by { rwa [←h_rank_eq_size] at h_k_idx_lt_shape_size }⟩
        change shape[k_idx]! > 0
        rw [Array.getElem_eq_get_safe (Nat.lt_of_lt_of_eq fin_k_idx.isLt h_rank_eq_size)]
        exact h_dims_pos fin_k_idx
      have h_one_le_ds_stride : 1 ≤ dimSize_k * stride :=
        one_le_mul_of_one_le_of_one_le (Nat.one_le_of_lt h_dim_k_pos)
          (Nat.one_le_of_lt h_stride_pos)
      rw [Nat.add_sub_assoc h_one_le_ds_stride]

/-- For empty shape arrays, the product is 1. -/
lemma empty_array_product (shape : Array Nat) (h_shape_size_eq_zero : shape.size = 0) :
    shape.foldl (· * ·) 1 = 1 := by
  rw [← Array.foldl_toList]
  have h_toList_nil : shape.toList = [] := by
    apply List.eq_nil_of_length_eq_zero
    rw [Array.length_toList, h_shape_size_eq_zero]
  rw [h_toList_nil, List.foldl_nil]

/-- When rank = 0, shape.extract 0 0 product is 1. -/
lemma extract_zero_zero_product (shape : Array Nat) :
  (shape.extract 0 0).foldl (· * ·) 1 = 1 := by
  exact extract_empty_product shape 0

/-- Base case: Extracting prefix from an empty shape array gives a product of 1. -/
lemma extract_prefix_of_empty_shape (shape : Array Nat) (h_shape_size_eq_zero : shape.size = 0) :
  (shape.extract 0 0).foldl (· * ·) 1 = shape.foldl (· * ·) 1 := by
  rw [extract_zero_zero_product, empty_array_product shape h_shape_size_eq_zero]

/-- Helper lemma for the base case when rank = 0 -/
lemma computeHelper_bounds_rank_zero
    (shape : Array Nat)
    (h_rank_eq_size : 0 = shape.size)
    (indices : Array Nat) (_ : indices.size = 0)
    (flatIndexRel : Nat) (stride : Nat)
    (h_stride : stride = (shape.extract 0 0).foldl (· * ·) 1)
    (h_flatIndexRel : flatIndexRel < stride * (shape.extract 0 0).foldl (· * ·) 1) :
    flatIndexRel < shape.foldl (· * ·) 1 := by
  rw [extract_zero_zero_product] at h_stride
  subst stride
  rw [extract_zero_zero_product, mul_one] at h_flatIndexRel
  rw [empty_array_product shape (Eq.symm h_rank_eq_size)]
  exact h_flatIndexRel

/-- Extracts the crucial components from computeHelper when i_rev = 0 and rank > 0. -/
lemma extract_computeHelper_i_rev_zero_components
    (shape : Array Nat) (rank : Nat) (indices : Array Nat)
    (flatIndexRel stride result : Nat)
    (h_rank_gt_zero : rank > 0)
    (h_helper : computeHelper shape rank indices 0 flatIndexRel stride = Except.ok result) :
    let k_idx := rank - 1
    let index_val := indices[k_idx]!
    let dim_size := shape[k_idx]!
    (index_val < dim_size) ∧
    (computeHelper shape rank indices 1 (flatIndexRel + index_val * stride) (stride * dim_size) =
      Except.ok result) := by
  unfold computeHelper at h_helper
  simp only [Nat.sub_zero, Nat.add_one] at h_helper
  split_ifs at h_helper with h_if_cond
  · exfalso
    exact Nat.lt_le_asymm h_rank_gt_zero h_if_cond
  · by_cases h_idx_ge_dim : indices[rank - 1]! >= shape[rank - 1]!
    · simp at h_helper
      omega
    · apply And.intro
      · exact Nat.lt_of_not_ge h_idx_ge_dim
      · exact h_helper

/-- When i_rev = 0, the stride for the recursive call equals the product of the single dimension. -/
lemma stride_for_i_rev_zero_recursive_call
    (shape : Array Nat) (rank : Nat)
    (h_rank_gt_zero : rank > 0)
    (h_rank_eq_size : rank = shape.size)
    (stride : Nat) (h_stride_eq_one : stride = 1) :
    let k_idx := rank - 1
    let dim_size := shape[k_idx]!
    stride * dim_size = (shape.extract (rank - 1) rank).foldl (· * ·) 1 := by
  let k_idx := rank - 1
  let dim_size := shape[k_idx]!
  have h_k_idx_lt_shape_size : k_idx < shape.size := by
    rw [←h_rank_eq_size]
    exact Nat.sub_one_lt_of_lt h_rank_gt_zero
  have product_extract_single_element_eq_getElem_bang :
      (shape.extract k_idx (k_idx+1)).foldl (· * ·) 1 = shape[k_idx]! := by
    have hkp1_le_size : k_idx + 1 ≤ shape.size :=
      Nat.succ_le_of_lt h_k_idx_lt_shape_size
    rw [← Array.foldl_toList, Array.extract_toList_eq_getElem_bang_cons_extract_toList
        shape k_idx (k_idx+1) (Nat.lt_succ_self _) hkp1_le_size]
    simp only [Array.extract_empty_of_start_eq_stop, Array.toList_empty, List.foldl_cons, one_mul,
      List.foldl_nil]
  have h_extract_eq : shape.extract (rank - 1) rank = shape.extract k_idx (k_idx+1) := by
    simp only [k_idx]
    have h_eq : rank - 1 + 1 = rank := by rw [Nat.sub_one_add_one_eq_of_pos h_rank_gt_zero]
    rw [h_eq]
  rw [h_extract_eq]
  clear_value dim_size
  have h_dim_size_eq : shape[k_idx]! = shape[rank - 1]! := by
    simp [k_idx]
  rw [h_dim_size_eq] at product_extract_single_element_eq_getElem_bang
  rw [product_extract_single_element_eq_getElem_bang]
  rw [h_stride_eq_one]
  exact
    let k_idx := rank - 1;
    let dim_size := shape[k_idx]!;
    Nat.one_mul dim_size

/--
When all dimensions in a shape array are positive, the product of any prefix extract
is also positive.
-/
lemma extract_prefix_product_positive (shape : Array Nat) (rank : Nat) (i : Nat)
    (h_rank_eq_size : rank = shape.size)
    (h_i_le_rank : i ≤ rank)
    (h_dims_pos : ∀ (k : Fin rank), shape[k]! > 0) :
    (shape.extract 0 i).foldl (· * ·) 1 > 0 := by
  rw [← Array.foldl_toList]
  rw [← List.prod_eq_foldl]
  have h_i_le_shape_size : i ≤ shape.size := by
    rw [←h_rank_eq_size]; exact h_i_le_rank
  rw [Array.extract_prefix_toList_eq_take_toList shape i h_i_le_shape_size]
  apply List.prod_pos
  intro x hx
  have h_mem_take : x ∈ List.take i shape.toList := hx
  have h_mem_characterize : ∃ j < i, shape.toList[j]? = some x := by
    have ⟨p, hp⟩ := List.get_of_mem h_mem_take
    have h_p_lt_drop_len : p.val < (List.take i shape.toList).length := p.isLt
    have h_get_take_p_eq_x : (List.take i shape.toList).get p = x := hp
    let j := p.val
    have h_j_lt_i : j < i := by
        have h_take_len : (List.take i shape.toList).length = min i shape.toList.length :=
          List.length_take
        have h_p_lt_min : p.val < min i shape.toList.length := by
          rw [← h_take_len]
          exact h_p_lt_drop_len
        exact Nat.lt_of_lt_of_le h_p_lt_min (min_le_left i shape.toList.length)
    have h_j_lt_list_len : j < shape.toList.length := by
      exact Nat.lt_of_lt_of_le h_j_lt_i h_i_le_shape_size
    have h_toList_j_eq_x : shape.toList[j] = x := by
      have h_get_take_eq_getElem :
          (List.take i shape.toList).get p = (List.take i shape.toList)[p.val] := rfl
      rw [← h_get_take_p_eq_x, h_get_take_eq_getElem]
      apply Eq.symm
      apply List.getElem_take
    use j
    constructor
    · exact h_j_lt_i
    · simp only [h_j_lt_list_len, List.getElem?_eq_getElem]
      exact congr_arg some h_toList_j_eq_x
  rcases h_mem_characterize with ⟨j, h_j_lt_i, h_get_eq⟩
  have h_toList_length : shape.toList.length = shape.size := Array.length_toList
  have h_j_lt_len : j < shape.toList.length := by
    rw [h_toList_length]
    rw [←h_rank_eq_size]
    exact Nat.lt_of_lt_of_le h_j_lt_i h_i_le_rank
  have h_j_lt_shape_size : j < shape.size := by
    rw [← h_toList_length]
    exact h_j_lt_len
  have h_j_lt_rank : j < rank := by
    rw [h_rank_eq_size]
    exact h_j_lt_shape_size
  let fin_j : Fin rank := ⟨j, h_j_lt_rank⟩
  have h_shape_j_eq_x : x = shape[j]! := by
    have h_shape_j_idx : shape.toList[j] = shape[j]! :=
      calc
        shape.toList[j] = shape[j]   := Array.getElem_toList h_j_lt_shape_size
        _               = shape[j]!  := by
              exact Eq.symm (Array.getElem_eq_get_safe h_j_lt_shape_size)
    have h_x_eq_toList_j : x = shape.toList[j] := by
      rw [← Option.some_inj]
      rw [← List.getElem?_eq_getElem h_j_lt_len]
      exact h_get_eq.symm
    rw [h_x_eq_toList_j]
    exact h_shape_j_idx
  rw [h_shape_j_eq_x]
  have h_shape_j_eq_shape_fin_j : shape[j]! = shape[fin_j.val] := by
    exact Array.getElem_eq_get_safe h_j_lt_shape_size
  rw [h_shape_j_eq_shape_fin_j]
  have h_pos := h_dims_pos fin_j
  exact Nat.lt_of_lt_of_eq (h_dims_pos fin_j) h_shape_j_eq_shape_fin_j

/--
When all dimensions in a shape array are positive, the product of any sub-array extract
is also positive.
-/
lemma extract_sub_array_product_positive (shape : Array Nat) (rank_param : Nat)
    (start_idx stop_idx : Nat)
    (h_rank_eq_size : rank_param = shape.size)
    (h_start_le_stop : start_idx ≤ stop_idx)
    (h_stop_le_rank : stop_idx ≤ rank_param)
    (h_dims_pos_bang : ∀ (k : Fin rank_param), shape[k]! > 0) :
    (shape.extract start_idx stop_idx).foldl (· * ·) 1 > 0 := by
  rw [← Array.foldl_toList, ← List.prod_eq_foldl]
  apply List.prod_pos
  intro x hx_mem_extract_toList
  have ⟨idx_in_extract_val, h_idx_lt_len, h_get_eq_x⟩ :
      ∃ (i : Nat) (h_lt_proof : i < (shape.extract start_idx stop_idx).toList.length),
                  (shape.extract start_idx stop_idx).toList.get ⟨i, h_lt_proof⟩ = x := by
    exact List.mem_iff_getElem.mp hx_mem_extract_toList
  let extracted_arr := shape.extract start_idx stop_idx
  have h_idx_lt_extracted_size : idx_in_extract_val < extracted_arr.size := by
    rwa [Array.length_toList] at h_idx_lt_len
  let original_idx := start_idx + idx_in_extract_val
  have h_stop_le_shape_size : stop_idx ≤ shape.size := by
    rw [←h_rank_eq_size]; exact h_stop_le_rank
  have h_original_idx_lt_shape_size : original_idx < shape.size := by
    by_cases h_start_eq_stop : start_idx = stop_idx
    · have h_extracted_size_zero : extracted_arr.size = 0 :=
        Array.size_extract_of_stop_le_start shape start_idx stop_idx
          (h_start_eq_stop ▸ Nat.le_refl _)
      rw [h_extracted_size_zero] at h_idx_lt_extracted_size
      exact absurd h_idx_lt_extracted_size (Nat.not_lt_zero _)
    have h_start_lt_stop : start_idx < stop_idx :=
      Nat.lt_of_le_of_ne h_start_le_stop h_start_eq_stop
    have h_extracted_arr_size_formula : extracted_arr.size = stop_idx - start_idx :=
      Array.size_extract_of_start_lt_stop_le_size shape start_idx stop_idx h_start_lt_stop
        h_stop_le_shape_size
    rw [h_extracted_arr_size_formula] at h_idx_lt_extracted_size
    have h_sum_lt_stop : start_idx + idx_in_extract_val < stop_idx :=
      Nat.add_lt_of_lt_sub' h_idx_lt_extracted_size
    exact Nat.lt_of_lt_of_le h_sum_lt_stop h_stop_le_shape_size
  have h_x_eq_shape_original_idx_bang : x = shape[original_idx]! := by
    rw [←h_get_eq_x]
    rw [List.get_eq_getElem, Array.getElem_toList]
    have h_get_extract : extracted_arr[idx_in_extract_val]'h_idx_lt_extracted_size =
        shape[original_idx]'h_original_idx_lt_shape_size := by
      simp only [extracted_arr, original_idx]
      rw [Array.getElem_extract]
    rw [h_get_extract]
    exact Eq.symm (Array.getElem_eq_get_safe h_original_idx_lt_shape_size)
  rw [h_x_eq_shape_original_idx_bang]
  have h_original_idx_lt_rank : original_idx < rank_param := by
    rw [h_rank_eq_size]; exact h_original_idx_lt_shape_size
  let fin_original_idx : Fin rank_param := ⟨original_idx, h_original_idx_lt_rank⟩
  exact h_dims_pos_bang fin_original_idx

/-- The flatIndexRel bound is maintained for the recursive call when i_rev = 0. -/
lemma flatIndexRel_bound_for_i_rev_zero_recursive_call
    (shape : Array Nat) (rank : Nat)
    (h_rank_gt_zero : rank > 0)
    (h_rank_eq_size : rank = shape.size)
    (_ : Array Nat)
    (flatIndexRel : Nat) (stride : Nat)
    (h_stride : stride = (shape.extract rank rank).foldl (· * ·) 1)
    (h_flatIndexRel : flatIndexRel < stride * (shape.extract 0 rank).foldl (· * ·) 1)
    (h_dims_pos : ∀ (k : Fin rank), shape[k]! > 0)
    (index_val : Nat) (dim_size : Nat)
    (h_index_val_lt_dim_size : index_val < dim_size)
    (h_dim_size_eq : dim_size = shape[rank - 1]!)
    (h_flatIndexRel_is_zero : flatIndexRel = 0) :
    flatIndexRel + index_val * stride <
    (stride * dim_size) * (shape.extract 0 (rank - 1)).foldl (· * ·) 1 := by
  have h_stride_is_one : stride = 1 := by
    rw [h_stride, extract_empty_product]
  let prefix_product := (shape.extract 0 (rank - 1)).foldl (· * ·) 1
  rw [h_stride_is_one] at *
  have h_extract_decomp : (shape.extract 0 rank).foldl (· * ·) 1 =
                         prefix_product * shape[rank - 1]! := by
    have h_k_idx_lt_shape_size : rank - 1 < shape.size := by
      rw [←h_rank_eq_size]
      exact Nat.sub_lt h_rank_gt_zero (Nat.zero_lt_one)
    have h_extract_eq : (shape.extract 0 rank).foldl (· * ·) 1 =
                         shape[rank - 1]! * (shape.extract 0 (rank - 1)).foldl (· * ·) 1 := by
        have h_simplify : rank - 1 + 1 = rank := by rw [Nat.sub_one_add_one_eq_of_pos
            h_rank_gt_zero]
        have h_step := product_extract_prefix_step shape (rank - 1) h_k_idx_lt_shape_size
        rw [h_simplify] at h_step
        rw [← h_step]
    rw [h_extract_eq]
    exact Nat.mul_comm _ _
  have h_flat_index_bound : flatIndexRel < dim_size * prefix_product := by
    rw [h_dim_size_eq]
    rw [h_extract_decomp] at h_flatIndexRel
    rw [h_stride_is_one] at h_flatIndexRel
    have h_mul_one : stride * (prefix_product * shape[rank - 1]!) =
                     prefix_product * shape[rank - 1]! := by
      rw [h_stride_is_one]
      subst h_dim_size_eq h_rank_eq_size h_stride
      simp_all only [gt_iff_lt, Fin.getElem!_fin, Array.extract_size, Array.extract_eq_pop,
        Array.size_pop, Array.extract_empty_of_start_eq_stop, List.size_toArray,
        List.length_nil, List.foldl_toArray', List.foldl_nil, one_mul, prefix_product]
    rw [h_mul_one] at h_flatIndexRel
    rw [Nat.mul_comm prefix_product shape[rank - 1]!] at h_flatIndexRel
    exact h_flatIndexRel
  have h_prefix_product_pos : prefix_product > 0 := by
    apply extract_prefix_product_positive shape rank (rank - 1)
    · exact h_rank_eq_size
    · exact Nat.sub_le rank 1
    · exact h_dims_pos
  have h_dim_size_pos : dim_size > 0 := by
    let k_idx := rank - 1
    let fin_k_idx : Fin rank := ⟨k_idx, Nat.sub_lt h_rank_gt_zero (Nat.zero_lt_one)⟩
    rw [h_dim_size_eq]
    exact h_dims_pos fin_k_idx
  simp only [mul_one, one_mul, Array.size_extract, tsub_zero, gt_iff_lt]
  have h_extract_normalize :
      Array.foldl (· * ·) 1 (shape.extract 0 (rank - 1)) = prefix_product := by
    rfl
  have h_min_simplify : (rank - 1) ⊓ shape.size = rank - 1 := by
    rw [h_rank_eq_size]
    exact min_eq_left (Nat.sub_le shape.size 1)
  have h_extract_rewrite : shape.extract 0 (rank - 1) =
    let sz' := ((rank - 1) ⊓ shape.size).sub 0;
    Array.extract.loop shape sz' 0 (Array.mkEmpty sz') := rfl
  rw [h_rank_eq_size] at h_min_simplify
  have h_extract_expanded : shape.extract 0 (rank - 1) =
    let sz' := (rank - 1).sub 0;
    Array.extract.loop shape sz' 0 (Array.mkEmpty sz') := by
    rw [h_extract_rewrite]
    simp only [h_min_simplify, h_rank_eq_size]
  have h_goal_proof : flatIndexRel + index_val < dim_size * prefix_product := by
    rw [h_flatIndexRel_is_zero, Nat.zero_add]
    apply Nat.lt_of_lt_of_le h_index_val_lt_dim_size
    exact Nat.le_mul_of_pos_right dim_size h_prefix_product_pos
  let arr_for_fold := shape.extract 0 (rank - 1)
  have h_fold_equiv : Array.foldl (· * ·) 1 arr_for_fold 0 ((rank - 1) ⊓ shape.size) =
      Array.foldl (· * ·) 1 arr_for_fold := by
    have h_stop_arg_eq_arr_size : ((rank - 1) ⊓ shape.size) = arr_for_fold.size := by
      rw [Array.size_extract]
      simp only [tsub_zero]
    rw [h_stop_arg_eq_arr_size]
  rw [h_fold_equiv]
  rw [h_extract_normalize]
  exact h_goal_proof

/-- For rank = 0, computeHelper returns flatIndexRel directly. -/
lemma computeHelper_rank_zero
    (shape : Array Nat) (indices : Array Nat)
    (flatIndexRel stride : Nat) :
    computeHelper shape 0 indices 0 flatIndexRel stride = Except.ok flatIndexRel := by
  unfold computeHelper
  simp only [Nat.zero_le, if_true]

/-- For empty shape arrays, the product is 1. -/
lemma empty_shape_product
    (shape : Array Nat) (h_shape_size_eq_zero : shape.size = 0) :
    shape.foldl (· * ·) 1 = 1 := by
  rw [empty_array_product shape h_shape_size_eq_zero]

/-- For rank = 0, stride is 1. -/
lemma stride_rank_zero
    (shape : Array Nat) (stride : Nat)
    (h_stride : stride = (shape.extract 0 0).foldl (· * ·) 1) :
    stride = 1 := by
  rw [h_stride, extract_zero_zero_product]

/-- For the rank = 0 case, flatIndexRel is bounded by 1. -/
lemma flatIndexRel_bound_rank_zero
    (shape : Array Nat) (flatIndexRel stride : Nat)
    (_ : shape.size = 0)
    (h_stride : stride = (shape.extract 0 0).foldl (· * ·) 1)
    (h_flatIndexRel : flatIndexRel < stride * (shape.extract 0 0).foldl (· * ·) 1) :
    flatIndexRel < 1 := by
  have h_stride_eq_one := stride_rank_zero shape stride h_stride
  rw [h_stride_eq_one] at h_flatIndexRel
  rw [extract_zero_zero_product, Nat.one_mul] at h_flatIndexRel
  exact h_flatIndexRel

/-- Extracts the components of the recursive computeHelper call for i_rev = 0. -/
lemma extract_recursive_call_components
    (shape : Array Nat) (rank : Nat) (indices : Array Nat)
    (flatIndexRel stride result : Nat)
    (h_rank_gt_zero : rank > 0)
    (h_helper : computeHelper shape rank indices 0 flatIndexRel stride = Except.ok result) :
    let k_idx := rank - 1
    let index_val := indices[k_idx]!
    let dim_size := shape[k_idx]!
    (index_val < dim_size) ∧
    (computeHelper shape rank indices 1 (flatIndexRel + index_val * stride) (stride * dim_size) =
      Except.ok result) := by
  exact extract_computeHelper_i_rev_zero_components shape rank indices flatIndexRel stride
    result h_rank_gt_zero h_helper

/-- For rank = 1, the recursive call with i_rev = 1 directly returns the result. -/
lemma recursive_call_rank_one
    (shape : Array Nat) (indices : Array Nat)
    (_ stride _ new_flat_index : Nat) :
    computeHelper shape 1 indices 1 new_flat_index (stride * shape[0]!) =
      Except.ok new_flat_index := by
  unfold computeHelper
  simp only [ge_iff_le, le_refl, if_true]

/-- Base case of computeHelper_bounds theorem when i_rev = 0 and rank = 0. -/
lemma computeHelper_bounds_base_rank_zero'
    (shape : Array Nat) (rank : Nat)
    (h_rank_eq_size : rank = shape.size)
    (h_rank_zero : rank = 0)
    (h_dims_pos : ∀ (i : Fin rank), shape[i]'(by
      have h1 : i.val < rank := i.isLt
      have h2 : rank = shape.size := h_rank_eq_size
      exact Nat.lt_of_lt_of_eq h1 h2
    ) > 0)
    (indices : Array Nat) (_ : indices.size = rank)
    (flatIndexRel : Nat) (stride : Nat)
    (h_stride : stride = (shape.extract rank rank).foldl (· * ·) 1)
    (h_flatIndexRel : flatIndexRel < stride * (shape.extract 0 rank).foldl (· * ·) 1)
    (result : Nat)
    (h_helper : computeHelper shape rank indices 0 flatIndexRel stride = Except.ok result)
    (h_shape_size_zero : shape.size = 0)     :
    result < shape.foldl (· * ·) 1 := by
  rw [h_rank_zero] at *
  have h_zero_eq_size : 0 = shape.size := by
    rw [←h_rank_eq_size]
    subst h_rank_eq_size h_stride
    simp_all only [Fin.getElem_fin, gt_iff_lt,
      Array.extract_empty_of_start_eq_stop, List.size_toArray, List.length_nil,
      List.foldl_toArray', List.foldl_nil, mul_one, Nat.lt_one_iff]
  have h_empty_fold : shape.foldl (· * ·) 1 = 1 := by
    apply empty_shape_product
    exact Eq.symm h_zero_eq_size
  have h_stride_eq_one : stride = 1 := by
    rw [h_stride]
    apply extract_empty_product
  have h_flatIndexRel_simplified : flatIndexRel < 1 := by
    apply flatIndexRel_bound_rank_zero shape flatIndexRel stride
    · exact Eq.symm h_zero_eq_size
    · exact h_stride
    · exact h_flatIndexRel
  have h_result_eq : result = flatIndexRel := by
    rw [h_rank_zero] at h_helper
    rw [computeHelper_rank_zero] at h_helper
    injection h_helper with h_eq
    exact id (Eq.symm h_eq)
  rw [h_result_eq]
  exact Nat.lt_of_lt_of_eq h_flatIndexRel_simplified (Eq.symm h_empty_fold)

/-- Lemma: For the initial call to computeHelper with i_rev = 0, flatIndexRel = 0 -/
lemma flatIndexRel_is_zero_for_i_rev_zero
    (shape : Array Nat) (rank : Nat)
    (h_rank_eq_size : rank = shape.size)
    (h_dims_pos : ∀ (i : Fin rank), shape[i.val]'(by
        have h1 : i.val < rank := i.isLt
        have h2 : rank = shape.size := h_rank_eq_size
        exact Nat.lt_of_lt_of_eq h1 h2) > 0)
    (indices : Array Nat) (result : Nat)
    (h_compute : computeFlatIndex shape rank h_rank_eq_size h_dims_pos indices = Except.ok result) :
    computeHelper shape rank indices 0 0 1 = Except.ok result := by
  unfold computeFlatIndex at h_compute
  split_ifs at h_compute with h_cond
  · exact h_compute

/-- For rank = 1, extract the result from the recursive call with i_rev = 1 -/
lemma computeHelper_bounds_base_rank_one_fixed'
    (shape : Array Nat) (rank : Nat)
    (h_rank_eq_size : rank = shape.size)
    (h_rank_one : rank = 1)
    (h_dims_pos : ∀ (i : Fin rank),
      shape[i]'(by {
        have h1 : i.val < rank := i.isLt
        have h2 : rank = shape.size := h_rank_eq_size
        exact Nat.lt_of_lt_of_eq h1 h2
      }) > 0)
    (indices : Array Nat) (h_indices_size : indices.size = rank)
    (flatIndexRel : Nat) (stride : Nat)
    (h_stride : stride = (shape.extract rank rank).foldl (· * ·) 1)
    (h_flatIndexRel : flatIndexRel < stride * (shape.extract 0 rank).foldl (· * ·) 1)
    (h_flatIndexRel_is_zero : flatIndexRel = 0)
    (result : Nat)
    (h_helper : computeHelper shape rank indices 0 flatIndexRel stride = Except.ok result) :
    result < shape.foldl (· * ·) 1 := by
  let k_idx := rank - 1
  let index_val := indices[k_idx]!
  let dim_size := shape[k_idx]!
  have h_components := extract_recursive_call_components
    shape rank indices flatIndexRel stride result (h_rank_one ▸ Nat.one_pos) h_helper
  have h_index_lt_dim : index_val < dim_size := h_components.1
  have h_recursive_call := h_components.2
  have h_result_eq : result = flatIndexRel + index_val * stride := by
    rw [h_rank_one] at h_recursive_call
    have h_indices_eq : indices[0]! = index_val := by
      simp only [index_val, k_idx, h_rank_one, Nat.sub_self]
    have h_shape_eq : shape[0]! = dim_size := by
      simp only [dim_size, k_idx, h_rank_one, Nat.sub_self]
    let new_flat_index := flatIndexRel + indices[0]! * stride
    have h_lemma_eval := recursive_call_rank_one shape indices indices[0]! stride flatIndexRel
      new_flat_index
    rw [h_lemma_eval] at h_recursive_call
    injection h_recursive_call with h_result_eq
    rw [←h_result_eq]
    simp only [index_val, k_idx, h_rank_one, Nat.sub_self]
    omega
  rw [h_result_eq]
  have h_rank_gt_zero : rank > 0 := by
    rw [h_rank_one]
    exact Nat.zero_lt_one
  have h_dims_pos_bang : ∀ (k : Fin rank), shape[k]! > 0 := by
    intro k
    have h_k_lt_size : k.val < shape.size := by
      rw [←h_rank_eq_size]
      exact k.isLt
    have := h_dims_pos k
    simp_all
  have h_bound := flatIndexRel_bound_for_i_rev_zero_recursive_call
    shape rank h_rank_gt_zero h_rank_eq_size indices
    flatIndexRel stride h_stride h_flatIndexRel h_dims_pos_bang
    index_val dim_size h_index_lt_dim rfl h_flatIndexRel_is_zero
  have h_k_idx_zero : k_idx = 0 := by simp [k_idx, h_rank_one]
  have h_dim_size_is_shape_0 : dim_size = shape[0]! := by
    simp [dim_size, h_k_idx_zero]
  have h_stride_is_one : stride = 1 := by
    rw [h_stride, h_rank_one]
    apply extract_empty_product
  have h_shape_product_eq : shape.foldl (· * ·) 1 =
      stride * dim_size * (shape.extract 0 (rank - 1)).foldl (· * ·) 1 := by
    rw [h_rank_one]
    have h_extract_empty : (shape.extract 0 (rank - 1)).foldl (· * ·) 1 = 1 := by
      rw [h_rank_one]; apply extract_empty_product
    have h_stride_is_one : stride = 1 := by
      rw [h_stride]; apply extract_empty_product
    simp only [h_stride_is_one, one_mul, Nat.sub_self, Array.extract_empty_of_start_eq_stop,
      List.size_toArray, List.length_nil, List.foldl_toArray', List.foldl_nil, mul_one]
    have singleton : shape.foldl (· * ·) 1 = dim_size := by
      have h_extract_all : shape.extract 0 rank = shape := by
        rw [h_rank_eq_size]
        exact extract_eq_self_of_rank_eq_size shape
      rw [h_rank_one] at h_extract_all
      have h_step : (shape.extract 0 (0 + 1)).foldl (· * ·) 1 =
          shape[0]! * (shape.extract 0 0).foldl (· * ·) 1 := by
        have h_lt : (0 : Nat) < shape.size := by rw [← h_rank_eq_size]; exact h_rank_gt_zero
        exact product_extract_prefix_step shape 0 h_lt
      simp only [Nat.zero_add] at h_step
      rw [h_extract_all] at h_step
      rw [extract_empty_product] at h_step
      rw [Eq.symm h_dim_size_is_shape_0] at h_step
      simpa using h_step
    simp [singleton]
  have h_shape_product : shape.foldl (· * ·) 1 = dim_size := by
    rw [h_shape_product_eq]
    have h_extract_is_empty : (shape.extract 0 (rank - 1)).foldl (· * ·) 1 = 1 := by
      rw [h_rank_one]
      simp only [Nat.sub_self, Array.extract_empty_of_start_eq_stop, List.size_toArray,
        List.length_nil, List.foldl_toArray', List.foldl_nil]
    rw [h_extract_is_empty]
    rw [Nat.mul_one]
    rw [h_dim_size_is_shape_0]
    exact h_stride_is_one ▸ (Nat.one_mul shape[0]!)
  rw [h_rank_eq_size] at h_bound
  simp only [Array.extract_eq_pop, Array.size_pop, k_idx, dim_size, index_val] at h_bound
  simp at h_bound
  rw [h_shape_product]
  subst h_indices_size h_stride h_flatIndexRel_is_zero h_result_eq
  simp_all only [Fin.getElem_fin, gt_iff_lt, le_refl, Nat.sub_eq_zero_of_le, Nat.lt_one_iff,
    pos_of_gt, Fin.getElem!_fin, Array.extract_empty_of_start_eq_stop, List.size_toArray,
    List.length_nil, List.foldl_toArray', List.foldl_nil, one_mul, mul_one, Array.size_extract,
    min_self, tsub_zero, zero_add, true_and, index_val, k_idx, dim_size]

lemma computeHelper_bounds_base_rank_zero
    (shape : Array Nat) (rank : Nat) (h_rank_eq_size : rank = shape.size)
    (h_rank_zero : rank = 0)
    (_h_dims_pos : ∀ (i : Fin rank), shape[i]! > 0)
    (indices : Array Nat) (_h_indices_size : indices.size = rank)
    (flatIndexRel : Nat) (stride : Nat)
    (h_stride : stride = (shape.extract (rank - 0) rank).foldl (· * ·) 1)
    (h_flatIndexRel : flatIndexRel < stride * (shape.extract 0 (rank - 0)).foldl (· * ·) 1)
    (result : Nat)
    (h_helper : computeHelper shape rank indices 0 flatIndexRel stride = Except.ok result)
    : result < shape.foldl (· * ·) 1 := by
  have h_shape_size_zero : shape.size = 0 := by
    rw [← h_rank_eq_size, h_rank_zero]
  have h_empty_fold : shape.foldl (· * ·) 1 = 1 := by
    apply empty_shape_product
    exact h_shape_size_zero
  have h_stride_eq_one : stride = 1 := by
    have h_extract_eq : shape.extract (rank - 0) rank = shape.extract 0 0 := by
        rw [h_rank_zero]
    rw [h_extract_eq] at h_stride
    apply stride_rank_zero shape stride h_stride
  have h_flatIndexRel_simplified : flatIndexRel < 1 := by
    have h_extract_eq : shape.extract (rank - 0) rank = shape.extract 0 0 := by
      rw [h_rank_zero]
    have h_stride_converted : stride = (shape.extract 0 0).foldl (· * ·) 1 := by
      rw [h_stride, h_extract_eq]
    have h_extract_eq2 : shape.extract 0 (rank - 0) = shape.extract 0 0 := by
      rw [Nat.sub_zero, h_rank_zero]
    have h_modified_flatIndexRel : flatIndexRel < stride * (shape.extract 0 0).foldl (· * ·) 1 := by
        have h_foldl_equal : (shape.extract 0 (rank - 0)).foldl (· * ·) 1 =
            (shape.extract 0 0).foldl (· * ·) 1 := by
          congr
        rw [h_foldl_equal] at h_flatIndexRel
        exact h_flatIndexRel
    apply flatIndexRel_bound_rank_zero shape flatIndexRel stride
    · exact h_shape_size_zero
    · exact h_stride_converted
    · exact h_modified_flatIndexRel
  have h_result_eq : result = flatIndexRel := by
    rw [h_rank_zero] at h_helper
    rw [computeHelper_rank_zero shape indices flatIndexRel stride] at h_helper
    injection h_helper with h_eq
    exact id (Eq.symm h_eq)
  rw [h_result_eq]
  exact Nat.lt_of_lt_of_eq h_flatIndexRel_simplified (Eq.symm h_empty_fold)

lemma computeHelper_bounds_base_rank_one_fixed
    (shape : Array Nat) (rank : Nat) (h_rank_eq_size : rank = shape.size)
    (h_rank_one : rank = 1)
    (_h_dims_pos : ∀ (i : Fin rank), shape[i]! > 0)
    (indices : Array Nat) (_h_indices_size : indices.size = rank)
    (flatIndexRel : Nat) (stride : Nat)
    (h_stride : stride = (shape.extract rank rank).foldl (· * ·) 1)
    (_h_flatIndexRel : flatIndexRel < stride * (shape.extract 0 rank).foldl (· * ·) 1)
    (h_flat_is_zero : flatIndexRel = 0)
    (result : Nat)
    (h_helper : computeHelper shape rank indices 0 flatIndexRel stride = Except.ok result)
    : result < shape.foldl (· * ·) 1 := by
  have h_size : shape.size = 1 := by
    rw [←h_rank_eq_size, h_rank_one]
  unfold computeHelper at h_helper
  by_cases h_ge_test : 0 ≥ rank
  case pos =>
    have h_zero_not_ge_one : ¬(0 ≥ 1) := by
      exact Nat.not_le_of_gt Nat.zero_lt_one
    rw [h_rank_one] at h_ge_test
    exact absurd h_ge_test h_zero_not_ge_one
  case neg =>
    let i := rank - 1 - 0
    let index := indices[i]!
    let dimSize := shape[i]!
    simp only [h_ge_test, if_false] at h_helper
    by_cases h_index_ge_local : index ≥ dimSize
    case pos =>
      have h_error_result : (let i_let := rank - 1 - 0;
          let index_let := indices[i_let]!;
          let dimSize_let := shape[i_let]!;
          if index_let ≥ dimSize_let then Except.error (TensorError.indexOutOfBounds indices shape)
          else
            let newFlatIndex := flatIndexRel + index_let * stride;
            let newStride := stride * dimSize_let;
            computeHelper shape rank indices (0 + 1) newFlatIndex newStride) =
            Except.error (TensorError.indexOutOfBounds indices shape) := by
        simp only
        rw [if_pos h_index_ge_local]
      rw [h_error_result] at h_helper
      cases h_helper
    case neg =>
      simp only [i, index, dimSize, h_index_ge_local, if_false] at h_helper
      have h_stride_one : stride = 1 := by
        have h_extract_empty : (shape.extract rank rank).foldl (· * ·) 1 = 1 := by
          apply extract_empty_product
        rw [h_stride]
        exact h_extract_empty
      have h_0_lt_size : 0 < shape.size := by
        rw [h_size]
        exact Nat.zero_lt_one
      have h_result_eq : result = indices[0]! := by
        let newFlatIndex_val := flatIndexRel + index * stride
        let newStride_val := stride * dimSize
        have h_recursive_call_eval :
            computeHelper shape 1 indices 1 newFlatIndex_val newStride_val =
              Except.ok newFlatIndex_val := by
          unfold computeHelper
          simp only [ge_iff_le, le_refl, if_true]
        have h_helper_simp := h_helper
        rw [h_rank_one] at h_helper_simp
        simp only [Nat.sub_self, tsub_zero, zero_add] at h_helper_simp
        unfold computeHelper at h_helper_simp
        rw [if_pos (by rw [← h_rank_one]; )] at h_helper_simp
        rw [Except.ok.injEq] at h_helper_simp
        rw [← h_helper_simp]
        simp only [h_flat_is_zero, h_stride_one, Nat.zero_add, Nat.mul_one]
      rw [h_result_eq]
      have h_final_product_val : shape.foldl (· * ·) 1 = shape[0]! := by
        have h_self_extract : shape = shape.extract 0 rank := by
          rw [h_rank_eq_size]
          exact (extract_eq_self_of_rank_eq_size shape).symm
        rw [h_self_extract]
        rw [← Array.foldl_toList]
        rw [h_rank_one]
        have h_extract_toList_singleton : (shape.extract 0 1).toList = [shape[0]!] := by
          have h_idx_lt_stop : (0 : Nat) < 1 := Nat.zero_lt_one
          have h_stop_le_size : 1 ≤ shape.size := by rw [h_size];
          rw [Array.extract_toList_eq_getElem_bang_cons_extract_toList shape 0 1 h_idx_lt_stop
            h_stop_le_size]
          simp only [Array.extract_empty_of_start_eq_stop, Array.toList_empty]
        rw [h_extract_toList_singleton]
        simp only [List.foldl_cons, List.foldl_nil, Nat.one_mul]
        have h_extract_size : (shape.extract 0 1).size = 1 := by
          rw [Array.size_extract]
          simp only [Nat.sub_zero]
          rw [min_eq_left]
          exact h_0_lt_size
        have h_0_lt_extract_size : 0 < (shape.extract 0 1).size := by
          rw [h_extract_size]
          exact Nat.zero_lt_one
        have h_0_lt_shape_size : 0 < shape.size := by
          rw [h_size]
          exact Nat.zero_lt_one
        have h_extract_elem : (shape.extract 0 1)[0]'h_0_lt_extract_size =
            shape[0]'h_0_lt_shape_size := by
          apply Array.getElem_extract
        have h_extract_elem_get_bang : (shape.extract 0 1)[0]! = shape[0]! := by
          rw [Array.getElem_eq_get_safe h_0_lt_extract_size]
          rw [Array.getElem_eq_get_safe h_0_lt_shape_size]
          exact h_extract_elem
        exact id (Eq.symm h_extract_elem_get_bang)
      have h_index_lt_dim : indices[0]! < shape[0]! := by
        have h_i_eq_0 : i = 0 := by
          simp [i, h_rank_one, Nat.sub_self]
        have h_index_is_indices_0 : index = indices[0]! := by
          simp [index, h_i_eq_0]
        have h_dimSize_is_shape_0 : dimSize = shape[0]! := by
          simp [dimSize, h_i_eq_0]
        rw [← h_index_is_indices_0, ← h_dimSize_is_shape_0]
        exact Nat.lt_of_not_ge h_index_ge_local
      rw [h_final_product_val]
      exact h_index_lt_dim

lemma product_extract_single_element_eq_getElem_bang (shape : Array Nat) (k : Nat)
    (_h_k_lt_size : k < shape.size) (h_kp1_le_size : k + 1 ≤ shape.size) :
    (shape.extract k (k+1)).foldl (· * ·) 1 = shape[k]! := by
  rw [← Array.foldl_toList, ← List.prod_eq_foldl]
  rw [Array.extract_toList_eq_getElem_bang_cons_extract_toList shape k (k+1)
    (Nat.lt_succ_self _) h_kp1_le_size]
  simp only [Array.extract_empty_of_start_eq_stop, Array.toList_empty, List.prod_cons,
    List.prod_nil, mul_one]

end LLM.GPT2
