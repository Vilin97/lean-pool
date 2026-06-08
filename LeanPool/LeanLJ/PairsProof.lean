/-
Copyright (c) 2026 Colin Jones. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Jones
-/
import Mathlib.Algebra.BigOperators.Intervals
import LeanPool.LeanLJ.Function

/-!
# Counting unordered index pairs

This file proves that the list of unordered index pairs `LeanLJ.pairs n` enumerated
for `n` atoms has length `n * (n - 1) / 2`, i.e. `n` choose `2`.
-/

open List
open scoped BigOperators

namespace LeanLJ

lemma list_sum_map_range (n : Nat) (f : Nat → Nat) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [List.range_succ, List.map_append, List.sum_append]
      simp only [List.map, List.sum_cons, List.sum_nil]
      rw [ih, Finset.sum_range_succ]
      rfl

lemma list_sum_range_eq_finset (n : Nat) :
    (List.range n).sum = ∑ i ∈ Finset.range n, i := by
  rw [← list_sum_map_range n (fun i => i)]
  rw [@map_id']


theorem pairs_length_eq (n : Nat) :
    (pairs n).length = n * (n - 1) / 2 := by
  have h₀ :
    (pairs n).length =
      ((List.range n).map (fun i =>
          (List.range' (i + 1) (n - (i + 1))).length)).sum := by
    simp [pairs, List.length_flatMap, List.length_map]
  have h₁ :
      ((List.range n).map (fun i =>
          (List.range' (i + 1) (n - (i + 1))).length)).sum
        =
      ((List.range n).map (fun i => n - 1 - i)).sum := by
    have h_list :
        (List.range n).map
          (fun i =>
            (List.map (fun j => (i, j))
                      (List.range' (i + 1) (n - (i + 1)))).length)
          =
        (List.range n).map (fun i => n - 1 - i) := by
      apply List.map_congr_left
      intro i _
      simp [List.length_map, List.length_range',
            Nat.sub_sub, add_comm]
    simpa using congrArg List.sum h_list
  have h₂ :
      ((List.range n).map (fun i => n - 1 - i)).sum
        = (List.range n).sum := by
    have h_left :
        ((List.range n).map (fun i => n - 1 - i)).sum
          = ∑ i ∈ Finset.range n, (n - 1 - i) := by
      exact list_sum_map_range n (fun i => n - 1 - i)
    have h_right :
        (List.range n).sum = ∑ i ∈ Finset.range n, i := by
      exact list_sum_range_eq_finset n
    have h_reflect :
        (∑ i ∈ Finset.range n, (n - 1 - i))
          = ∑ i ∈ Finset.range n, i := by
      exact Finset.sum_range_reflect (fun i : Nat => i) n
    rw [h_left, h_reflect, ← h_right]
  have h_chain :
      (pairs n).length = (List.range n).sum := by
    rw [h₀, h₁, h₂]
  have h_sum :
      (List.range n).sum = n * (n - 1) / 2 := by
    rw [list_sum_range_eq_finset n, Finset.sum_range_id]
  rw [h_chain, h_sum]

end LeanLJ
