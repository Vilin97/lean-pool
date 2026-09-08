/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
import LeanPool.RareDistanceFields.OrderedColors

/-!
# Ordered pair counts under a binary partition

See the project entry module for the exact coordinate restrictions and source roles.
Elementary finite sums used to count distance classes inside and across parity
classes; the final identity converts ordered counts to unordered graph edges.
-/

namespace LeanPool.RareDistanceFields.SplitCounts

noncomputable section

variable {V A B C : Type*} [Fintype V] [Fintype A] [Fintype B]

open Classical in
/-- The number of pairs in a finite Cartesian product carrying the specified color. -/
def count (q : A → B → C) (r : C) : ℕ := ∑ a, ∑ b, if q a b = r then 1 else 0

open Classical in
theorem count_zero (q : A → B → C) (r : C) (h : ∀ a b, q a b ≠ r) : count q r = 0 := by
  simp [count, h]

open Classical in
theorem count_congr {D : Type*} (q : A → B → C) (q' : A → B → D) (r : C) (r' : D)
    (h : ∀ a b, q a b = r ↔ q' a b = r') : count q r = count q' r' := by
  simp only [count, h]

open Classical in
theorem count_symm (q : A → B → C) (r : C) :
    count q r = count (fun b a => q a b) r := by
  exact Finset.sum_comm

open Classical in
theorem count_split (q : V → V → C) (r : C) (p : V → Prop) [DecidablePred p] :
    count q r =
      count (fun a b : {v // p v} => q a.1 b.1) r +
      count (fun a : {v // p v} => fun b : {v // ¬p v} => q a.1 b.1) r +
      count (fun a : {v // ¬p v} => fun b : {v // p v} => q a.1 b.1) r +
      count (fun a b : {v // ¬p v} => q a.1 b.1) r := by
  unfold count
  rw [← Fintype.sum_subtype_add_sum_subtype p]
  simp_rw [← Fintype.sum_subtype_add_sum_subtype p (fun b => if q _ b = r then 1 else 0)]
  simp only [Finset.sum_add_distrib]
  omega

open Classical in
theorem card_split (p : V → Prop) [DecidablePred p] :
    Fintype.card {v // p v} + Fintype.card {v // ¬p v} = Fintype.card V := by
  simpa using Fintype.sum_subtype_add_sum_subtype p (fun _ => (1 : ℕ))

open Classical in
theorem count_eq_twice_edges (q : V → V → C) (hs : ∀ a b, q a b = q b a)
    (r : C) (hdiag : ∀ a, q a a ≠ r) :
    count q r = 2 * (OrderedColors.colorGraph q hs r).edgeFinset.card := by
  rw [← SimpleGraph.sum_degrees_eq_twice_card_edges]
  unfold count
  apply Finset.sum_congr rfl
  intro a ha
  have he : (OrderedColors.colorGraph q hs r).neighborFinset a =
      Finset.univ.filter (fun b => q a b = r) := by
    ext b
    rw [SimpleGraph.mem_neighborFinset]
    simp only [OrderedColors.colorGraph, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact And.right
    · intro h
      refine ⟨?_, h⟩
      intro hab
      exact hdiag a (hab ▸ h)
  rw [← SimpleGraph.card_neighborFinset_eq_degree, he, Finset.card_filter]

end
end LeanPool.RareDistanceFields.SplitCounts
