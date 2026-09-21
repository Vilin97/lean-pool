/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Definitions

/-!
# Inversions and the sorting sign

The calculus of the sorting sign (`inversions` and `sortSign` are
defined in `RS/Definitions.lean`): the sign is antisymmetric under
adjacent transpositions of distinct elements, which is the
combinatorial engine of the alternating evaluation of mixed vertex
functionals.
-/

namespace RS

/-- Sorting signs square to one over ℂ. -/
theorem sortSign_sq {α : Type} [LinearOrder α] (l : List α) :
    (sortSign l : ℂ) * (sortSign l : ℂ) = 1 := by
  rw [sortSign]
  push_cast
  rw [← pow_add, ← two_mul, pow_mul]
  norm_num

/-- Increasing embeddings preserve inversion counts. -/
theorem inversions_map_orderEmbedding {α β : Type}
    [LinearOrder α] [LinearOrder β] (e : α ↪o β) (l : List α) :
    inversions (l.map e) = inversions l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons, inversions, ih, List.filter_map,
      List.length_map, Function.comp_def, e.lt_iff_lt]

/-- Increasing embeddings preserve the sorting sign. -/
theorem sortSign_map_orderEmbedding {α β : Type}
    [LinearOrder α] [LinearOrder β] (e : α ↪o β) (l : List α) :
    sortSign (l.map e) = sortSign l := by
  rw [sortSign, inversions_map_orderEmbedding, sortSign]

/-- Sorted lists have no inversions. -/
theorem inversions_eq_zero_of_sorted {α : Type} [LinearOrder α] :
    ∀ (l : List α), List.Pairwise (· ≤ ·) l → inversions l = 0
  | [], _ => rfl
  | a :: l, h => by
    rw [inversions]
    rw [inversions_eq_zero_of_sorted l h.of_cons]
    rw [show l.filter (fun b => b < a) = [] from
      List.filter_eq_nil_iff.mpr (fun b hb => by
        have hab := (List.pairwise_cons.mp h).1 b hb
        simp only [decide_eq_true_eq]
        exact not_lt.mpr hab)]
    rfl

/-- Sorted lists have sorting sign one. -/
theorem sortSign_eq_one_of_sorted {α : Type} [LinearOrder α]
    (l : List α) (h : List.Pairwise (· ≤ ·) l) :
    sortSign l = 1 := by
  rw [sortSign, inversions_eq_zero_of_sorted l h]
  rfl

/-- Inversion counts are invariant under permuting the tail past a
fixed head-filter: permuted lists have equal filter lengths. -/
theorem filter_length_of_perm {α : Type} (p : α → Bool)
    {l₁ l₂ : List α} (h : l₁.Perm l₂) :
    (l₁.filter p).length = (l₂.filter p).length :=
  (h.filter p).length_eq

/-- Swapping two distinct adjacent elements flips the sorting
sign. -/
theorem sortSign_swap_adjacent {α : Type} [LinearOrder α]
    (l₁ l₂ : List α) {a b : α} (hab : a ≠ b) :
    sortSign (l₁ ++ b :: a :: l₂) = -sortSign (l₁ ++ a :: b :: l₂) := by
  induction l₁ with
  | nil =>
    simp only [List.nil_append, sortSign, inversions]
    rcases lt_trichotomy a b with h | h | h
    · rw [show (List.filter (fun x => decide (x < b)) (a :: l₂)).length =
          (List.filter (fun x => decide (x < b)) l₂).length + 1 from by
        simp [h],
        show (List.filter (fun x => decide (x < a)) (b :: l₂)).length =
          (List.filter (fun x => decide (x < a)) l₂).length from by
        simp [not_lt.mpr h.le]]
      ring
    · exact absurd h hab
    · rw [show (List.filter (fun x => decide (x < a)) (b :: l₂)).length =
          (List.filter (fun x => decide (x < a)) l₂).length + 1 from by
        simp [h],
        show (List.filter (fun x => decide (x < b)) (a :: l₂)).length =
          (List.filter (fun x => decide (x < b)) l₂).length from by
        simp [not_lt.mpr h.le]]
      ring
  | cons c l₁ ih =>
    simp only [List.cons_append, sortSign, inversions] at ih ⊢
    have hperm : (l₁ ++ b :: a :: l₂).Perm (l₁ ++ a :: b :: l₂) :=
      List.Perm.append_left l₁ (List.Perm.swap a b l₂)
    rw [filter_length_of_perm _ hperm]
    rw [pow_add, pow_add, ih]
    ring

/-- Moving a two-element block past another two-element block
preserves the sorting sign: four adjacent transpositions, an even
number of sign flips. -/
theorem sortSign_pair_block_swap {α : Type} [LinearOrder α]
    (l₁ l₂ : List α) {p₁ p₂ q₁ q₂ : α}
    (hp₁q₁ : p₁ ≠ q₁) (hp₁q₂ : p₁ ≠ q₂)
    (hp₂q₁ : p₂ ≠ q₁) (hp₂q₂ : p₂ ≠ q₂) :
    sortSign (l₁ ++ q₁ :: q₂ :: p₁ :: p₂ :: l₂) =
      sortSign (l₁ ++ p₁ :: p₂ :: q₁ :: q₂ :: l₂) := by
  have s₁ := sortSign_swap_adjacent (l₁ ++ [p₁]) (q₂ :: l₂)
    (a := p₂) (b := q₁) hp₂q₁
  have s₂ := sortSign_swap_adjacent l₁ (p₂ :: q₂ :: l₂)
    (a := p₁) (b := q₁) hp₁q₁
  have s₃ := sortSign_swap_adjacent (l₁ ++ [q₁, p₁]) l₂
    (a := p₂) (b := q₂) hp₂q₂
  have s₄ := sortSign_swap_adjacent (l₁ ++ [q₁]) (p₂ :: l₂)
    (a := p₁) (b := q₂) hp₁q₂
  simp only [List.append_assoc, List.cons_append, List.nil_append]
    at s₁ s₂ s₃ s₄
  rw [s₄, s₃, s₂, s₁]
  ring

end RS
