/-
Copyright (c) 2026 Arthur F. Ramos, David Barros Hulak, Ruy J.G.B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/
module

public import LeanPool.MarshallHall.MarshallHall.PartialAction
public import Mathlib.GroupTheory.FreeGroup.Reduce


/-!
## Finite word states

When a word is read by a left action, its tail is applied first.  The finite
state set therefore records suffix products.  This is the same finite core
that appears in the usual folded covering-graph proof, but expressed directly
in the free group.
-/

@[expose] public section

open Function

noncomputable section

namespace MarshallHall

universe u

variable {α : Type u}
variable [DecidableEq α]



/-- The free-group element represented by a letter, with `true` denoting the positive sign. -/
def signedLetter (x : α × Bool) : FreeGroup α :=
  if x.2 then FreeGroup.of x.1 else (FreeGroup.of x.1)⁻¹

/-- The product in the free group represented by a list of signed letters. -/
def wordValue : List (α × Bool) → FreeGroup α
  | [] => 1
  | x :: w => signedLetter x * wordValue w

/-- The successive states obtained by evaluating the word from its rightmost letter. -/
def actionStates : List (α × Bool) → List (FreeGroup α)
  | [] => [1]
  | x :: w => actionStates w ++ [signedLetter x * wordValue w]

/-- The finite set of action states collected from the word and all of its tails. -/
def allActionStates : List (α × Bool) → Finset (FreeGroup α)
  | [] => (actionStates []).toFinset
  | x :: w => allActionStates w ∪ (actionStates (x :: w)).toFinset

omit [DecidableEq α] in
@[simp]
theorem wordValue_nil : wordValue ([] : List (α × Bool)) = 1 := rfl

omit [DecidableEq α] in
@[simp]
theorem wordValue_cons (x : α × Bool) (w : List (α × Bool)) :
    wordValue (x :: w) = signedLetter x * wordValue w := rfl

omit [DecidableEq α] in
@[simp]
theorem actionStates_nil : actionStates ([] : List (α × Bool)) = [1] := rfl

omit [DecidableEq α] in
@[simp]
theorem actionStates_cons (x : α × Bool) (w : List (α × Bool)) :
    actionStates (x :: w) = actionStates w ++ [signedLetter x * wordValue w] := rfl

omit [DecidableEq α] in
@[simp]
theorem wordValue_eq_freeGroup_mk (w : List (α × Bool)) :
    wordValue w = FreeGroup.mk w := by
  induction w with
  | nil => simp [wordValue, FreeGroup.one_eq_mk]
  | cons x w ih =>
      calc
        wordValue (x :: w) = signedLetter x * wordValue w := rfl
        _ = FreeGroup.mk [x] * FreeGroup.mk w := by
          rw [ih]
          congr 1
          cases x with
          | mk a b =>
              cases b <;> simp [signedLetter, FreeGroup.of, FreeGroup.invRev]
        _ = FreeGroup.mk ([x] ++ w) := FreeGroup.mul_mk
        _ = FreeGroup.mk (x :: w) := rfl

omit [DecidableEq α] in
theorem wordValue_mem_actionStates (w : List (α × Bool)) :
    wordValue w ∈ actionStates w := by
  induction w with
  | nil => simp [actionStates, FreeGroup.one_eq_mk]
  | cons x w ih =>
      simp only [actionStates_cons, List.mem_append, List.mem_singleton]
      exact Or.inr rfl

omit [DecidableEq α] in
theorem one_mem_actionStates (w : List (α × Bool)) :
    (1 : FreeGroup α) ∈ actionStates w := by
  induction w with
  | nil => simp [actionStates]
  | cons x w ih =>
      simp only [actionStates_cons, List.mem_append, List.mem_singleton]
      exact Or.inl ih

theorem actionStates_subset_allActionStates (w : List (α × Bool)) :
    ∀ x ∈ actionStates w, x ∈ allActionStates w := by
  induction w with
  | nil =>
      intro x hx
      simpa [allActionStates] using hx
  | cons y w ih =>
      intro x hx
      simp only [actionStates_cons, List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | hx
      · exact Finset.mem_union_left _ (ih x hx)
      · exact Finset.mem_union_right _ (List.mem_toFinset.mpr (by
          simp only [actionStates_cons, List.mem_append, List.mem_singleton]
          exact Or.inr hx))

theorem one_mem_allActionStates (w : List (α × Bool)) :
    (1 : FreeGroup α) ∈ allActionStates w := by
  exact actionStates_subset_allActionStates w 1 (one_mem_actionStates w)

theorem allActionStates_tail_mem (w u : List (α × Bool))
    (hu : u ∈ List.tails w) :
    ∀ x ∈ actionStates u, x ∈ allActionStates w := by
  induction w with
  | nil =>
      simp only [List.tails, List.mem_cons, List.not_mem_nil, or_false] at hu
      subst u
      exact actionStates_subset_allActionStates []
  | cons y w ih =>
      simp only [List.tails, List.mem_cons] at hu
      rcases hu with rfl | hu
      · exact actionStates_subset_allActionStates (y :: w)
      · exact fun x hx => by
          exact Finset.mem_union_left _ (ih hu x hx)

/-!
The recursive version above is intentionally kept local to the finite-core
construction.  The following finite union is the set of all suffix states of
the finitely many words under consideration.
-/

/-- The finite core containing action states of the subgroup generators and the separating word. -/
def corePoints [DecidableEq (FreeGroup α)] (S : Finset (FreeGroup α)) (g : FreeGroup α) :
    Finset (FreeGroup α) :=
  S.biUnion (fun s => (allActionStates s.toWord)) ∪ allActionStates g.toWord

theorem mem_corePoints_of_generator [DecidableEq (FreeGroup α)]
    {S : Finset (FreeGroup α)} {g s : FreeGroup α}
    (hs : s ∈ S) (x : FreeGroup α) (hx : x ∈ allActionStates s.toWord) :
    x ∈ corePoints S g := by
  exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨s, hs, hx⟩)

theorem mem_corePoints_of_separating [DecidableEq (FreeGroup α)]
    {S : Finset (FreeGroup α)} {g x : FreeGroup α}
    (hx : x ∈ allActionStates g.toWord) : x ∈ corePoints S g := by
  exact Finset.mem_union_right _ hx

theorem mem_corePoints_of_generator_suffix [DecidableEq (FreeGroup α)]
    {S : Finset (FreeGroup α)} {g s : FreeGroup α} {u : List (α × Bool)}
    (hs : s ∈ S) (hu : u ∈ List.tails s.toWord)
    {x : FreeGroup α} (hx : x ∈ actionStates u) : x ∈ corePoints S g := by
  exact mem_corePoints_of_generator hs x
    (allActionStates_tail_mem s.toWord u hu x hx)

theorem mem_corePoints_of_separating_suffix [DecidableEq (FreeGroup α)]
    {S : Finset (FreeGroup α)} {g : FreeGroup α} {u : List (α × Bool)}
    (hu : u ∈ List.tails g.toWord) {x : FreeGroup α}
    (hx : x ∈ actionStates u) : x ∈ corePoints S g := by
  exact mem_corePoints_of_separating
    (allActionStates_tail_mem g.toWord u hu x hx)

omit [DecidableEq α] in
theorem exists_wordValue_of_mem_actionStates (u : List (α × Bool))
    {x : FreeGroup α} (hx : x ∈ actionStates u) :
    ∃ v ∈ List.tails u, x = wordValue v := by
  induction u with
  | nil =>
      refine ⟨[], ?_, ?_⟩
      · simp [List.tails]
      · simpa [actionStates, wordValue] using hx
  | cons y u ih =>
      simp only [actionStates_cons, List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | hx
      · obtain ⟨v, hv, hvx⟩ := ih hx
        refine ⟨v, ?_, hvx⟩
        simp only [List.tails, List.mem_cons]
        exact Or.inr hv
      · refine ⟨y :: u, ?_, ?_⟩
        · simp [List.tails]
        · simpa [wordValue] using hx

theorem exists_wordValue_of_mem_allActionStates (u : List (α × Bool))
    {x : FreeGroup α} (hx : x ∈ allActionStates u) :
    ∃ v ∈ List.tails u, x = wordValue v := by
  induction u with
  | nil =>
      refine ⟨[], ?_, ?_⟩
      · simp [List.tails]
      · simpa [allActionStates, actionStates, wordValue] using hx
  | cons y u ih =>
      simp only [allActionStates, Finset.mem_union] at hx
      rcases hx with hx | hx
      · obtain ⟨v, hv, hvx⟩ := ih hx
        refine ⟨v, ?_, hvx⟩
        simp only [List.tails, List.mem_cons]
        exact Or.inr hv
      · obtain ⟨v, hv, hvx⟩ :=
          exists_wordValue_of_mem_actionStates (y :: u) (List.mem_toFinset.mp hx)
        exact ⟨v, hv, hvx⟩

end MarshallHall
