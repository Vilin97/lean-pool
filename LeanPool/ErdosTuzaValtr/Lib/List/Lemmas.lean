/-
Copyright (c) 2026 Jineon Baek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jineon Baek
-/

import Mathlib.Data.List.Basic
import Mathlib.Data.List.Chain
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Order.Basic
import LeanPool.ErdosTuzaValtr.Lib.List.Defs

/-!
# LeanPool.ErdosTuzaValtr.Lib.List.Lemmas

Imported Lean Pool material for `LeanPool.ErdosTuzaValtr.Lib.List.Lemmas`.
-/

variable {α : Type _}

section ListIn

theorem List.in_superset {l : List α} {S T : Finset α} (h : S ⊆ T) : l.In S → l.In T :=
  fun l_in_S _ al => h (l_in_S _ al)

theorem List.subset_in {l1 l2 : List α} {S : Finset α} (h : l1 ⊆ l2) (h_l2 : l2.In S) : l1.In S :=
  fun a ha => h_l2 a (h ha)

@[simp]
theorem List.nil_in {S : Finset α} : [].In S := by simp only [List.In, not_mem_nil, false_implies,
  implies_true]

@[simp]
theorem List.cons_in {a : α} {l : List α} {S : Finset α} : (a :: l).In S ↔ a ∈ S ∧ l.In S := by
  simp [List.In]

@[simp]
theorem List.append_in {l1 l2 : List α} {S : Finset α} : (l1 ++ l2).In S ↔ l1.In S ∧ l2.In S := by
  constructor
  · intro h
    refine ⟨fun a al1 => ?_, fun a al2 => ?_⟩
    · exact h a (List.mem_append_left l2 al1)
    · exact h a (List.mem_append_right l1 al2)
  · rintro ⟨h1, h2⟩ a al12
    rw [List.mem_append] at al12
    rcases al12 with al1 | al2
    · exact h1 a al1
    · exact h2 a al2

@[simp]
theorem List.reverse_in {l : List α} {S : Finset α} : l.reverse.In S ↔ l.In S := by simp [List.In]

end ListIn

theorem List.reverse_getLast {l : List α} : l.reverse.getLast? = l.head? := by cases l <;> simp

theorem List.reverse_head {l : List α} : l.reverse.head? = l.getLast? := by
  convert List.reverse_getLast.symm; simp

section Mirror

open OrderDual

@[simp]
theorem List.Mirror_nil : ([] : List α).Mirror = [] :=
  rfl

@[simp]
theorem List.Mirror_singleton {a : α} : [a].Mirror = [toDual a] :=
  rfl

@[simp]
theorem List.Mirror_cons {a : α} {l : List α} : (a :: l).Mirror = l.Mirror ++ [toDual a] := by
  simp [List.Mirror]

@[simp]
theorem List.Mirror_append {l1 l2 : List α} : (l1 ++ l2).Mirror = l2.Mirror ++ l1.Mirror := by
  simp [List.Mirror]

@[simp]
theorem List.ofMirror_nil : ([] : List αᵒᵈ).ofMirror = [] :=
  rfl

@[simp]
theorem List.ofMirrorMirror {l : List αᵒᵈ} : l.ofMirror.Mirror = l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.ofMirror, List.Mirror] at ih ⊢
    simp only [map_reverse, map_map, reverse_reverse, map_cons,
      OrderDual.toDual_ofDual] at ih ⊢
    rw [ih]

@[simp]
theorem Finset.ofMirrorMirror [LinearOrder α] {S : Finset αᵒᵈ} : S.ofMirror.Mirror = S :=
  by
  rw [Finset.ofMirror, Finset.Mirror]
  rw [Finset.image_image]
  simp only [Function.comp_def, OrderDual.toDual_ofDual, Finset.image_id']

@[simp]
theorem List.Mirror_length {l : List α} : l.Mirror.length = l.length := by rw [List.Mirror]; simp

theorem List.chain'_mirror [LinearOrder α] {l : List α} :
    List.IsChain (· < ·) l.Mirror ↔ List.IsChain (· < ·) l := by
  simp_rw [List.Mirror, List.isChain_reverse, List.isChain_map, toDual_lt_toDual]

theorem List.Mirror_getLast {l : List α} : l.Mirror.getLast? = Option.map toDual l.head? := by
  rw [List.Mirror, List.reverse_getLast, List.head?_map]

theorem List.Mirror_head {l : List α} : l.Mirror.head? = Option.map toDual l.getLast? := by
  rw [List.Mirror, List.reverse_head, List.getLast?_map]

theorem List.ofMirror_getLast {l : List αᵒᵈ} :
    l.ofMirror.getLast? = Option.map ofDual l.head? := by
  rw [List.ofMirror, List.reverse_getLast, List.head?_map]

theorem List.ofMirror_head {l : List αᵒᵈ} :
    l.ofMirror.head? = Option.map ofDual l.getLast? := by
  rw [List.ofMirror, List.reverse_head, List.getLast?_map]

theorem List.Mirror_mem_getLast {a : α} {l : List α} :
    toDual a ∈ l.Mirror.getLast? ↔ a ∈ l.head? := by
  rw [List.Mirror_getLast, Option.mem_map_of_injective toDual.injective]

theorem List.Mirror_mem_head {a : α} {l : List α} :
    toDual a ∈ l.Mirror.head? ↔ a ∈ l.getLast? := by
  rw [List.Mirror_head, Option.mem_map_of_injective toDual.injective]

@[simp]
theorem List.Mirror_in [LinearOrder α] {l : List α} {S : Finset α} :
    l.Mirror.In S.Mirror ↔ l.In S := by
  rw [List.Mirror]; simp; constructor
  · simp [List.In, Finset.Mirror]
  · simp [List.In, Finset.Mirror]

@[simp]
theorem Finset.memMirror [LinearOrder α] {a : α} {S : Finset α} : toDual a ∈ S.Mirror ↔ a ∈ S := by
  simp [Finset.Mirror]

@[simp]
theorem Finset.Mirror_card [LinearOrder α] {S : Finset α} : S.Mirror.card = S.card :=
  by
  rw [Finset.Mirror]
  apply S.card_image_of_injective
  intro a b; simp

end Mirror

@[simp]
theorem List.getLast?_cons_append_cons (a b : α) (l1 l2 : List α) :
    (a :: (l1 ++ b :: l2)).getLast? = (b :: l2).getLast? := by
  induction l1 generalizing a with
  | nil => simp only [nil_append, getLast?_cons_cons]
  | cons c l1 ih =>
    rw [cons_append, getLast?_cons_cons]
    exact ih c

/-- Split off the head of a list given a witness that `a` is its head. -/
def List.takeHead' {a : α} : ∀ {l : List α} (_ : a ∈ l.head?), Σ' t, l = a :: t
  | [], h => absurd h (Option.not_mem_none a)
  | b :: t, h => ⟨t, by rw [List.head?_cons, Option.mem_some_iff] at h; rw [h]⟩

/-- Split a nonempty list into its head and tail. -/
def List.takeHead : ∀ {l : List α}, l ≠ [] → Σ' (h1 : α) (t : List α), l = h1 :: t
  | [], h => absurd rfl h
  | h1 :: t, _ => ⟨h1, t, rfl⟩

/-- Split a list of length at least 2 into its first two elements and the rest. -/
def List.takeHead2 : ∀ {l : List α}, 2 ≤ l.length → Σ' (h1 h2 : α) (t : List α), l = h1 :: h2 :: t
  | [], h => absurd h (Bool.of_decide_false rfl)
  | [_], h => absurd h (Bool.of_decide_false rfl)
  | a :: b :: t, _ => ⟨a, b, t, rfl⟩

/-- Split a list of length at least 3 into its first three elements and the rest. -/
def List.takeHead3 :
    ∀ {l : List α}, 3 ≤ l.length → Σ' (h1 h2 h3 : α) (t : List α), l = h1 :: h2 :: h3 :: t
  | [], h => absurd h (Bool.of_decide_false rfl)
  | [_], h => absurd h (Bool.of_decide_false rfl)
  | [_, _], h => absurd h (Bool.of_decide_false rfl)
  | a :: b :: c :: t, _ => ⟨a, b, c, t, rfl⟩

/-- Split off the last element of a list given a witness that `a` is its last element. -/
def List.takeLast' {a : α} : ∀ {l : List α} (_ : a ∈ l.getLast?), Σ' l', l = l' ++ [a]
  | [], h => absurd h (Option.not_mem_none a)
  | [b], h => ⟨[], by
      rw [List.getLast?_singleton, Option.mem_some_iff] at h; rw [h, nil_append]⟩
  | b :: c :: t, h =>
    let h' : a ∈ (c :: t).getLast? := by
      rw [List.getLast?_cons_cons] at h; exact h
    let ⟨l'', hl''⟩ := List.takeLast' h'
    ⟨b :: l'', by simp only [cons_append, cons.injEq, true_and]; exact hl''⟩

/-- Split a nonempty list into its last element and the preceding prefix. -/
def List.takeLast : ∀ {l : List α}, l ≠ [] → Σ' (e1 : α) (m : List α), l = m ++ [e1]
  | [], h => absurd rfl h
  | [a], _ => ⟨a, [], rfl⟩
  | a :: b :: rest, _ =>
    let h : b :: rest ≠ [] := List.cons_ne_nil b rest
    let ⟨e1, m', eq_l'⟩ := List.takeLast h
    ⟨e1, a :: m', congr_arg (List.cons a) eq_l'⟩

/-- Split a list of length at least 2 into its last two elements and the preceding prefix. -/
def List.takeLast2 : ∀ {l : List α}, 2 ≤ l.length → Σ' (e1 e2 : α) (m : List α), l = m ++ [e1, e2]
  | [], h => absurd h (Bool.of_decide_false rfl)
  | [_], h => absurd h (Bool.of_decide_false rfl)
  | [a, b], _ => ⟨a, b, [], rfl⟩
  | a :: b :: c :: t, _ =>
    let h : 2 ≤ (b :: c :: t).length := (2 : ℕ).le_add_left (List.length t)
    let ⟨e1, e2, m', eq_l'⟩ := List.takeLast2 h
    ⟨e1, e2, a :: m', congr_arg (List.cons a) eq_l'⟩

/-- Split a list of length at least 3 into its last three elements and the preceding prefix. -/
def List.takeLast3 :
    ∀ {l : List α}, 3 ≤ l.length → Σ' (e1 e2 e3 : α) (m : List α), l = m ++ [e1, e2, e3]
  | [], h => absurd h (Bool.of_decide_false rfl)
  | [_], h => absurd h (Bool.of_decide_false rfl)
  | [_, _], h => absurd h (Bool.of_decide_false rfl)
  | [a, b, c], _ => ⟨a, b, c, [], rfl⟩
  | a :: b :: c :: d :: t, _ =>
    let h : 3 ≤ (b :: c :: d :: t).length := (3 : ℕ).le_add_left (List.length t)
    let ⟨e1, e2, e3, m', eq_l'⟩ := List.takeLast3 h
    ⟨e1, e2, e3, a :: m', congr_arg (List.cons a) eq_l'⟩
