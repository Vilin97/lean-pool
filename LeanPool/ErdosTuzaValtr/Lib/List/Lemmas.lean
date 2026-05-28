/-
Copyright (c) 2026 Jineon Baek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jineon Baek
-/

import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Order.Basic
import LeanPool.ErdosTuzaValtr.Lib.List.Defs

variable {α : Type _}

section ListIn

def List.in_superset {l : List α} {S T : Finset α} (h : S ⊆ T) : l.In S → l.In T :=
  fun l_in_S a al => h (l_in_S _ al)

def List.subset_in {l1 l2 : List α} {S : Finset α} (h : l1 ⊆ l2) (h_l2 : l2.In S) : l1.In S :=
  fun a ha => h_l2 a (h ha)

@[simp]
theorem List.nil_in {S : Finset α} : [].In S := by rw [List.In] <;> simp

@[simp]
theorem List.cons_in {a : α} {l : List α} {S : Finset α} : (a :: l).In S ↔ a ∈ S ∧ l.In S := by
  simp [List.In]

@[simp]
theorem List.append_in {l1 l2 : List α} {S : Finset α} : (l1 ++ l2).In S ↔ l1.In S ∧ l2.In S :=
  by
  constructor
  · intro h; constructor
    intro a al1; apply h; exact List.mem_append_left l2 al1
    intro a al2; apply h; exact List.mem_append_right l1 al2
  · intro h a al12; cases' h with h1 h2
    simp at al12; cases' al12 with al1 al2
    exact h1 _ al1; exact h2 _ al2

@[simp]
theorem List.reverse_in {l : List α} {S : Finset α} : l.reverse.In S ↔ l.In S := by simp [List.In]

end ListIn

@[simp]
theorem List.reverse_getLast? {l : List α} : l.reverse.getLast? = l.head? := by cases l <;> simp

@[simp]
theorem List.reverse_head? {l : List α} : l.reverse.head? = l.getLast? := by
  convert List.reverse_getLast?.symm; simp

section Mirror

variable [LinearOrder α]

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
theorem List.ofMirrorMirror {l : List αᵒᵈ} : l.ofMirror.Mirror = l :=
  by
  induction' l with a l ih; simp
  rw [List.ofMirror, List.Mirror]; simp
  rw [List.ofMirror, List.Mirror] at ih; simp at ih
  exact ih

@[simp]
theorem Finset.ofMirrorMirror {S : Finset αᵒᵈ} : S.ofMirror.Mirror = S :=
  by
  rw [Finset.ofMirror, Finset.Mirror]
  rw [Finset.image_image]; convert Finset.image_id
  infer_instance

@[simp]
theorem List.Mirror_length {l : List α} : l.Mirror.length = l.length := by rw [List.Mirror]; simp

theorem List.chain'_mirror {l : List α} : List.Chain' (· < ·) l.Mirror ↔ List.Chain' (· < ·) l := by
  simp_rw [List.Mirror, List.chain'_reverse, List.chain'_map, flip, toDual_lt_toDual]

theorem List.Mirror_getLast? {l : List α} : l.Mirror.getLast? = Option.map toDual l.head? := by
  rw [List.Mirror] <;> cases l <;> simp <;> tauto

theorem List.Mirror_head? {l : List α} : l.Mirror.head? = Option.map toDual l.getLast? :=
  by
  rw [List.Mirror, List.reverse_head?]
  -- quick-and-dirty proof
  induction' l with a l ih;
  simp
  simp; cases' l with b l; simp
  simp; simp at ih; exact ih

theorem List.ofMirror_getLast? {l : List αᵒᵈ} : l.ofMirror.getLast? = Option.map ofDual l.head? :=
  by rw [List.ofMirror] <;> cases l <;> simp <;> tauto

theorem List.ofMirror_head? {l : List αᵒᵈ} : l.ofMirror.head? = Option.map ofDual l.getLast? :=
  by
  rw [List.ofMirror, List.reverse_head?]
  -- quick-and-dirty proof
  induction' l with a l ih;
  simp
  simp; cases' l with b l; simp
  simp; simp at ih; exact ih

theorem List.Mirror_mem_getLast? {a : α} {l : List α} :
    toDual a ∈ l.Mirror.getLast? ↔ a ∈ l.head? := by rw [List.Mirror] <;> cases l <;> simp

theorem List.Mirror_mem_head? {a : α} {l : List α} : toDual a ∈ l.Mirror.head? ↔ a ∈ l.getLast? :=
  by
  rw [List.Mirror, List.reverse_head?]
  -- quick-and-dirty proof
  induction' l with a l ih;
  simp
  simp; cases' l with b l; simp
  simp; simp at ih; exact ih

@[simp]
theorem List.Mirror_in {l : List α} {S : Finset α} : l.Mirror.In S.Mirror ↔ l.In S :=
  by
  rw [List.Mirror]; simp; constructor
  · simp [List.In, Finset.Mirror, HasSubset.Subset]
  · simp [List.In, Finset.Mirror]

@[simp]
theorem Finset.memMirror {a : α} {S : Finset α} : toDual a ∈ S.Mirror ↔ a ∈ S := by
  simp [Finset.Mirror]

@[simp]
theorem Finset.Mirror_card {S : Finset α} : S.Mirror.card = S.card :=
  by
  rw [Finset.Mirror]
  apply S.card_image_of_injective
  intro a b; simp

end Mirror

@[simp]
theorem List.dropLast_singleton (a : α) : [a].dropLast = [] := by rw [List.dropLast]

@[simp]
theorem List.getLast?_cons_append_cons (a b : α) (l1 l2 : List α) :
    (a :: (l1 ++ b :: l2)).getLast? = (b :: l2).getLast? := by
  revert a <;> induction' l1 with c l1 ih <;> simp <;> intro <;> exact ih c

def List.takeHead' {a : α} : ∀ {l : List α} (h : a ∈ l.head?), Σ' t, l = a :: t
  | [], h => by simp at h <;> exfalso <;> assumption
  | b :: t, h => ⟨t, by simp at h ⊢ <;> assumption⟩

def List.takeHead : ∀ {l : List α}, l ≠ [] → Σ' (h1 : α) (t : List α), l = h1 :: t
  | [], h => absurd rfl h
  | h1 :: t, _ => ⟨h1, t, rfl⟩

def List.takeHead2 : ∀ {l : List α}, 2 ≤ l.length → Σ' (h1 h2 : α) (t : List α), l = h1 :: h2 :: t
  | [], h => absurd h (Bool.of_decide_false rfl)
  | [a], h => absurd h (Bool.of_decide_false rfl)
  | a :: b :: t, _ => ⟨a, b, t, rfl⟩

def List.takeHead3 :
    ∀ {l : List α}, 3 ≤ l.length → Σ' (h1 h2 h3 : α) (t : List α), l = h1 :: h2 :: h3 :: t
  | [], h => absurd h (Bool.of_decide_false rfl)
  | [a], h => absurd h (Bool.of_decide_false rfl)
  | [a, b], h => absurd h (Bool.of_decide_false rfl)
  | a :: b :: c :: t, _ => ⟨a, b, c, t, rfl⟩

def List.takeLast' {a : α} : ∀ {l : List α} (h : a ∈ l.getLast?), Σ' l', l = l' ++ [a]
  | [], h => by simp at h
  | [a], h => ⟨[], by simp at h ⊢; assumption⟩
  | b :: c :: t, h =>
    let h' : a ∈ (c :: t).getLast? := by
      simp only [Option.mem_def, List.getLast?_cons_cons]; exact h
    let ⟨l'', hl''⟩ := List.takeLast' h'
    ⟨b :: l'', by simp only [cons_append, cons.injEq, true_and]; exact hl''⟩

def List.takeLast : ∀ {l : List α}, l ≠ [] → Σ' (e1 : α) (m : List α), l = m ++ [e1]
  | [], h => absurd rfl h
  | [a], h => ⟨a, [], rfl⟩
  | a :: b :: rest, _ =>
    let h : b :: rest ≠ [] := fun h => List.noConfusion h
    let ⟨e1, m', eq_l'⟩ := List.takeLast h
    ⟨e1, a :: m', congr_arg (List.cons a) eq_l'⟩

def List.takeLast2 : ∀ {l : List α}, 2 ≤ l.length → Σ' (e1 e2 : α) (m : List α), l = m ++ [e1, e2]
  | [], h => absurd h (Bool.of_decide_false rfl)
  | [a], h => absurd h (Bool.of_decide_false rfl)
  | [a, b], h => ⟨a, b, [], rfl⟩
  | a :: b :: c :: t, _ =>
    let h : 2 ≤ (b :: c :: t).length := (2 : ℕ).le_add_left (List.length t)
    let ⟨e1, e2, m', eq_l'⟩ := List.takeLast2 h
    ⟨e1, e2, a :: m', congr_arg (List.cons a) eq_l'⟩

def List.takeLast3 :
    ∀ {l : List α}, 3 ≤ l.length → Σ' (e1 e2 e3 : α) (m : List α), l = m ++ [e1, e2, e3]
  | [], h => absurd h (Bool.of_decide_false rfl)
  | [a], h => absurd h (Bool.of_decide_false rfl)
  | [a, b], h => absurd h (Bool.of_decide_false rfl)
  | [a, b, c], h => ⟨a, b, c, [], rfl⟩
  | a :: b :: c :: d :: t, _ =>
    let h : 3 ≤ (b :: c :: d :: t).length := (3 : ℕ).le_add_left (List.length t)
    let ⟨e1, e2, e3, m', eq_l'⟩ := List.takeLast3 h
    ⟨e1, e2, e3, a :: m', congr_arg (List.cons a) eq_l'⟩
