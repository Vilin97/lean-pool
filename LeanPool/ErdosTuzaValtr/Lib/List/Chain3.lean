/-
Copyright (c) 2026 Jineon Baek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jineon Baek
-/

import LeanPool.ErdosTuzaValtr.Lib.List.Defs

variable {α : Type _} {R : α → α → α → Prop}

namespace List

theorem chain3_split {a b c d : α} {l1 l2 : List α} :
    Chain3 R a b (l1 ++ c :: d :: l2) ↔ Chain3 R a b (l1 ++ [c, d]) ∧ Chain3 R c d l2 := by
  induction' l1 with x l1 IH generalizing a b
  · simp only [nil_append, chain3_cons, Chain3, Chain3.nil, and_true, and_assoc]
  · simp only [cons_append, chain3_cons, IH, and_assoc]

@[simp]
theorem chain3_append_cons3 {a b c d e : α} {l1 l2 : List α} :
    Chain3 R a b (l1 ++ c :: d :: e :: l2) ↔
      Chain3 R a b (l1 ++ [c, d]) ∧ R c d e ∧ Chain3 R d e l2 :=
  by rw [chain3_split, chain3_cons]

@[simp]
theorem chain3'_nil : Chain3' R [] :=
  trivial

@[simp]
theorem chain3'_singleton (a : α) : Chain3' R [a] :=
  trivial

@[simp]
theorem chain3'_pair (a b : α) : Chain3' R [a, b] :=
  Chain3.nil

@[simp]
theorem chain3'_cons {x y z l} : Chain3' R (x :: y :: z :: l) ↔ R x y z ∧ Chain3' R (y :: z :: l) :=
  chain3_cons

theorem chain3'_split {a b : α} :
    ∀ {l1 l2 : List α},
      Chain3' R (l1 ++ a :: b :: l2) ↔ Chain3' R (l1 ++ [a, b]) ∧ Chain3' R (a :: b :: l2)
  | [], l2 => (and_iff_right (chain3'_pair a b)).symm
  | [c], l2 => by simp
  |-- todo
      c ::
      d :: l1,
    l2 => chain3_split

@[simp]
theorem chain3'_append_cons3 {a b c : α} {l1 l2 : List α} :
    Chain3' R (l1 ++ a :: b :: c :: l2) ↔
      Chain3' R (l1 ++ [a, b]) ∧ R a b c ∧ Chain3' R (b :: c :: l2) :=
  by rw [chain3'_split, chain3'_cons]

theorem Chain3'.left_of_append {l1 l2 : List α} (h : Chain3' R (l1 ++ l2)) : Chain3' R l1 :=
  by
  induction' l1 with a l1 ih; simp
  cases' l1 with b l1; simp
  cases' l1 with c l1; simp
  simp at h ⊢; tauto

theorem Chain3'.right_of_append {l1 l2 : List α} (h : Chain3' R (l1 ++ l2)) : Chain3' R l2 :=
  by
  revert l2
  induction' l1 with a l1 ih; intro l2 h'; exact h'
  intro l2 h'
  cases' l1 with b l1
  · cases' l2 with c l2; simp
    cases' l2 with d l2; simp
    simp at h'; exact h'.right
  cases' l1 with c l1
  · cases' l2 with d l2; simp
    cases' l2 with e l2; simp
    simp at h'; exact h'.right.right
  apply ih; simp at h' ⊢; exact h'.right

theorem Chain3'.infix {l₁ l : List α} (h : Chain3' R l) (h' : l₁ <:+: l) : Chain3' R l₁ := by
  rcases h' with ⟨l₂, l₃, rfl⟩; exact h.left_of_append.right_of_append

theorem Chain3'.suffix {l₁ l : List α} (h : Chain3' R l) (h' : l₁ <:+ l) : Chain3' R l₁ :=
  h.infix h'.isInfix

theorem Chain3'.prefix {l₁ l : List α} (h : Chain3' R l) (h' : l₁ <+: l) : Chain3' R l₁ :=
  h.infix h'.isInfix

theorem Chain3'.drop {l : List α} (h : Chain3' R l) (n : ℕ) : Chain3' R (drop n l) :=
  h.suffix (drop_suffix _ _)

theorem Chain3'.dropLast {l : List α} (h : Chain3' R l) : Chain3' R l.dropLast :=
  h.prefix l.dropLast_prefix

theorem Chain3'.take {l : List α} (h : Chain3' R l) (n : ℕ) : Chain3' R (take n l) :=
  h.prefix (take_prefix _ _)

theorem Chain3'.tail {l : List α} (h : Chain3' R l) : Chain3' R l.tail :=
  by
  cases' l with a l; simp
  cases' l with b l; simp
  cases' l with c l; simp
  simp at h ⊢; exact h.right

theorem chain3'_mirror [LinearOrder α] {l : List α} : Chain3' (Mirror3 R) l.Mirror ↔ Chain3' R l :=
  by
  induction' l with a l ih; simp only [List.Mirror, map_nil, reverse_nil, chain3'_nil]
  cases' l with b l; simp only [List.Mirror, map_cons, map_nil, reverse_cons, reverse_nil,
    nil_append, chain3'_singleton]
  cases' l with c l
  rw [List.Mirror]; simp
  rw [List.Mirror]; simp
  simp [List.Mirror] at ih; rw [← ih]
  rw [Mirror3]; simp; exact and_comm

end List
