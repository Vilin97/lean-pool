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
  induction l1 generalizing a b with
  | nil => simp only [nil_append, chain3_cons, Chain3.nil, and_true, and_assoc]
  | cons x l1 IH => simp only [cons_append, chain3_cons, IH, and_assoc]

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

namespace Chain3'

theorem left_of_append {l1 l2 : List α} (h : Chain3' R (l1 ++ l2)) : Chain3' R l1 := by
  induction l1 with
  | nil => simp only [chain3'_nil]
  | cons a l1 ih =>
    cases l1 with
    | nil => simp only [chain3'_singleton]
    | cons b l1 =>
      cases l1 with
      | nil => simp only [chain3'_pair]
      | cons c l1 =>
        rw [cons_append, cons_append, cons_append, chain3'_cons] at h
        rw [chain3'_cons]
        exact ⟨h.1, ih h.2⟩

theorem right_of_append {l1 l2 : List α} (h : Chain3' R (l1 ++ l2)) : Chain3' R l2 := by
  induction l1 generalizing l2 with
  | nil => exact h
  | cons a l1 ih =>
    cases l1 with
    | nil =>
      cases l2 with
      | nil => simp only [chain3'_nil]
      | cons c l2 =>
        cases l2 with
        | nil => simp only [chain3'_singleton]
        | cons d l2 =>
          rw [cons_append, nil_append, chain3'_cons] at h
          exact h.right
    | cons b l1 =>
      cases l1 with
      | nil =>
        cases l2 with
        | nil => simp only [chain3'_nil]
        | cons d l2 =>
          cases l2 with
          | nil => simp only [chain3'_singleton]
          | cons e l2 =>
            rw [cons_append, cons_append, nil_append, chain3'_cons, chain3'_cons] at h
            exact h.right.right
      | cons c l1 =>
        apply ih
        rw [cons_append, cons_append, cons_append, chain3'_cons] at h
        exact h.right

theorem «infix» {l₁ l : List α} (h : Chain3' R l) (h' : l₁ <:+: l) : Chain3' R l₁ := by
  rcases h' with ⟨l₂, l₃, rfl⟩; exact h.left_of_append.right_of_append

theorem suffix {l₁ l : List α} (h : Chain3' R l) (h' : l₁ <:+ l) : Chain3' R l₁ :=
  h.«infix» h'.isInfix

theorem «prefix» {l₁ l : List α} (h : Chain3' R l) (h' : l₁ <+: l) : Chain3' R l₁ :=
  h.«infix» h'.isInfix

theorem drop {l : List α} (h : Chain3' R l) (n : ℕ) : Chain3' R (List.drop n l) :=
  h.suffix (drop_suffix _ _)

theorem dropLast {l : List α} (h : Chain3' R l) : Chain3' R l.dropLast :=
  h.«prefix» l.dropLast_prefix

theorem take {l : List α} (h : Chain3' R l) (n : ℕ) : Chain3' R (List.take n l) :=
  h.«prefix» (take_prefix _ _)

theorem tail {l : List α} (h : Chain3' R l) : Chain3' R l.tail := by
  cases l with
  | nil => simp only [List.tail_nil, chain3'_nil]
  | cons a l =>
    cases l with
    | nil => simp only [List.tail_cons, chain3'_nil]
    | cons b l =>
      cases l with
      | nil => simp only [List.tail_cons, chain3'_singleton]
      | cons c l =>
        rw [chain3'_cons] at h
        exact h.right

end Chain3'

theorem chain3'_mirror [LinearOrder α] {l : List α} :
    Chain3' (Mirror3 R) l.Mirror ↔ Chain3' R l := by
  induction l with
  | nil => simp only [List.Mirror, map_nil, reverse_nil, chain3'_nil]
  | cons a l ih =>
    cases l with
    | nil =>
      simp only [List.Mirror, map_cons, map_nil, reverse_cons, reverse_nil, nil_append,
        chain3'_singleton]
    | cons b l =>
      cases l with
      | nil =>
        rw [List.Mirror]
        simp only [map_cons, map_nil, reverse_cons, reverse_nil, nil_append, cons_append,
          chain3'_pair]
      | cons c l =>
        rw [List.Mirror]
        simp only [map_cons, reverse_cons, append_assoc, cons_append, nil_append,
          chain3'_append_cons3, chain3'_pair, and_true, chain3'_cons]
        simp only [List.Mirror, map_cons, reverse_cons, append_assoc, cons_append, nil_append] at ih
        rw [← ih, Mirror3]
        simp only [OrderDual.ofDual_toDual]
        exact and_comm

end List
