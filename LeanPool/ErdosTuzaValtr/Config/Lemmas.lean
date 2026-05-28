/-
Copyright (c) 2026 Jineon Baek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jineon Baek
-/

import Mathlib.Algebra.Algebra.Defs
import Mathlib.Data.List.Sort
import Mathlib.Tactic.Linarith
import LeanPool.ErdosTuzaValtr.Config.Defs


variable {α : Type _} [LinearOrder α] {C : Config α}

namespace Config

namespace Cap

@[simp]
protected theorem nil : C.Cap [] := by rw [Config.Cap]; tauto

@[simp]
protected theorem singleton (a : α) : C.Cap [a] := by rw [Config.Cap]; simp

@[simp]
protected theorem pair {a b : α} : C.Cap [a, b] ↔ a < b := by rw [Config.Cap]; simp

@[simp]
protected theorem cons3 {a b c : α} {l : List α} :
    C.Cap (a::b::c::l) ↔ a < b ∧ C.Cap3 a b c ∧ C.Cap (b::c::l) := by
  repeat' rw [Config.Cap]; simp
  tauto

@[simp]
protected theorem append_cons3 {a b c : α} {l1 l2 : List α} :
    C.Cap (l1 ++ a::b::c::l2) ↔ C.Cap (l1 ++ [a, b]) ∧ C.Cap3 a b c ∧ C.Cap (b::c::l2) :=
  by
  induction' l1 with d l1 l1_ih
  · simp [Config.Cap]; tauto
  cases' l1 with e l1
  · simp [Config.Cap]; tauto
  cases' l1 with f l1
  · simp [Config.Cap]; tauto
  simp; simp at l1_ih; rw [l1_ih]; tauto

protected theorem dropLast {l : List α} (h : C.Cap l) : C.Cap l.dropLast := by
  induction' l with a l
  · simp [Config.Cap]
  cases' l with b l
  · simp [Config.Cap]
  cases' l with c l
  · simp [Config.Cap, List.dropLast] at *
  cases' l with d l
  · simp [Config.Cap, List.dropLast] at *; tauto
  simp [List.dropLast] at *; tauto

protected theorem tail {l : List α} (h : C.Cap l) : C.Cap l.tail := by
  induction' l with a l
  · simp [Config.Cap]
  cases' l with b l
  · simp [Config.Cap]
  cases' l with c l
  · simp [Config.Cap] at *
  cases' l with d l
  · simp [Config.Cap] at *; tauto
  simp [List.dropLast] at *; tauto

end Cap

namespace NCap

protected theorem dropLast {n : ℕ} {l : List α} (h : C.NCap (n + 1) l) : C.NCap n l.dropLast :=
  by
  cases' l with a l
  · simp [Config.NCap, Config.Cap] at h
  simp [Config.NCap] at *; cases' h with hc hl
  exact ⟨hc.dropLast, hl⟩

protected theorem tail {n : ℕ} {l : List α} (h : C.NCap (n + 1) l) : C.NCap n l.tail :=
  by
  cases' l with a l
  · simp [Config.NCap, Config.Cap] at h
  simp [Config.NCap] at *; cases' h with hc hl
  constructor; exact hc.tail; assumption

end NCap

namespace Cup

@[simp]
protected theorem nil : C.Cup [] := by rw [Config.Cup]; tauto

@[simp]
protected theorem singleton (a : α) : C.Cup [a] := by rw [Config.Cup]; simp

@[simp]
protected theorem pair {a b : α} : C.Cup [a, b] ↔ a < b := by rw [Config.Cup]; simp

@[simp]
protected theorem cons3 {a b c : α} {l : List α} :
    C.Cup (a::b::c::l) ↔ a < b ∧ C.Cup3 a b c ∧ C.Cup (b::c::l) := by
  repeat' rw [Config.Cup]; simp
  tauto

@[simp]
protected theorem append_cons3 {a b c : α} {l1 l2 : List α} :
    C.Cup (l1 ++ a::b::c::l2) ↔ C.Cup (l1 ++ [a, b]) ∧ C.Cup3 a b c ∧ C.Cup (b::c::l2) :=
  by
  induction' l1 with d l1 l1_ih
  · simp [Config.Cup]; tauto
  cases' l1 with e l1
  · simp [Config.Cup]; tauto
  cases' l1 with f l1
  · simp [Config.Cup]; tauto
  simp; simp at l1_ih; rw [l1_ih]; tauto

protected theorem dropLast {l : List α} (h : C.Cup l) : C.Cup l.dropLast := by
  induction' l with a l
  · simp
  cases' l with b l
  · simp
  cases' l with c l
  · simp
  cases' l with d l
  · simp [Config.Cap, List.dropLast] at *; tauto
  simp [List.dropLast] at *; tauto

protected theorem take {l : List α} (h : C.Cup l) (n : ℕ) : C.Cup (l.take n) :=
  ⟨h.left.take n, h.right.take n⟩

protected theorem drop {l : List α} (h : C.Cup l) (n : ℕ) : C.Cup (l.drop n) :=
  ⟨h.left.drop n, h.right.drop n⟩

protected theorem tail {l : List α} (h : C.Cup l) : C.Cup l.tail :=
  ⟨h.left.tail, h.right.tail⟩

theorem head?_lt_getLast? {l : List α} (l_cup : C.Cup l) (p q : α) (hl : 2 ≤ l.length)
    (hp : p ∈ l.head?) (hq : q ∈ l.getLast?) : p < q :=
  by
  cases' l with p l
  · simp at hp
  simp at hp; subst hp
  have l_nnil : l ≠ [] := by intro h; subst h; simp at hl
  rcases List.takeLast l_nnil with ⟨q, l', eq_l⟩
  rw [eq_l] at hq; simp at hq; subst hq
  rw [Config.Cup, eq_l] at l_cup
  cases' l_cup with l_sorted _
  rw [List.chain'_iff_pairwise] at l_sorted; simp at l_sorted
  have h' := l_sorted.left q; tauto

end Cup

namespace NCup

@[simp]
protected theorem nil : C.NCup 0 [] := by rw [Config.NCup, Config.Cup]; tauto

@[simp]
protected theorem singleton (a : α) : C.NCup 1 [a] := by rw [Config.NCup, Config.Cup]; simp

@[simp]
protected theorem pair {a b : α} : C.NCup 2 [a, b] ↔ a < b := by
  rw [Config.NCup, Config.Cup]; simp

@[simp]
protected theorem cons3 {n : ℕ} {a b c : α} {l : List α} :
    C.NCup (n + 1) (a::b::c::l) ↔ a < b ∧ C.Cup3 a b c ∧ C.NCup n (b::c::l) := by
  repeat' rw [Config.NCup, Config.Cup]; simp
  tauto

protected theorem dropLast {n : ℕ} {l : List α} (h : C.NCup (n + 1) l) : C.NCup n l.dropLast :=
  by
  cases' l with a l
  · simp [Config.NCup, Config.Cup] at h
  simp [Config.NCup] at *; cases' h with hc hl
  constructor; exact hc.dropLast; assumption

protected theorem dropLast_append_last {n : ℕ} {l : List α} (h : C.NCup (n + 1) l) :
    ∃ (l' : List α) (a : α), l = l' ++ [a] ∧ C.NCup n l' :=
  by
  cases' l with a l
  · simp [Config.NCup, Config.Cup] at h
  have nnil : (a::l) ≠ [] := by simp
  use(a::l).dropLast, (a::l).getLast nnil; constructor
  apply symm; exact List.dropLast_append_getLast nnil
  exact h.dropLast

protected theorem tail {n : ℕ} {l : List α} (h : C.NCup (n + 1) l) : C.NCup n l.tail :=
  by
  cases' l with a l
  · simp [Config.NCup, Config.Cup] at h
  simp at *; cases' h with hc hl
  constructor; exact hc.tail; simp at hl; assumption

protected theorem cons_head_tail {n : ℕ} {l : List α} (h : C.NCup (n + 1) l) :
    ∃ (a : α) (l' : List α), (l = a::l') ∧ C.NCup n l' :=
  by
  cases' l with a l
  · simp [Config.NCup, Config.Cup] at h
  simp [Config.NCup] at *; cases' h with hc hl
  use a, l; have hc' := hc.tail; simp at hc'; tauto

protected theorem take_head_last {n : ℕ} {l : List α} (h : C.NCup (n + 2) l) :
    ∃ (a : α) (l' : List α) (b : α), l = (a::l') ++ [b] ∧ C.NCup n l' :=
  by
  rcases h.cons_head_tail with ⟨a, l', eq_l, cup_l'⟩
  rcases cup_l'.dropLast_append_last with ⟨l'', b, eq_l', cup_l''⟩
  use a, l'', b; constructor
  rw [eq_l, eq_l']; simp; assumption

theorem take_left_with_head {n : ℕ} {l : List α} (h : C.NCup n l) (m : ℕ) (p : α) :
    1 ≤ m → m ≤ n → p ∈ l.head? → ∃ l' : List α, l' ⊆ l ∧ C.NCup m l' ∧ p ∈ l'.head? :=
  by
  intro one_le_m m_le_n l_last
  use l.take m; refine' ⟨_, _, _⟩
  · exact List.take_subset m l
  · refine' ⟨h.left.take m, _⟩; simp; rw [h.right]; assumption
  · rw [← List.take_append_drop m l] at l_last
    rw [List.head?_append_of_ne_nil] at l_last; exact l_last
    rw [← h.right] at m_le_n
    intro hnil; simp at hnil
    cases' hnil with hnil hnil <;> subst hnil <;> try simp at m_le_n; linarith

theorem take_right_with_last {n : ℕ} {l : List α} (h : C.NCup n l) (m : ℕ) (p : α) :
    1 ≤ m → m ≤ n → p ∈ l.getLast? → ∃ l' : List α, l' ⊆ l ∧ C.NCup m l' ∧ p ∈ l'.getLast? :=
  by
  intro one_le_m m_le_n l_last
  use l.drop (n - m); refine' ⟨_, _, _⟩
  · exact List.drop_subset (n - m) l
  · constructor; exact h.left.drop (n - m); simp; rw [h.right]
    exact Nat.sub_sub_self m_le_n
  · rw [← List.take_append_drop (n - m) l] at l_last
    rw [List.getLast?_append_of_ne_nil] at l_last; exact l_last
    rw [← h.right] at m_le_n
    intro hnil; rw [← List.reverse_eq_nil_iff, ← h.right] at hnil
    simp at hnil
    omega

theorem head?_lt_getLast? {n : ℕ} {l : List α} (l_ncup : C.NCup (n + 2) l) (p q : α)
    (hp : p ∈ l.head?) (hq : q ∈ l.getLast?) : p < q :=
  by
  cases' l_ncup with l_cup l_length
  apply l_cup.head?_lt_getLast? p q
  rw [l_length]; exact le_add_self
  assumption; assumption

theorem head?_le_getLast? {n : ℕ} {l : List α} (l_ncup : C.NCup n l) (p q : α) (hp : p ∈ l.head?)
    (hq : q ∈ l.getLast?) : p ≤ q :=
  by
  have l_sorted : l.Sorted (· < ·) :=
    by
    rw [List.Sorted, ← List.chain'_iff_pairwise]
    exact l_ncup.left.left
  cases' l_ncup with l_cup l_length
  cases' l with p l; simp at hp
  simp at hp; subst hp
  cases' l with p' l; simp at hq; subst hq; exact le_rfl
  rw [List.getLast?_cons_cons] at hq
  set l' := p'::l; clear_value l'
  simp at l_sorted
  apply le_of_lt; apply l_sorted.left
  exact List.mem_of_mem_getLast? hq

end NCup

end Config

theorem ncup_is_ngon {n : ℕ} {S : Finset α} (hn : 2 ≤ n) (h : C.HasNCup n S) : C.HasNGon n S :=
  by
  rcases h with ⟨c, ⟨⟨c_cup, c_length⟩, c_in_S⟩⟩
  have hc : c ≠ [] := by cases c; subst c_length; simp at hn; tauto
  rcases List.takeLast hc with ⟨y, c, eq_c⟩; subst eq_c
  have hc : c ≠ [] := by
    intro h; subst c_length; subst h; simp at hn
  rcases List.takeHead hc with ⟨x, c, eq_c⟩; subst eq_c
  clear hc
  use[x, y], (x::c) ++ [y]
  refine' ⟨_, _, _⟩; try simp; simp at c_in_S; tauto
  rw [Config.NGon, Config.Gon]; simp
  have hxy : x < y := by
    apply c_cup.head?_lt_getLast? x y <;> simp
  simp at c_length; rw [c_length]; constructor; tauto; linarith
  simp at c_in_S; simp; tauto
  exact c_in_S

theorem hasNCap_supset {n : ℕ} {S1 S2 : Finset α} (h : S1 ⊆ S2) (h1 : C.HasNCap n S1) :
    C.HasNCap n S2 := by
  cases' h1 with c1 h1
  use c1; constructor; exact h1.left
  intro a a_c1; exact h (h1.right a a_c1)

theorem hasNCup_supset {n : ℕ} {S1 S2 : Finset α} (h : S1 ⊆ S2) (h1 : C.HasNCup n S1) :
    C.HasNCup n S2 := by
  cases' h1 with c1 h1
  use c1; constructor; exact h1.left
  intro a a_c1; exact h (h1.right a a_c1)

theorem hasNGon_supset {n : ℕ} {S1 S2 : Finset α} (h : S1 ⊆ S2) (h1 : C.HasNGon n S1) :
    C.HasNGon n S2 := by
  rcases h1 with ⟨c1, c2, ⟨gon, c1_in, c2_in⟩⟩
  exists c1, c2; refine' ⟨gon, _, _⟩
  intro a a_c1; apply h; exact c1_in a a_c1
  intro a a_c2; apply h; exact c2_in a a_c2

theorem hasNCup_le {n m : ℕ} {S : Finset α} (h : n ≤ m) : C.HasNCup m S → C.HasNCup n S :=
  by
  intro ngon
  rcases ngon with ⟨c, ⟨⟨c_cup, c_length⟩, c_in⟩⟩
  use c.take n; constructor
  · constructor; exact c_cup.take n; simp; rw [c_length]; exact h
  · intro a ha; apply c_in; exact List.take_subset _ _ ha
