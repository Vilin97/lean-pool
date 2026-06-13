/-
Copyright (c) 2026 Jineon Baek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jineon Baek
-/

import Mathlib.Algebra.Algebra.Defs
import Mathlib.Data.List.Sort
import Mathlib.Tactic.Linarith
import LeanPool.ErdosTuzaValtr.Config.Defs

/-!
# LeanPool.ErdosTuzaValtr.Config.Lemmas

Imported Lean Pool material for `LeanPool.ErdosTuzaValtr.Config.Lemmas`.
-/


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
  simp only [Config.Cap, List.isChain_cons_cons, List.chain3'_cons]
  tauto

@[simp]
protected theorem append_cons3 {a b c : α} {l1 l2 : List α} :
    C.Cap (l1 ++ a::b::c::l2) ↔ C.Cap (l1 ++ [a, b]) ∧ C.Cap3 a b c ∧ C.Cap (b::c::l2) := by
  simp only [Config.Cap, List.chain3'_append_cons3, List.isChain_append_cons_cons,
    List.isChain_cons_cons]
  tauto

protected theorem dropLast {l : List α} (h : C.Cap l) : C.Cap l.dropLast :=
  ⟨h.left.dropLast, h.right.dropLast⟩

protected theorem tail {l : List α} (h : C.Cap l) : C.Cap l.tail :=
  ⟨h.left.tail, h.right.tail⟩

end Cap

namespace NCap

protected theorem dropLast {n : ℕ} {l : List α} (h : C.NCap (n + 1) l) : C.NCap n l.dropLast :=
  ⟨h.1.dropLast, by rw [List.length_dropLast, h.2, Nat.add_sub_cancel]⟩

protected theorem tail {n : ℕ} {l : List α} (h : C.NCap (n + 1) l) : C.NCap n l.tail :=
  ⟨h.1.tail, by rw [List.length_tail, h.2, Nat.add_sub_cancel]⟩

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
  simp only [Config.Cup, List.isChain_cons_cons, List.chain3'_cons]
  tauto

@[simp]
protected theorem append_cons3 {a b c : α} {l1 l2 : List α} :
    C.Cup (l1 ++ a::b::c::l2) ↔ C.Cup (l1 ++ [a, b]) ∧ C.Cup3 a b c ∧ C.Cup (b::c::l2) := by
  simp only [Config.Cup, List.chain3'_append_cons3, List.isChain_append_cons_cons,
    List.isChain_cons_cons]
  tauto

protected theorem dropLast {l : List α} (h : C.Cup l) : C.Cup l.dropLast :=
  ⟨h.left.dropLast, h.right.dropLast⟩

protected theorem take {l : List α} (h : C.Cup l) (n : ℕ) : C.Cup (l.take n) :=
  ⟨h.left.take n, h.right.take n⟩

protected theorem drop {l : List α} (h : C.Cup l) (n : ℕ) : C.Cup (l.drop n) :=
  ⟨h.left.drop n, h.right.drop n⟩

protected theorem tail {l : List α} (h : C.Cup l) : C.Cup l.tail :=
  ⟨h.left.tail, h.right.tail⟩

theorem head_lt_getLast {l : List α} (l_cup : C.Cup l) (p q : α) (hl : 2 ≤ l.length)
    (hp : p ∈ l.head?) (hq : q ∈ l.getLast?) : p < q := by
  cases l with
  | nil => exact absurd hp (Option.not_mem_none p)
  | cons x l =>
    rw [List.head?_cons, Option.mem_some_iff] at hp
    subst hp
    have l_nnil : l ≠ [] := by
      rintro rfl
      simp only [List.length_cons, List.length_nil] at hl
      omega
    rcases List.takeLast l_nnil with ⟨q', l', eq_l⟩
    rw [eq_l, ← List.cons_append, List.getLast?_concat, Option.mem_some_iff] at hq
    have l_sorted := List.isChain_iff_pairwise.mp l_cup.left
    rw [eq_l, ← List.cons_append, List.pairwise_append] at l_sorted
    rw [← hq]
    exact l_sorted.2.2 x (by simp) q' (by simp)

/-- Compatibility alias for the upstream theorem name. -/
theorem «head?_lt_getLast?» {l : List α} (l_cup : C.Cup l) (p q : α) (hl : 2 ≤ l.length)
    (hp : p ∈ l.head?) (hq : q ∈ l.getLast?) : p < q := head_lt_getLast l_cup p q hl hp hq

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
  simp only [Config.NCup, Cup.cons3, List.length_cons, Nat.add_right_cancel_iff]
  tauto

protected theorem dropLast {n : ℕ} {l : List α} (h : C.NCup (n + 1) l) : C.NCup n l.dropLast :=
  ⟨h.1.dropLast, by rw [List.length_dropLast, h.2, Nat.add_sub_cancel]⟩

protected theorem dropLast_append_last {n : ℕ} {l : List α} (h : C.NCup (n + 1) l) :
    ∃ (l' : List α) (a : α), l = l' ++ [a] ∧ C.NCup n l' := by
  have nnil : l ≠ [] := by
    rintro rfl
    rw [Config.NCup] at h
    simp only [List.length_nil] at h
    omega
  exact ⟨l.dropLast, l.getLast nnil, (List.dropLast_append_getLast nnil).symm, h.dropLast⟩

protected theorem tail {n : ℕ} {l : List α} (h : C.NCup (n + 1) l) : C.NCup n l.tail :=
  ⟨h.1.tail, by rw [List.length_tail, h.2, Nat.add_sub_cancel]⟩

protected theorem cons_head_tail {n : ℕ} {l : List α} (h : C.NCup (n + 1) l) :
    ∃ (a : α) (l' : List α), (l = a::l') ∧ C.NCup n l' := by
  cases l with
  | nil =>
    rw [Config.NCup] at h
    simp only [List.length_nil] at h
    omega
  | cons a l => exact ⟨a, l, rfl, h.tail⟩

protected theorem take_head_last {n : ℕ} {l : List α} (h : C.NCup (n + 2) l) :
    ∃ (a : α) (l' : List α) (b : α), l = (a::l') ++ [b] ∧ C.NCup n l' := by
  rcases h.cons_head_tail with ⟨a, l', eq_l, cup_l'⟩
  rcases cup_l'.dropLast_append_last with ⟨l'', b, eq_l', cup_l''⟩
  refine ⟨a, l'', b, ?_, cup_l''⟩
  rw [eq_l, eq_l', List.cons_append]

theorem take_left_with_head {n : ℕ} {l : List α} (h : C.NCup n l) (m : ℕ) (p : α) :
    1 ≤ m → m ≤ n → p ∈ l.head? → ∃ l' : List α, l' ⊆ l ∧ C.NCup m l' ∧ p ∈ l'.head? := by
  intro one_le_m m_le_n l_last
  refine ⟨l.take m, List.take_subset m l, ⟨h.left.take m, ?_⟩, ?_⟩
  · rw [List.length_take, h.right, Nat.min_eq_left m_le_n]
  · rw [← List.take_append_drop m l] at l_last
    rw [List.head?_append_of_ne_nil] at l_last
    · exact l_last
    · intro hnil
      rw [List.take_eq_nil_iff] at hnil
      rcases hnil with hm | hl
      · omega
      · have hlen := h.right
        rw [hl, List.length_nil] at hlen
        omega

theorem take_right_with_last {n : ℕ} {l : List α} (h : C.NCup n l) (m : ℕ) (p : α) :
    1 ≤ m → m ≤ n → p ∈ l.getLast? → ∃ l' : List α, l' ⊆ l ∧ C.NCup m l' ∧ p ∈ l'.getLast? := by
  intro one_le_m m_le_n l_last
  refine ⟨l.drop (n - m), List.drop_subset (n - m) l, ⟨h.left.drop (n - m), ?_⟩, ?_⟩
  · rw [List.length_drop, h.right]
    omega
  · rw [← List.take_append_drop (n - m) l] at l_last
    rw [List.getLast?_append_of_ne_nil] at l_last
    · exact l_last
    · intro hnil
      have hlen : (l.drop (n - m)).length = 0 := by rw [hnil, List.length_nil]
      rw [List.length_drop, h.right] at hlen
      omega

theorem head_lt_getLast {n : ℕ} {l : List α} (l_ncup : C.NCup (n + 2) l) (p q : α)
    (hp : p ∈ l.head?) (hq : q ∈ l.getLast?) : p < q :=
  l_ncup.left.head_lt_getLast p q (by rw [l_ncup.right]; omega) hp hq

/-- Compatibility alias for the upstream theorem name. -/
theorem «head?_lt_getLast?» {n : ℕ} {l : List α} (l_ncup : C.NCup (n + 2) l) (p q : α)
    (hp : p ∈ l.head?) (hq : q ∈ l.getLast?) : p < q := head_lt_getLast l_ncup p q hp hq

theorem head_le_getLast {n : ℕ} {l : List α} (l_ncup : C.NCup n l) (p q : α) (hp : p ∈ l.head?)
    (hq : q ∈ l.getLast?) : p ≤ q := by
  have l_sorted : l.Pairwise (· < ·) := List.isChain_iff_pairwise.mp l_ncup.left.left
  cases l with
  | nil => exact absurd hp (Option.not_mem_none p)
  | cons x rest =>
    rw [List.head?_cons, Option.mem_some_iff] at hp
    subst hp
    cases rest with
    | nil =>
      rw [List.getLast?_singleton, Option.mem_some_iff] at hq
      rw [← hq]
    | cons p' rest =>
      rw [List.getLast?_cons_cons] at hq
      rw [List.pairwise_cons] at l_sorted
      exact le_of_lt (l_sorted.1 q (List.mem_of_mem_getLast? hq))

/-- Compatibility alias for the upstream theorem name. -/
theorem «head?_le_getLast?» {n : ℕ} {l : List α} (l_ncup : C.NCup n l) (p q : α)
    (hp : p ∈ l.head?) (hq : q ∈ l.getLast?) : p ≤ q := head_le_getLast l_ncup p q hp hq

end NCup

end Config

theorem ncup_is_ngon {n : ℕ} {S : Finset α} (hn : 2 ≤ n) (h : C.HasNCup n S) : C.HasNGon n S := by
  rcases h with ⟨c, ⟨⟨c_cup, c_length⟩, c_in_S⟩⟩
  have hc : c ≠ [] := by
    rintro rfl
    rw [List.length_nil] at c_length
    omega
  rcases List.takeLast hc with ⟨y, c, eq_c⟩; subst eq_c
  have hc : c ≠ [] := by
    rintro rfl
    simp only [List.nil_append, List.length_cons, List.length_nil] at c_length
    omega
  rcases List.takeHead hc with ⟨x, c, eq_c⟩; subst eq_c
  clear hc
  have hxy : x < y :=
    c_cup.head_lt_getLast x y (by rw [c_length]; omega) (by simp) (by simp)
  refine ⟨[x, y], (x :: c) ++ [y], ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩, ?_, ?_⟩
  · simp
  · rw [Config.Cap]
    exact ⟨by simpa using hxy, by simp [List.Chain3']⟩
  · simp only [List.length_append, List.length_cons]
    omega
  · exact c_cup
  · simp
  · simp
  · simp only [List.length_cons, List.length_append, List.length_nil] at c_length ⊢
    omega
  · simp only [List.append_in, List.cons_in, List.nil_in, and_true] at c_in_S
    simp only [List.cons_in, List.nil_in, and_true]
    exact ⟨c_in_S.1.1, c_in_S.2⟩
  · exact c_in_S

theorem hasNCap_supset {n : ℕ} {S1 S2 : Finset α} (h : S1 ⊆ S2) (h1 : C.HasNCap n S1) :
    C.HasNCap n S2 := by
  obtain ⟨c1, h1⟩ := h1
  exact ⟨c1, h1.left, fun a a_c1 => h (h1.right a a_c1)⟩

theorem hasNCup_supset {n : ℕ} {S1 S2 : Finset α} (h : S1 ⊆ S2) (h1 : C.HasNCup n S1) :
    C.HasNCup n S2 := by
  obtain ⟨c1, h1⟩ := h1
  exact ⟨c1, h1.left, fun a a_c1 => h (h1.right a a_c1)⟩

theorem hasNGon_supset {n : ℕ} {S1 S2 : Finset α} (h : S1 ⊆ S2) (h1 : C.HasNGon n S1) :
    C.HasNGon n S2 := by
  rcases h1 with ⟨c1, c2, ⟨gon, c1_in, c2_in⟩⟩
  exact ⟨c1, c2, gon, fun a a_c1 => h (c1_in a a_c1), fun a a_c2 => h (c2_in a a_c2)⟩

theorem hasNCup_le {n m : ℕ} {S : Finset α} (h : n ≤ m) : C.HasNCup m S → C.HasNCup n S := by
  rintro ⟨c, ⟨⟨c_cup, c_length⟩, c_in⟩⟩
  refine ⟨c.take n, ⟨c_cup.take n, ?_⟩, fun a ha => c_in a (List.take_subset _ _ ha)⟩
  rw [List.length_take, c_length, Nat.min_eq_left h]
