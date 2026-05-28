/-
Copyright (c) 2026 Jineon Baek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jineon Baek
-/

import Mathlib.Order.Basic
import Mathlib.Tactic.Ring.RingNF
import LeanPool.ErdosTuzaValtr.Lib.List.Default
import LeanPool.ErdosTuzaValtr.Etv.Defs
import LeanPool.ErdosTuzaValtr.Etv.Label

open OrderDual

variable {α : Type _} [LinearOrder α] (C : Config α)

theorem Config.join_n2_n2_case_ff (S : Finset α) (n : ℕ) (a x b : α) (c1 c2 : List α)
    (lab : C.Label S) (a_in_S : a ∈ S) (x_in_S : x ∈ S) (b_in_S : b ∈ S)
    (hc1 : C.NCup (n + 2) (c1 ++ [a, x])) (c1_in_S : c1.In S) (hc2 : C.NCup (n + 2) (x::b::c2))
    (c2_in_S : c2.In S) (sab : ¬lab.Slope a b) : C.HasNGon (n + 3) S :=
  by
  have hax : a < x := by simp [Config.Cup, Config.NCup] at hc1 <;> tauto
  have hxb : x < b := by simp [Config.Cup, Config.NCup] at hc2 <;> tauto
  have hab : a < b := LT.lt.trans hax hxb
  have h_b_c2 : (b::c2) ≠ [] := by simp
  rcases List.takeLast h_b_c2 with ⟨c, c3, eq_c2⟩
  rw [eq_c2] at hc2
  have hxc : x < c := by apply hc2.head?_lt_getLast? x c <;> simp <;> decide
  have c_in_S : c ∈ S := by
    have h_in : (b::c2).In S := by simp; tauto
    rw [eq_c2] at h_in; simp at h_in; tauto
  by_cases haxc : C.Cup3 a x c
  · apply ncup_is_ngon; simp
    use c1 ++ [a, x, c]; constructor; constructor
    simp; rw [Config.NCup] at hc1; tauto
    simp; simp [Config.NCup] at hc1; tauto
    simp; tauto
  · use[a, x, c], a::c3 ++ [c]
    refine' ⟨⟨_, _⟩, _, _⟩ <;> try simp; try tauto
    constructor; tauto
    rw [← eq_c2]; rw [← eq_c2] at hc2
    have hbc2 := hc2.tail.left; simp at hbc2
    apply hbc2.extend_left sab <;> try tauto
    simp; tauto; simp [Config.NCup] at hc2
    ring_nf; simp; exact hc2.right
    constructor; assumption
    have hh : (b::c2).In S := by simp; tauto
    rw [eq_c2] at hh; simp at hh; exact hh

theorem Config.join_n2_n2_case_tt (S : Finset α) (n : ℕ) (a x b : α) (c1 c2 : List α)
    (lab : C.Label S) (a_in_S : a ∈ S) (x_in_S : x ∈ S) (b_in_S : b ∈ S)
    (hc1 : C.NCup (n + 2) (c1 ++ [a, x])) (c1_in_S : c1.In S) (hc2 : C.NCup (n + 2) (x::b::c2))
    (c2_in_S : c2.In S) (hab : lab.Slope a b) : C.HasNGon (n + 3) S :=
  by
  rw [← Finset.memMirror] at a_in_S x_in_S b_in_S
  rw [← Mirror.ncup] at hc1 hc2
  rw [← List.Mirror_in] at c1_in_S c2_in_S
  simp at hc1 hc2
  have hba := hab; rw [← Mirror_slope] at hba
  have Mirrored_goal :=
    C.Mirror.join_n2_n2_case_ff S.Mirror n (toDual b) (toDual x) (toDual a) c2.Mirror c1.Mirror
      lab.Mirror b_in_S x_in_S a_in_S hc2 c2_in_S hc1 c1_in_S hba
  rw [Mirror.hasNGon] at Mirrored_goal
  tauto

theorem Config.join_n2_n2 (S : Finset α) {n : ℕ} (cap4_free : ¬C.HasNCap 4 S) {c1 : List α}
    (hc1 : C.NCup (n + 2) c1) (c1_in_S : c1.In S) {c2 : List α} (hc2 : C.NCup (n + 2) c2)
    (c2_in_S : c2.In S) (x : α) (hx1 : x ∈ c1.getLast?) (hx2 : x ∈ c2.head?) :
    C.HasNGon (n + 3) S :=
  by
  -- Introduce variables
  have c1_size2 : 2 ≤ c1.length := by cases hc1 <;> linarith
  rcases List.takeLast2 c1_size2 with ⟨a, x, c1', eq_c1⟩
  subst eq_c1; simp at hx1; subst hx1
  have c2_size2 : 2 ≤ c2.length := by cases hc2 <;> linarith
  rcases List.takeHead2 c2_size2 with ⟨x, b, c2', eq_c2⟩
  subst eq_c2; simp at hx2; subst hx2
  have lab := cap4FreeLabel cap4_free
  by_cases hl : lab.Slope a b
  · apply C.join_n2_n2_case_tt S n a x b c1' c2' lab <;> simp at c1_in_S c2_in_S <;> tauto
  · apply C.join_n2_n2_case_ff S n a x b c1' c2' lab <;> simp at c1_in_S c2_in_S <;> tauto
