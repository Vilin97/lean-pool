/-
Copyright (c) 2026 Jineon Baek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jineon Baek
-/

import Mathlib.Order.Basic
import Mathlib.Tactic.Ring.RingNF
import LeanPool.ErdosTuzaValtr.Lib.List.Default
import LeanPool.ErdosTuzaValtr.Etv.Default
import LeanPool.ErdosTuzaValtr.Main.Lemmas.JoinN2N3N2

open OrderDual

variable {α : Type _} [LinearOrder α] (C : Config α)

theorem Config.join_n2_n2_interweaved {S : Finset α} {n : ℕ} {c1 : List α}
    (c1_cup : C.NCup (n + 2) c1) (c1_in_S : c1.In S) {c2 : List α} (c2_cup : C.NCup (n + 2) c2)
    (c2_in_S : c2.In S) (x : α) (c1_last : x ∈ c1.getLast?) (c2_head : x ∈ c2.head?) :
    ∃ p q r s, C.HasInterweavedLaced (n + 2) S p q r s :=
  by
  rcases c1_cup.take_head_last with ⟨p, c1', q, eq_c1, c1'_cup⟩
  rcases c2_cup.take_head_last with ⟨q, c2', r, eq_c2, c2'_cup⟩
  rw [eq_c1] at c1_last; rw [eq_c2] at c2_head
  simp at c1_last c2_head; subst c1_last; subst c2_head
  use p, q, q, r; refine' ⟨_, _, _⟩
  · refine' ⟨_, _, _⟩
    rw [eq_c1] at c1_cup; apply c1_cup.head?_lt_getLast? p q <;> simp; simp
    rw [eq_c2] at c2_cup; apply c2_cup.head?_lt_getLast? q r <;> simp
  · exists 1, n + 1, [p], c1, c2.dropLast, (by simp), c1_cup, c2_cup.dropLast; simp
    rw [eq_c1] at c1_in_S ⊢; rw [eq_c2] at c2_in_S ⊢
    simp only [List.getLast?_concat, List.cons_in, List.append_in, List.nil_in, and_true,
      List.head?_cons, List.getLast?_cons_append_cons, List.getLast?_singleton, true_and,
      List.dropLast_concat]
        at c1_in_S c2_in_S ⊢; ring_nf;
    simp only [List.cons_append, List.head?_cons]
    tauto
  · exists n + 1, 1, c1.tail, c2, [r], c1_cup.tail, c2_cup, (by simp); simp
    rw [eq_c1] at c1_in_S ⊢; rw [eq_c2] at c2_in_S ⊢
    simp at c1_in_S c2_in_S ⊢; tauto

theorem Config.join_n2_n3_join_n3_n2_main (S : Finset α) (n : ℕ) (cap4_free : ¬C.HasNCap 4 S)
    (cup_free : ¬C.HasNCup (n + 4) S) {cx : List α} (cx_cup : C.NCup (n + 2) cx) (cx_in_S : cx.In S)
    {cx1 : List α} (cx1_cup : C.NCup (n + 3) cx1) (cx1_in_S : cx1.In S) {cy1 : List α}
    (cy1_cup : C.NCup (n + 3) cy1) (cy1_in_S : cy1.In S) {cy : List α} (cy_cup : C.NCup (n + 2) cy)
    (cy_in_S : cy.In S) (x : α) (cx_last : x ∈ cx.getLast?) (cx1_head : x ∈ cx1.head?) (y : α)
    (cy1_last : y ∈ cy1.getLast?) (cy_head : y ∈ cy.head?) :
    ∃ p q r s, C.HasInterweavedLaced (n + 3) S p q r s :=
  by
  have l := cap4FreeLabel cap4_free
  have x_in_S := cx_in_S _ (List.mem_of_mem_getLast? cx_last)
  have y_in_S := cy_in_S _ (List.mem_of_mem_head? cy_head)
  rcases lt_or_le y x with (hxy | hxy)
  -- Case y < x
  · by_cases lyx : l.Slope y x
    · exfalso; apply cup_free; use cy1 ++ [x]; constructor
      apply cy1_cup.extend_right lyx <;> try assumption
      simp; constructor <;> assumption
    · exfalso; apply cup_free; use y::cx1; constructor
      apply cx1_cup.extend_left lyx <;> try assumption
      simp; constructor <;> assumption
  -- Case x ≤ y
  rcases cx1_cup.take_head_last with ⟨x, cx1', z, eq_cx1, cx1'_cup⟩
  rw [eq_cx1] at cx1_head; simp at cx1_head; subst cx1_head
  rcases cy1_cup.take_head_last with ⟨w, cy1', y, eq_cy1, cy1'_cup⟩
  rw [eq_cy1] at cy1_last; simp at cy1_last; subst cy1_last
  have z_in_S : z ∈ S := by rw [eq_cx1] at cx1_in_S <;> simp at cx1_in_S <;> tauto
  have w_in_S : w ∈ S := by rw [eq_cy1] at cy1_in_S <;> simp at cy1_in_S <;> tauto
  rcases lt_trichotomy x w with (hwx | hwx | hwx); swap
  · subst hwx;
    apply
          C.join_n2_n3_n2 S cap4_free cup_free cx_cup cx_in_S cy1_cup cy1_in_S cy_cup cy_in_S x
            cx_last _ y _ cy_head <;>
        rw [eq_cy1] <;>
      simp
  · by_cases lxw : l.Slope x w
    · have cxw_cup : C.NCup (n + 3) (cx ++ [w]) := by
        apply cx_cup.extend_right lxw <;> try assumption
      apply C.join_n2_n2_interweaved cxw_cup _ cy1_cup cy1_in_S w
      simp; rw [eq_cy1]; simp; simp; tauto
    · exfalso; apply cup_free; use x::cy1; constructor
      apply cy1_cup.extend_left lxw <;> try assumption;
      rw [eq_cy1]; simp
      simp; constructor <;> assumption
  -- w < x
  rcases lt_trichotomy z y with (hyz | hyz | hyz);
  swap
  · subst hyz;
    apply
          C.join_n2_n3_n2 S cap4_free cup_free cx_cup cx_in_S cx1_cup cx1_in_S cy_cup cy_in_S x
            cx_last _ z _ cy_head <;>
        rw [eq_cx1] <;>
      simp
  · by_cases lzy : l.Slope z y
    · exfalso; apply cup_free; use cx1 ++ [y]; constructor
      apply cx1_cup.extend_right lzy <;> try assumption
      rw [eq_cx1]; simp
      simp; constructor <;> assumption
    · have zcy_cup : C.NCup (n + 3) (z::cy) := by apply cy_cup.extend_left lzy <;> try assumption
      apply C.join_n2_n2_interweaved cx1_cup _ zcy_cup _ z
      rw [eq_cx1]; simp; simp; tauto; simp; tauto
  -- y < z
  use w, x, y, z;
  refine' ⟨_, _, _⟩; tauto
  · exists 1, n + 2, [w], cy1, cy, (by simp), cy1_cup, cy_cup; simp
    constructor; tauto; constructor; ring_nf; rw [eq_cy1]; simp; assumption
  · exists n + 2, 1, cx, cx1, [z], cx_cup, cx1_cup, (by simp); simp
    constructor; tauto; constructor; rw [←Option.mem_def]; assumption
    rw [eq_cx1]; simp

theorem Config.join_n2_n3_join_n3_n2 (S : Finset α) (n : ℕ) (cap4_free : ¬C.HasNCap 4 S)
    (cup_free : ¬C.HasNCup (n + 4) S) (hx : C.HasJoin (n + 2) (n + 3) S)
    (hy : C.HasJoin (n + 3) (n + 2) S) : ∃ p q r s, C.HasInterweavedLaced (n + 3) S p q r s :=
  by
  rcases hx with ⟨x, cx, cx1, ⟨cx_cup, cx_in_S, cx_last⟩, ⟨cx1_cup, cx1_in_S, cx1_head⟩⟩
  rcases hy with ⟨y, cy1, cy, ⟨cy1_cup, cy1_in_S, cy1_last⟩, ⟨cy_cup, cy_in_S, cy_head⟩⟩
  apply
    C.join_n2_n3_join_n3_n2_main S n cap4_free cup_free cx_cup cx_in_S cx1_cup cx1_in_S cy1_cup
      cy1_in_S cy_cup cy_in_S x cx_last cx1_head y cy1_last cy_head
