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
    ∃ p q r s, C.HasInterweavedLaced (n + 2) S p q r s := by
  rcases c1_cup.take_head_last with ⟨p, c1', x1, eq_c1, c1'_cup⟩
  rcases c2_cup.take_head_last with ⟨x2, c2', r, eq_c2, c2'_cup⟩
  rw [eq_c1, List.getLast?_concat, Option.mem_some_iff] at c1_last
  rw [eq_c2, List.cons_append, List.head?_cons, Option.mem_some_iff] at c2_head
  subst x1; subst x2
  have c1_last' : x ∈ c1.getLast? := by rw [eq_c1, List.getLast?_concat]; rfl
  have c2_head' : x ∈ c2.head? := by rw [eq_c2, List.cons_append, List.head?_cons]; rfl
  have c1_head : p ∈ c1.head? := by rw [eq_c1, List.cons_append, List.head?_cons]; rfl
  have c2_last : r ∈ c2.getLast? := by rw [eq_c2, List.getLast?_concat]; rfl
  have p_lt_x : p < x := c1_cup.head_lt_getLast p x c1_head c1_last'
  have x_lt_r : x < r := c2_cup.head_lt_getLast x r c2_head' c2_last
  have x_in_S : x ∈ S := c1_in_S x (by rw [eq_c1]; simp)
  have p_in_S : p ∈ S := c1_in_S p (by rw [eq_c1]; simp)
  have r_in_S : r ∈ S := c2_in_S r (by rw [eq_c2]; simp)
  have hc2d_head : x ∈ c2.dropLast.head? := by
    rw [eq_c2, show (x :: c2') ++ [r] = x :: (c2' ++ [r]) by simp,
      List.dropLast_cons_of_ne_nil (by simp), List.head?_cons]; rfl
  have hc1t_last : x ∈ c1.tail.getLast? := by
    rw [eq_c1, show (p :: c1') ++ [x] = p :: (c1' ++ [x]) by simp, List.tail_cons,
      List.getLast?_concat]; rfl
  refine ⟨p, x, x, r, ⟨p_lt_x, le_refl x, x_lt_r⟩, ?_, ?_⟩
  · -- HasLaced (n+2) S p x
    have hp : C.NCup 1 [p] := by simp
    have hc2d : C.NCup (n + 1) c2.dropLast := c2_cup.dropLast
    refine ⟨1, n + 1, _, _, _, hp, c1_cup, hc2d, ⟨?_, c1_in_S, ?_⟩, by omega,
      by rw [List.getLast?_singleton]; rfl, c1_head, c1_last', hc2d_head⟩
    · rw [List.cons_in]; exact ⟨p_in_S, List.nil_in⟩
    · exact fun w hw => c2_in_S w (List.dropLast_subset _ hw)
  · -- HasLaced (n+2) S x r
    have hr : C.NCup 1 [r] := by simp
    have hc1t : C.NCup (n + 1) c1.tail := c1_cup.tail
    refine ⟨n + 1, 1, _, _, _, hc1t, c2_cup, hr, ⟨?_, c2_in_S, ?_⟩, by omega,
      hc1t_last, c2_head', c2_last, by rw [List.head?_cons]; rfl⟩
    · exact fun w hw => c1_in_S w (List.tail_subset _ hw)
    · rw [List.cons_in]; exact ⟨r_in_S, List.nil_in⟩

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
  rcases lt_or_ge y x with (hxy | hxy)
  -- Case y < x
  · by_cases lyx : l.Slope y x
    · exfalso
      apply cup_free
      refine ⟨cy1 ++ [x], cy1_cup.extend_right lyx hxy x_in_S cy1_in_S cy1_last, ?_⟩
      rw [List.append_in, List.cons_in]
      exact ⟨cy1_in_S, x_in_S, List.nil_in⟩
    · exfalso
      apply cup_free
      refine ⟨y :: cx1, cx1_cup.extend_left lyx y_in_S hxy cx1_in_S cx1_head, ?_⟩
      rw [List.cons_in]
      exact ⟨y_in_S, cx1_in_S⟩
  -- Case x ≤ y
  rcases cx1_cup.take_head_last with ⟨x', cx1', z, eq_cx1, cx1'_cup⟩
  rw [eq_cx1, List.cons_append, List.head?_cons, Option.mem_some_iff] at cx1_head
  subst x'
  rcases cy1_cup.take_head_last with ⟨w, cy1', y', eq_cy1, cy1'_cup⟩
  rw [eq_cy1, List.getLast?_concat, Option.mem_some_iff] at cy1_last
  subst y'
  have z_in_S : z ∈ S := cx1_in_S z (by rw [eq_cx1]; simp)
  have w_in_S : w ∈ S := cy1_in_S w (by rw [eq_cy1]; simp)
  rcases lt_trichotomy x w with (hwx | hwx | hwx); swap
  · subst hwx;
    apply
          C.join_n2_n3_n2 S cap4_free cup_free cx_cup cx_in_S cy1_cup cy1_in_S cy_cup cy_in_S x
            cx_last _ y _ cy_head <;>
        rw [eq_cy1] <;>
      simp
  · by_cases lxw : l.Slope x w
    · have cxw_cup : C.NCup (n + 3) (cx ++ [w]) :=
        cx_cup.extend_right lxw hwx w_in_S cx_in_S cx_last
      apply C.join_n2_n2_interweaved cxw_cup ?_ cy1_cup cy1_in_S w
      · rw [List.getLast?_concat]; rfl
      · rw [eq_cy1, List.cons_append, List.head?_cons]; rfl
      · rw [List.append_in, List.cons_in]
        exact ⟨cx_in_S, w_in_S, List.nil_in⟩
    · exfalso
      apply cup_free
      refine ⟨x :: cy1, cy1_cup.extend_left lxw x_in_S hwx cy1_in_S ?_, ?_⟩
      · rw [eq_cy1, List.cons_append, List.head?_cons]; rfl
      · rw [List.cons_in]
        exact ⟨x_in_S, cy1_in_S⟩
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
    · exfalso
      apply cup_free
      have cx1_last : z ∈ cx1.getLast? := by rw [eq_cx1, List.getLast?_concat]; rfl
      refine ⟨cx1 ++ [y], cx1_cup.extend_right lzy hyz y_in_S cx1_in_S cx1_last, ?_⟩
      rw [List.append_in, List.cons_in]
      exact ⟨cx1_in_S, y_in_S, List.nil_in⟩
    · have zcy_cup : C.NCup (n + 3) (z :: cy) :=
        cy_cup.extend_left lzy z_in_S hyz cy_in_S cy_head
      apply C.join_n2_n2_interweaved cx1_cup ?_ zcy_cup ?_ z
      · rw [eq_cx1, List.getLast?_concat]; rfl
      · rw [List.head?_cons]; rfl
      · exact cx1_in_S
      · rw [List.cons_in]; exact ⟨z_in_S, cy_in_S⟩
  -- y < z
  have cy1_head : w ∈ cy1.head? := by rw [eq_cy1, List.cons_append, List.head?_cons]; rfl
  have cy1_last : y ∈ cy1.getLast? := by rw [eq_cy1, List.getLast?_concat]; rfl
  have cx1_head : x ∈ cx1.head? := by rw [eq_cx1, List.cons_append, List.head?_cons]; rfl
  have cx1_last : z ∈ cx1.getLast? := by rw [eq_cx1, List.getLast?_concat]; rfl
  refine ⟨w, x, y, z, ⟨hwx, hxy, hyz⟩, ?_, ?_⟩
  · -- HasLaced (n+3) S w y
    have hw : C.NCup 1 [w] := by simp
    refine ⟨1, n + 2, _, _, _, hw, cy1_cup, cy_cup, ⟨?_, cy1_in_S, cy_in_S⟩, by omega,
      by rw [List.getLast?_singleton]; rfl, cy1_head, cy1_last, cy_head⟩
    rw [List.cons_in]; exact ⟨w_in_S, List.nil_in⟩
  · -- HasLaced (n+3) S x z
    have hz : C.NCup 1 [z] := by simp
    refine ⟨n + 2, 1, _, _, _, cx_cup, cx1_cup, hz, ⟨cx_in_S, cx1_in_S, ?_⟩, by omega,
      cx_last, cx1_head, cx1_last, by rw [List.head?_cons]; rfl⟩
    rw [List.cons_in]; exact ⟨z_in_S, List.nil_in⟩

theorem Config.join_n2_n3_join_n3_n2 (S : Finset α) (n : ℕ) (cap4_free : ¬C.HasNCap 4 S)
    (cup_free : ¬C.HasNCup (n + 4) S) (hx : C.HasJoin (n + 2) (n + 3) S)
    (hy : C.HasJoin (n + 3) (n + 2) S) : ∃ p q r s, C.HasInterweavedLaced (n + 3) S p q r s :=
  by
  rcases hx with ⟨x, cx, cx1, ⟨cx_cup, cx_in_S, cx_last⟩, ⟨cx1_cup, cx1_in_S, cx1_head⟩⟩
  rcases hy with ⟨y, cy1, cy, ⟨cy1_cup, cy1_in_S, cy1_last⟩, ⟨cy_cup, cy_in_S, cy_head⟩⟩
  apply
    C.join_n2_n3_join_n3_n2_main S n cap4_free cup_free cx_cup cx_in_S cx1_cup cx1_in_S cy1_cup
      cy1_in_S cy_cup cy_in_S x cx_last cx1_head y cy1_last cy_head
