/-
Copyright (c) 2026 Jineon Baek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jineon Baek
-/

import Mathlib.Order.Basic
import LeanPool.ErdosTuzaValtr.Lib.List.Default
import LeanPool.ErdosTuzaValtr.Etv.Default

open OrderDual

variable {α : Type _} [LinearOrder α] (C : Config α)

theorem Config.join_n2_n3_n2_ff (S : Finset α) (cap4_free : ¬C.HasNCap 4 S) {n : ℕ} (x y : α)
    {P : List α} (hPx : C.NCup (n + 2) (P ++ [x])) (Px_in_S : (P ++ [x]).In S) {Q : List α}
    (hxQy : C.NCup (n + 3) ((x::Q) ++ [y])) (xQy_in_S : ((x::Q) ++ [y]).In S) {R : List α}
    (hyR : C.NCup (n + 2) (y::R)) (yR_in_S : (y::R).In S) (label : C.Label S)
    (sxy : ¬label.Slope x y) : ∃ p q r s, C.HasInterweavedLaced (n + 3) S p q r s :=
  by
  have x_in_S : x ∈ S := by simp at xQy_in_S <;> tauto
  have y_in_S : y ∈ S := by simp at xQy_in_S <;> tauto
  have x_lt_y : x < y := by apply hxQy.head?_lt_getLast? x y <;> simp
  have hP := hPx.dropLast; simp at hP
  have hQy := hxQy.tail; simp at hQy
  rcases hP.dropLast_append_last with ⟨P', a, eq_P, hP'⟩; subst eq_P
  rcases hQy.cons_head_tail with ⟨b, Q', eq_Q, hQ'⟩
  have eq_xQy : (x::Q) ++ [y] = x::(Q ++ [y]) := by simp
  rw [eq_xQy] at hxQy xQy_in_S; clear eq_xQy
  rw [eq_Q] at hxQy xQy_in_S;
  have a_in_S : a ∈ S := by simp at Px_in_S <;> tauto
  have b_in_S : b ∈ S := by simp at xQy_in_S <;> tauto
  have hR := hyR.tail; simp at hR
  rcases hR.dropLast_append_last with ⟨R', z, eq_R, hR'⟩
  have xy_laced : C.HasLaced (n + 3) S x y :=
    by
    have hy : C.NCup 1 [y] := by simp
    exists _, _, _, _, _, hPx, hxQy, hy
    refine' ⟨_, _, _⟩
    constructor; assumption; constructor; assumption
    simp; simp at xQy_in_S; tauto
    simp; simp
    rw [←eq_Q]; simp
  have xz_laced : C.HasLaced (n + 3) S x z :=
    by
    have hxyR : C.NCup (n + 3) (x::y::R) := by
      apply hyR.extend_left sxy <;> try assumption
      simp
    rw [eq_R] at hxyR
    have hz : C.NCup 1 [z] := by simp
    exists _, _, _, _, _, hPx, hxyR, hz
    refine' ⟨_, _, _⟩
    constructor; assumption; rw [eq_R] at yR_in_S
    simp; simp at yR_in_S; tauto
    simp; simp
  have a_lt_x : a < x := by rw [Config.NCup, Config.Cup] at hPx <;> simp at hPx <;> tauto
  have x_lt_b : x < b := by rw [Config.NCup, Config.Cup] at hxQy <;> simp at hxQy <;> tauto
  have y_lt_z : y < z := by
    rw [eq_R] at hyR; apply hyR.head?_lt_getLast? y z
    simp; simp
  have a_lt_b : a < b := LT.lt.trans a_lt_x x_lt_b
  by_cases sab : label.Slope a b; swap
  -- case ¬label.Slope a b
  · have hQy := hxQy.tail; simp at hQy
    have haQy : C.NCup (n + 3) ((a::Q) ++ [y]) :=
      by
      rw [←eq_Q] at hQy xQy_in_S
      apply hQy.extend_left sab <;> try assumption
      simp; simp at xQy_in_S; tauto;
      rw [eq_Q]; simp
    have ha : C.NCup 1 [a] := by simp
    have ay_laced : C.HasLaced (n + 3) S a y :=
      by
      exists _, _, _, _, _, ha, haQy, hyR
      refine' ⟨_, _, _⟩
      simp; rw [← eq_Q] at xQy_in_S; simp at xQy_in_S yR_in_S; tauto
      rw [Nat.add_comm]; simp
    use a, x, y, z; constructor
    · constructor; assumption; constructor
      exact le_of_lt x_lt_y; assumption
    · tauto
  -- case label.Slope a b
  have b_lt_y : b < y := by
    have hQy := hxQy.tail; simp at hQy
    apply hQy.head?_lt_getLast? b y <;> simp
    rw [← eq_Q]; simp
  have hP := hPx.dropLast; simp at hP
  have hPb : C.NCup (n + 2) (P' ++ [a] ++ [b]) :=
    by
    apply hP.extend_right sab <;> try assumption
    simp <;> simp at Px_in_S <;> tauto
    simp
  by_cases sby : label.Slope b y; swap
  · have bz_laced : C.HasLaced (n + 3) S b z :=
      by
      have hbyR : C.NCup (n + 3) (b::y::R) := by
        apply hyR.extend_left sby <;> try assumption
        simp
      have hz : C.NCup 1 [z] := by simp
      exists _, _, _, _, _, hPb, hbyR, hz; rw [eq_R]
      refine' ⟨_, _, _⟩
      rw [eq_R] at yR_in_S; simp at Px_in_S yR_in_S; simp; tauto
      simp; simp
    use x, b, y, z; constructor
    constructor; assumption; constructor; apply le_of_lt; assumption; assumption
    tauto
  · have hPby : C.NCup (n + 3) (P' ++ [a] ++ [b] ++ [y]) :=
      by
      apply hPb.extend_right sby <;> try assumption
      simp <;> simp at Px_in_S <;> tauto; simp
    have P_nnil : P' ++ [a] ≠ [] := by simp
    rcases List.takeHead P_nnil with ⟨w, P_, eq_P_⟩
    rw [eq_P_] at hPby
    have wy_laced : C.HasLaced (n + 3) S w y :=
      by
      have hw : C.NCup 1 [w] := by simp
      exists _, _, _, _, _, hw, hPby, hyR
      refine' ⟨_, _, _⟩
      rw [eq_P_] at Px_in_S; simp at yR_in_S Px_in_S; simp; tauto
      rw [Nat.add_comm]; simp
    use w, x, y, z; constructor; constructor
    rw [eq_P_] at hPx; apply hPx.head?_lt_getLast? w x <;> simp
    constructor; exact le_of_lt x_lt_y; assumption; tauto

theorem Config.join_n2_n3_n2_tt (S : Finset α) (cap4_free : ¬C.HasNCap 4 S) {n : ℕ} (x y : α)
    {P : List α} (hPx : C.NCup (n + 2) (P ++ [x])) (Px_in_S : (P ++ [x]).In S) {Q : List α}
    (hxQy : C.NCup (n + 3) ((x::Q) ++ [y])) (xQy_in_S : ((x::Q) ++ [y]).In S) {R : List α}
    (hyR : C.NCup (n + 2) (y::R)) (yR_in_S : (y::R).In S) (label : C.Label S)
    (sxy : label.Slope x y) : ∃ p q r s, C.HasInterweavedLaced (n + 3) S p q r s :=
  by
  have Mirrored_goal : ∃ s r q p, C.Mirror.HasInterweavedLaced (n + 3) S.Mirror s r q p :=
    by
    rw [← Mirror.ncup] at hPx hxQy hyR; simp at hPx hxQy hyR
    rw [← Mirror.hasNCap] at cap4_free
    rw [← List.Mirror_in] at Px_in_S xQy_in_S yR_in_S
    simp [-List.cons_in, -List.append_in] at Px_in_S xQy_in_S yR_in_S
    have syx := sxy; rw [← Mirror_slope] at syx
    apply
        C.Mirror.join_n2_n3_n2_ff _ _ (toDual y) (toDual x) hyR _ hxQy _ hPx _ label.Mirror _ <;>
      assumption
  simp at Mirrored_goal
  rcases Mirrored_goal with ⟨s, r, q, p, h⟩
  rw [Mirror.hasInterweavedLaced] at h
  use p, q, r, s

theorem Config.join_n2_n3_n2 (S : Finset α) {n : ℕ} (cap4_free : ¬C.HasNCap 4 S)
    (cup_free : ¬C.HasNCup (n + 4) S) {cx : List α} (cx_ncup : C.NCup (n + 2) cx)
    (cx_in_S : cx.In S) {c : List α} (c_ncup : C.NCup (n + 3) c) (c_in_S : c.In S) {cy : List α}
    (cy_ncup : C.NCup (n + 2) cy) (cy_in_S : cy.In S) (x : α) (hxcx : x ∈ cx.getLast?)
    (hxc : x ∈ c.head?) (y : α) (hyc : y ∈ c.getLast?) (hycy : y ∈ cy.head?) :
    ∃ p q r s, C.HasInterweavedLaced (n + 3) S p q r s :=
  by
  rcases c_ncup.take_head_last with ⟨x, Q, y, eq_Q, Q_ncup⟩
  subst eq_Q; simp at hxc hyc; subst hxc; subst hyc
  rcases cx_ncup.dropLast_append_last with ⟨P, x, eq_P, P_ncup⟩
  subst eq_P; simp at hxcx; subst hxcx
  rcases cy_ncup.cons_head_tail with ⟨y, R, eq_R, R_ncup⟩
  subst eq_R; simp at hycy; subst hycy
  have label := cap4FreeLabel cap4_free
  by_cases sxy : label.Slope x y
  · apply C.join_n2_n3_n2_tt S <;> try assumption
  · apply C.join_n2_n3_n2_ff S <;> try assumption
