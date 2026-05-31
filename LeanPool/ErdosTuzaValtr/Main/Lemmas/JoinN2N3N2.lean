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

theorem Config.join_n2_n3_n2_ff (S : Finset α) (_cap4_free : ¬C.HasNCap 4 S) {n : ℕ} (x y : α)
    {P : List α} (hPx : C.NCup (n + 2) (P ++ [x])) (Px_in_S : (P ++ [x]).In S) {Q : List α}
    (hxQy : C.NCup (n + 3) ((x::Q) ++ [y])) (xQy_in_S : ((x::Q) ++ [y]).In S) {R : List α}
    (hyR : C.NCup (n + 2) (y::R)) (yR_in_S : (y::R).In S) (label : C.Label S)
    (sxy : ¬label.Slope x y) : ∃ p q r s, C.HasInterweavedLaced (n + 3) S p q r s := by
  have x_in_S : x ∈ S := xQy_in_S x (by simp)
  have y_in_S : y ∈ S := xQy_in_S y (by simp)
  have x_lt_y : x < y := hxQy.head_lt_getLast x y (by simp) (by simp)
  have hP : C.NCup (n + 1) P := by
    have := hPx.dropLast
    rwa [List.dropLast_concat] at this
  have hQy : C.NCup (n + 2) (Q ++ [y]) := by
    have := hxQy.tail
    rwa [List.cons_append, List.tail_cons] at this
  rcases hP.dropLast_append_last with ⟨P', a, eq_P, hP'⟩; subst eq_P
  rcases hQy.cons_head_tail with ⟨b, Q', eq_Q, hQ'⟩
  have eq_xQy : (x::Q) ++ [y] = x::(Q ++ [y]) := by simp
  rw [eq_xQy] at hxQy xQy_in_S; clear eq_xQy
  rw [eq_Q] at hxQy xQy_in_S
  have a_in_S : a ∈ S := Px_in_S a (by simp)
  have b_in_S : b ∈ S := xQy_in_S b (by simp)
  have hR : C.NCup (n + 1) R := by
    have := hyR.tail
    rwa [List.tail_cons] at this
  rcases hR.dropLast_append_last with ⟨R', z, eq_R, hR'⟩
  have hxQy_last : y ∈ (x :: b :: Q').getLast? := by
    rw [← eq_Q]
    rw [List.getLast?_cons_of_ne_nil (by simp), List.getLast?_append_of_ne_nil _ (by simp),
      List.getLast?_singleton]
    rfl
  have xy_laced : C.HasLaced (n + 3) S x y := by
    have hy : C.NCup 1 [y] := by simp
    refine ⟨n + 2, 1, _, _, _, hPx, hxQy, hy, ⟨Px_in_S, xQy_in_S, ?_⟩, by omega, ?_, ?_,
      hxQy_last, ?_⟩
    · rw [List.cons_in]; exact ⟨y_in_S, List.nil_in⟩
    · rw [List.getLast?_concat]; rfl
    · rw [List.head?_cons]; rfl
    · rw [List.head?_cons]; rfl
  have xz_laced : C.HasLaced (n + 3) S x z := by
    have hxyR : C.NCup (n + 3) (x::y::R) := hyR.extend_left sxy x_in_S x_lt_y yR_in_S (by simp)
    have hz : C.NCup 1 [z] := by simp
    have hxyz_last : z ∈ (x :: y :: R).getLast? := by
      rw [eq_R, List.getLast?_cons_of_ne_nil (by simp), List.getLast?_cons_of_ne_nil (by simp),
        List.getLast?_append_of_ne_nil _ (by simp), List.getLast?_singleton]
      rfl
    have hxyR_in : (x :: y :: R).In S := by
      rw [List.cons_in]; exact ⟨x_in_S, yR_in_S⟩
    refine ⟨n + 2, 1, _, _, _, hPx, hxyR, hz, ⟨Px_in_S, hxyR_in, ?_⟩, by omega, ?_, ?_,
      hxyz_last, ?_⟩
    · rw [List.cons_in]
      refine ⟨yR_in_S z (by rw [eq_R]; simp), List.nil_in⟩
    · rw [List.getLast?_concat]; rfl
    · rw [List.head?_cons]; rfl
    · rw [List.head?_cons]; rfl
  have a_lt_x : a < x := by
    have h_infix : [a, x] <:+: P' ++ [a] ++ [x] := ⟨P', [], by simp⟩
    exact List.isChain_pair.mp (hPx.left.left.infix h_infix)
  have x_lt_b : x < b := (List.isChain_cons_cons.mp hxQy.left.left).1
  have y_lt_z : y < z := by
    have hyR' : C.NCup (n + 2) (y :: (R' ++ [z])) := by rw [← eq_R]; exact hyR
    apply hyR'.head_lt_getLast y z (by simp)
    rw [List.getLast?_cons_of_ne_nil (by simp), List.getLast?_append_of_ne_nil _ (by simp),
      List.getLast?_singleton]
    rfl
  have a_lt_b : a < b := LT.lt.trans a_lt_x x_lt_b
  by_cases sab : label.Slope a b
  swap
  -- case ¬label.Slope a b
  · have hbQy : C.NCup (n + 2) (b :: Q') := by
      have := hxQy.tail
      rwa [List.tail_cons] at this
    have hbQy_in : (b :: Q').In S := fun w hw => xQy_in_S w (by rw [List.mem_cons]; right; exact hw)
    have haQy : C.NCup (n + 3) (a :: b :: Q') :=
      hbQy.extend_left sab a_in_S a_lt_b hbQy_in (by simp)
    have ha : C.NCup 1 [a] := by simp
    have ay_laced : C.HasLaced (n + 3) S a y := by
      have haQy_last : y ∈ (a :: b :: Q').getLast? := by
        rw [List.getLast?_cons_cons, ← eq_Q, List.getLast?_append_of_ne_nil _ (by simp),
          List.getLast?_singleton]
        rfl
      have haQy_in : (a :: b :: Q').In S := fun w hw =>
        (List.mem_cons.mp hw).elim (fun h => h ▸ a_in_S) (fun h => hbQy_in w h)
      refine ⟨1, n + 2, _, _, _, ha, haQy, hyR, ⟨?_, haQy_in, yR_in_S⟩, by omega, ?_, ?_,
        haQy_last, ?_⟩
      · rw [List.cons_in]; exact ⟨a_in_S, List.nil_in⟩
      · rw [List.getLast?_singleton]; rfl
      · rw [List.head?_cons]; rfl
      · rw [List.head?_cons]; rfl
    exact ⟨a, x, y, z, ⟨a_lt_x, le_of_lt x_lt_y, y_lt_z⟩, ay_laced, xz_laced⟩
  -- case label.Slope a b
  have b_lt_y : b < y := by
    have hbQy : C.NCup (n + 2) (b :: Q') := by
      have := hxQy.tail
      rwa [List.tail_cons] at this
    apply hbQy.head_lt_getLast b y (by simp)
    rw [← eq_Q, List.getLast?_append_of_ne_nil _ (by simp), List.getLast?_singleton]
    rfl
  have hPa_in : (P' ++ [a]).In S := fun w hw =>
    Px_in_S w (List.mem_append_left _ hw)
  have hPb : C.NCup (n + 2) (P' ++ [a] ++ [b]) :=
    hP.extend_right sab a_lt_b b_in_S hPa_in (by rw [List.getLast?_concat]; rfl)
  have hPb_in : (P' ++ [a] ++ [b]).In S := by
    rw [List.append_in, List.cons_in]
    exact ⟨hPa_in, b_in_S, List.nil_in⟩
  have hPb_last : b ∈ (P' ++ [a] ++ [b]).getLast? := by rw [List.getLast?_concat]; rfl
  by_cases sby : label.Slope b y
  swap
  · have bz_laced : C.HasLaced (n + 3) S b z := by
      have hbyR : C.NCup (n + 3) (b::y::R) := hyR.extend_left sby b_in_S b_lt_y yR_in_S (by simp)
      have hz : C.NCup 1 [z] := by simp
      have hbyR_in : (b :: y :: R).In S := fun w hw =>
        (List.mem_cons.mp hw).elim (fun h => h ▸ b_in_S) (fun h => yR_in_S w h)
      have hbyR_last : z ∈ (b :: y :: R).getLast? := by
        rw [eq_R, List.getLast?_cons_of_ne_nil (by simp), List.getLast?_cons_of_ne_nil (by simp),
          List.getLast?_append_of_ne_nil _ (by simp), List.getLast?_singleton]
        rfl
      refine ⟨n + 2, 1, _, _, _, hPb, hbyR, hz, ⟨hPb_in, hbyR_in, ?_⟩, by omega, hPb_last, ?_,
        hbyR_last, ?_⟩
      · rw [List.cons_in]
        exact ⟨yR_in_S z (by rw [eq_R]; simp), List.nil_in⟩
      · rw [List.head?_cons]; rfl
      · rw [List.head?_cons]; rfl
    exact ⟨x, b, y, z, ⟨x_lt_b, le_of_lt b_lt_y, y_lt_z⟩, xy_laced, bz_laced⟩
  · have hPby : C.NCup (n + 3) (P' ++ [a] ++ [b] ++ [y]) :=
      hPb.extend_right sby b_lt_y y_in_S hPb_in hPb_last
    have P_nnil : P' ++ [a] ≠ [] := by simp
    rcases List.takeHead P_nnil with ⟨w, P_, eq_P_⟩
    rw [eq_P_] at hPby
    have hPby_in : (w :: P_ ++ [b] ++ [y]).In S := by
      intro v hv
      rw [List.mem_append, List.mem_append] at hv
      rcases hv with (hv | hv) | hv
      · exact hPa_in v (by rw [eq_P_]; exact hv)
      · rw [List.mem_singleton] at hv; exact hv ▸ b_in_S
      · rw [List.mem_singleton] at hv; exact hv ▸ y_in_S
    have wy_laced : C.HasLaced (n + 3) S w y := by
      have hw : C.NCup 1 [w] := by simp
      have hw_in_S : w ∈ S := hPa_in w (by rw [eq_P_]; simp)
      have hPby_last : y ∈ (w :: P_ ++ [b] ++ [y]).getLast? := by rw [List.getLast?_concat]; rfl
      refine ⟨1, n + 2, _, _, _, hw, hPby, hyR, ⟨?_, hPby_in, yR_in_S⟩, by omega, ?_, ?_,
        hPby_last, ?_⟩
      · rw [List.cons_in]; exact ⟨hw_in_S, List.nil_in⟩
      · rw [List.getLast?_singleton]; rfl
      · rw [List.cons_append, List.cons_append, List.head?_cons]; rfl
      · rw [List.head?_cons]; rfl
    have w_lt_x : w < x := by
      rw [eq_P_] at hPx
      apply hPx.head_lt_getLast w x (by simp)
      rw [show w :: P_ ++ [x] = (w :: P_) ++ [x] by rfl, List.getLast?_concat]
      rfl
    exact ⟨w, x, y, z, ⟨w_lt_x, le_of_lt x_lt_y, y_lt_z⟩, wy_laced, xz_laced⟩

theorem Config.join_n2_n3_n2_tt (S : Finset α) (cap4_free : ¬C.HasNCap 4 S) {n : ℕ} (x y : α)
    {P : List α} (hPx : C.NCup (n + 2) (P ++ [x])) (Px_in_S : (P ++ [x]).In S) {Q : List α}
    (hxQy : C.NCup (n + 3) ((x::Q) ++ [y])) (xQy_in_S : ((x::Q) ++ [y]).In S) {R : List α}
    (hyR : C.NCup (n + 2) (y::R)) (yR_in_S : (y::R).In S) (label : C.Label S)
    (sxy : label.Slope x y) : ∃ p q r s, C.HasInterweavedLaced (n + 3) S p q r s :=
  by
  have Mirrored_goal : ∃ s r q p, C.Mirror.HasInterweavedLaced (n + 3) S.Mirror s r q p := by
    rw [← Mirror.ncup] at hPx hxQy hyR
    simp only [List.Mirror_append, List.Mirror_cons, List.Mirror_nil, List.nil_append,
      List.cons_append] at hPx hxQy hyR
    rw [← Mirror.hasNCap] at cap4_free
    rw [← List.Mirror_in] at Px_in_S xQy_in_S yR_in_S
    simp only [List.Mirror_append, List.Mirror_cons, List.Mirror_nil, List.nil_append,
      List.cons_append] at Px_in_S xQy_in_S yR_in_S
    have syx := sxy; rw [← Mirror_slope] at syx
    apply
        C.Mirror.join_n2_n3_n2_ff _ _ (toDual y) (toDual x) hyR _ hxQy _ hPx _ label.Mirror _ <;>
      assumption
  simp only [OrderDual.exists] at Mirrored_goal
  rcases Mirrored_goal with ⟨s, r, q, p, h⟩
  rw [Mirror.hasInterweavedLaced] at h
  use p, q, r, s

theorem Config.join_n2_n3_n2 (S : Finset α) {n : ℕ} (cap4_free : ¬C.HasNCap 4 S)
    (_cup_free : ¬C.HasNCup (n + 4) S) {cx : List α} (cx_ncup : C.NCup (n + 2) cx)
    (cx_in_S : cx.In S) {c : List α} (c_ncup : C.NCup (n + 3) c) (c_in_S : c.In S) {cy : List α}
    (cy_ncup : C.NCup (n + 2) cy) (cy_in_S : cy.In S) (x : α) (hxcx : x ∈ cx.getLast?)
    (hxc : x ∈ c.head?) (y : α) (hyc : y ∈ c.getLast?) (hycy : y ∈ cy.head?) :
    ∃ p q r s, C.HasInterweavedLaced (n + 3) S p q r s := by
  rcases c_ncup.take_head_last with ⟨x, Q, y, eq_Q, _⟩
  subst eq_Q
  rw [List.cons_append, List.head?_cons, Option.mem_some_iff] at hxc
  rw [List.getLast?_concat, Option.mem_some_iff] at hyc
  subst hxc; subst hyc
  rcases cx_ncup.dropLast_append_last with ⟨P, x, eq_P, _⟩
  subst eq_P
  rw [List.getLast?_concat, Option.mem_some_iff] at hxcx
  subst hxcx
  rcases cy_ncup.cons_head_tail with ⟨y, R, eq_R, _⟩
  subst eq_R
  rw [List.head?_cons, Option.mem_some_iff] at hycy
  subst hycy
  have label := cap4FreeLabel cap4_free
  by_cases sxy : label.Slope x y
  · exact C.join_n2_n3_n2_tt S cap4_free x y cx_ncup cx_in_S c_ncup c_in_S cy_ncup cy_in_S label sxy
  · exact C.join_n2_n3_n2_ff S cap4_free x y cx_ncup cx_in_S c_ncup c_in_S cy_ncup cy_in_S label sxy
