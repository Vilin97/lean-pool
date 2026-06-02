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

/-!
# LeanPool.ErdosTuzaValtr.Main.Lemmas.JoinN2N2

Imported Lean Pool material for `LeanPool.ErdosTuzaValtr.Main.Lemmas.JoinN2N2`.
-/

open OrderDual

variable {α : Type _} [LinearOrder α] (C : Config α)

theorem Config.join_n2_n2_case_ff (S : Finset α) (n : ℕ) (a x b : α) (c1 c2 : List α)
    (lab : C.Label S) (a_in_S : a ∈ S) (x_in_S : x ∈ S) (b_in_S : b ∈ S)
    (hc1 : C.NCup (n + 2) (c1 ++ [a, x])) (c1_in_S : c1.In S) (hc2 : C.NCup (n + 2) (x::b::c2))
    (c2_in_S : c2.In S) (sab : ¬lab.Slope a b) : C.HasNGon (n + 3) S := by
  have hax : a < x := by
    have h_infix : [a, x] <:+: c1 ++ [a, x] := ⟨c1, [], by simp⟩
    exact List.isChain_pair.mp (hc1.left.left.infix h_infix)
  have hxb : x < b := (List.isChain_cons_cons.mp hc2.left.left).1
  have hab : a < b := hax.trans hxb
  have h_b_c2 : (b::c2) ≠ [] := List.cons_ne_nil b c2
  rcases List.takeLast h_b_c2 with ⟨c, c3, eq_c2⟩
  have c_in_S : c ∈ S := by
    have h_in : (b::c2).In S := by rw [List.cons_in]; exact ⟨b_in_S, c2_in_S⟩
    rw [eq_c2] at h_in
    exact h_in c (by simp)
  have hc2' : C.NCup (n + 2) (x :: (c3 ++ [c])) := by rw [← eq_c2]; exact hc2
  have hc_last : c ∈ (x :: (c3 ++ [c])).getLast? := by
    rw [List.getLast?_cons_of_ne_nil (by simp), List.getLast?_append_of_ne_nil _ (by simp),
      List.getLast?_singleton]
    rfl
  have hxc : x < c := hc2'.head_lt_getLast x c (by simp) hc_last
  by_cases haxc : C.Cup3 a x c
  · apply ncup_is_ngon (by omega)
    refine ⟨c1 ++ [a, x, c], ⟨?_, ?_⟩, ?_⟩
    · rw [show c1 ++ [a, x, c] = c1 ++ a :: x :: c :: [] by simp, Config.Cup.append_cons3]
      exact ⟨hc1.left, haxc, by rw [Config.Cup.pair]; exact hxc⟩
    · rw [show c1 ++ [a, x, c] = c1 ++ [a, x] ++ [c] by simp, List.length_append, hc1.2,
        List.length_singleton]
    · rw [show c1 ++ [a, x, c] = c1 ++ [a, x] ++ [c] by simp, List.append_in, List.append_in,
        List.cons_in, List.cons_in, List.cons_in]
      exact ⟨⟨c1_in_S, a_in_S, x_in_S, List.nil_in⟩, c_in_S, List.nil_in⟩
  · have key : C.Cup (a :: (c3 ++ [c])) := by
      have hbc2 : C.Cup (b :: c2) := by rw [eq_c2]; exact hc2'.tail.left
      have hbc2_in : (b :: c2).In S := by rw [List.cons_in]; exact ⟨b_in_S, c2_in_S⟩
      rw [← eq_c2]
      exact hbc2.extend_left sab a_in_S hab hbc2_in (by simp)
    have key_in : (a :: (c3 ++ [c])).In S := by
      rw [List.cons_in]
      refine ⟨a_in_S, ?_⟩
      have h_in : (b::c2).In S := by rw [List.cons_in]; exact ⟨b_in_S, c2_in_S⟩
      rw [eq_c2] at h_in
      exact h_in
    refine ⟨[a, x, c], a :: (c3 ++ [c]), ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩, ?_, key_in⟩
    · simp
    · refine ⟨?_, ?_⟩
      · rw [List.isChain_cons_cons, List.isChain_cons_cons]
        exact ⟨hax, hxc, List.isChain_singleton c⟩
      · rw [show ([a, x, c] : List α) = [] ++ a :: x :: c :: [] by simp, List.chain3'_append_cons3]
        exact ⟨List.chain3'_pair a x, haxc, List.chain3'_pair x c⟩
    · simp
    · exact key
    · rw [List.head?_cons, List.head?_cons]
    · have hc_last2 : c ∈ (a :: (c3 ++ [c])).getLast? := by
        rw [List.getLast?_cons_of_ne_nil (by simp), List.getLast?_append_of_ne_nil _ (by simp),
          List.getLast?_singleton]
        rfl
      rw [Option.mem_def] at hc_last2
      rw [hc_last2]
      rfl
    · rw [show a :: (c3 ++ [c]) = a :: c3 ++ [c] by simp, List.length_append, List.length_cons,
        List.length_singleton, List.length_cons, List.length_cons, List.length_cons,
        List.length_nil]
      have hlen : (b :: c2).length = (c3 ++ [c]).length := by rw [eq_c2]
      rw [List.length_cons, List.length_append, List.length_singleton] at hlen
      have := hc2'.2
      rw [List.length_cons, List.length_append, List.length_singleton] at this
      omega
    · rw [List.cons_in, List.cons_in, List.cons_in]
      exact ⟨a_in_S, x_in_S, c_in_S, List.nil_in⟩

theorem Config.join_n2_n2_case_tt (S : Finset α) (n : ℕ) (a x b : α) (c1 c2 : List α)
    (lab : C.Label S) (a_in_S : a ∈ S) (x_in_S : x ∈ S) (b_in_S : b ∈ S)
    (hc1 : C.NCup (n + 2) (c1 ++ [a, x])) (c1_in_S : c1.In S) (hc2 : C.NCup (n + 2) (x::b::c2))
    (c2_in_S : c2.In S) (hab : lab.Slope a b) : C.HasNGon (n + 3) S :=
  by
  rw [← Finset.memMirror] at a_in_S x_in_S b_in_S
  rw [← Mirror.ncup] at hc1 hc2
  rw [← List.Mirror_in] at c1_in_S c2_in_S
  simp only [List.Mirror_append, List.Mirror_cons, List.Mirror_nil, List.nil_append,
    List.cons_append, List.append_assoc] at hc1 hc2
  have hba := hab; rw [← Mirror_slope] at hba
  have Mirrored_goal :=
    C.Mirror.join_n2_n2_case_ff S.Mirror n (toDual b) (toDual x) (toDual a) c2.Mirror c1.Mirror
      lab.Mirror b_in_S x_in_S a_in_S hc2 c2_in_S hc1 c1_in_S hba
  rw [Mirror.hasNGon] at Mirrored_goal
  tauto

theorem Config.join_n2_n2 (S : Finset α) {n : ℕ} (cap4_free : ¬C.HasNCap 4 S) {c1 : List α}
    (hc1 : C.NCup (n + 2) c1) (c1_in_S : c1.In S) {c2 : List α} (hc2 : C.NCup (n + 2) c2)
    (c2_in_S : c2.In S) (x : α) (hx1 : x ∈ c1.getLast?) (hx2 : x ∈ c2.head?) :
    C.HasNGon (n + 3) S := by
  -- Introduce variables
  have c1_size2 : 2 ≤ c1.length := by rw [hc1.2]; omega
  rcases List.takeLast2 c1_size2 with ⟨a, x, c1', eq_c1⟩
  subst eq_c1
  rw [List.getLast?_append_cons, List.getLast?_cons_cons, List.getLast?_singleton,
    Option.mem_some_iff] at hx1
  subst hx1
  have c2_size2 : 2 ≤ c2.length := by rw [hc2.2]; omega
  rcases List.takeHead2 c2_size2 with ⟨x, b, c2', eq_c2⟩
  subst eq_c2
  rw [List.head?_cons, Option.mem_some_iff] at hx2
  subst hx2
  rw [List.append_in, List.cons_in, List.cons_in] at c1_in_S
  rw [List.cons_in, List.cons_in] at c2_in_S
  have lab := cap4FreeLabel cap4_free
  by_cases hl : lab.Slope a b
  · exact C.join_n2_n2_case_tt S n a x b c1' c2' lab c1_in_S.2.1 c1_in_S.2.2.1 c2_in_S.2.1
      hc1 c1_in_S.1 hc2 c2_in_S.2.2 hl
  · exact C.join_n2_n2_case_ff S n a x b c1' c2' lab c1_in_S.2.1 c1_in_S.2.2.1 c2_in_S.2.1
      hc1 c1_in_S.1 hc2 c2_in_S.2.2 hl
