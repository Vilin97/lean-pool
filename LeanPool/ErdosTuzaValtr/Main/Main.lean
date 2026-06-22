/-
Copyright (c) 2026 Jineon Baek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jineon Baek
-/

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Finset.Basic
import LeanPool.ErdosTuzaValtr.Config.Default
import LeanPool.ErdosTuzaValtr.Etv.Default
import LeanPool.ErdosTuzaValtr.Main.Defs
import LeanPool.ErdosTuzaValtr.Main.Lemmas.Default
import LeanPool.ErdosTuzaValtr.Main.InductionStep

/-!
# LeanPool.ErdosTuzaValtr.Main.Main

Imported Lean Pool material for `LeanPool.ErdosTuzaValtr.Main.Main`.
-/

noncomputable section

variable {γ : Type _} [LinearOrder γ] (C : Config γ)

open OrderDual

theorem Config.Mirror_mainGoal (n : ℕ) : C.MainGoal n → C.Mirror.MainGoal n :=
  by
  intro h Sm hSm cap4_free cup_free
  have eq_S : Sm.ofMirror.Mirror = Sm := Finset.ofMirrorMirror
  rw [← eq_S] at hSm cap4_free cup_free ⊢
  set S := Sm.ofMirror
  rw [Finset.Mirror_card] at hSm
  rw [Mirror.hasNCap] at cap4_free
  rw [Mirror.hasNCup] at cup_free
  have goal := h S hSm cap4_free cup_free
  rcases goal with ⟨p, q, r, s, interweave⟩
  exists toDual s, toDual r, toDual q, toDual p
  rw [Mirror.hasInterweavedLaced]
  exact interweave

private theorem hasLaced_pair {S : Finset γ} {x y : γ} (x_mem : x ∈ S) (y_mem : y ∈ S)
    (hxy : x < y) : C.HasLaced (0 + 2) S x y := by
  refine ⟨1, 1, [x], [x, y], [y], by simp, Config.NCup.pair.mpr hxy, by simp,
    ⟨?_, ?_, ?_⟩, by omega, ?_, ?_, ?_, ?_⟩
  · rw [List.cons_in]; exact ⟨x_mem, List.nil_in⟩
  · rw [List.cons_in, List.cons_in]; exact ⟨x_mem, y_mem, List.nil_in⟩
  · rw [List.cons_in]; exact ⟨y_mem, List.nil_in⟩
  · rw [List.getLast?_singleton]; rfl
  · rw [List.head?_cons]; rfl
  · rw [List.getLast?_cons_cons, List.getLast?_singleton]; rfl
  · rw [List.head?_cons]; rfl

theorem Config.main_lemma (n : ℕ) : C.MainGoal n := by
  induction n with
  | zero =>
    intro S hS cap4_free cup_free
    rw [Nat.choose_self] at hS
    set Sl := S.sort (· ≤ ·) with def_Sl
    have Sl_card : 3 ≤ Sl.length := by rw [def_Sl, Finset.length_sort]; omega
    have mem_Sl : ∀ {a : γ}, a ∈ Sl ↔ a ∈ S := by
      intro a
      rw [def_Sl, Finset.mem_sort]
    -- Take three elements of S
    rcases List.takeHead3 Sl_card with ⟨a, b, c, Sl', eq_Sl⟩
    have a_mem : a ∈ S := by rw [← mem_Sl, eq_Sl]; simp
    have b_mem : b ∈ S := by rw [← mem_Sl, eq_Sl]; simp
    have c_mem : c ∈ S := by rw [← mem_Sl, eq_Sl]; simp
    have abc_lt : a < b ∧ b < c := by
      have sorted : Sl.Pairwise (· < ·) := (Finset.sortedLT_sort S).pairwise
      rw [eq_Sl, List.pairwise_cons, List.pairwise_cons] at sorted
      exact ⟨sorted.1 b (by simp), sorted.2.1 c (by simp)⟩
    have laced1 := hasLaced_pair C a_mem b_mem abc_lt.left
    have laced2 := hasLaced_pair C b_mem c_mem abc_lt.right
    exact ⟨a, b, b, c, ⟨abc_lt.left, le_refl b, abc_lt.right⟩, laced1, laced2⟩
  | succ n ih =>
    intro S hS cap4_free cup_free
    by_cases join_n3_n2 : C.HasJoin (n + 3) (n + 2) S; swap
    · apply C.main_induction_wlog <;> assumption
    by_cases join_n2_n3 : C.HasJoin (n + 2) (n + 3) S; swap
    · rw [← Finset.Mirror_card] at hS
      rw [← Mirror.hasJoin] at join_n2_n3
      rw [← Mirror.hasNCap] at cap4_free
      rw [← Mirror.hasNCup] at cup_free
      have Mirrored_goal :=
        C.Mirror.main_induction_wlog n (C.Mirror_mainGoal n ih) S.Mirror join_n2_n3 hS cap4_free
          cup_free
      rcases Mirrored_goal with ⟨sm, rm, qm, pm, mgoal⟩
      have eq_p := pm.toDual_ofDual; set p := ofDual pm
      have eq_q := qm.toDual_ofDual; set q := ofDual qm
      have eq_r := rm.toDual_ofDual; set r := ofDual rm
      have eq_s := sm.toDual_ofDual; set s := ofDual sm
      exists p, q, r, s
      rw [← eq_p, ← eq_q, ← eq_r, ← eq_s, Mirror.hasInterweavedLaced] at mgoal
      assumption
    apply C.join_n2_n3_join_n3_n2 <;> assumption

namespace ErdosTuzaValtr

theorem main (n : ℕ) (C : Config γ) (S : Finset γ) (hS : Nat.choose (n + 2) 2 + 2 ≤ S.card) :
    C.HasNCap 4 S ∨ C.HasNGon (n + 3) S := by
  by_cases has_cap4 : C.HasNCap 4 S
  · left; exact has_cap4
  by_cases has_cup : C.HasNCup (n + 3) S
  · right; exact ncup_is_ngon (by omega) has_cup
  rcases C.main_lemma n S hS has_cap4 has_cup with ⟨p, q, r, s, laced⟩
  right
  exact C.hasInterweavedLaced_hasNGon has_cap4 laced

end ErdosTuzaValtr
