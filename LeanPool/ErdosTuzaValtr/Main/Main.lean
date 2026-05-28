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

open scoped Classical

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

theorem Config.main_lemma (n : ℕ) : C.MainGoal n :=
  by
  induction' n with n ih
  · intro S hS cap4_free cup_free; simp at hS
    set Sl := S.sort (· ≤ ·) with def_Sl
    have Sl_card : 3 ≤ Sl.length := by rw [def_Sl] <;> simp <;> exact hS
    have mem_Sl : ∀ {a : γ}, a ∈ Sl ↔ a ∈ S := by
      intro a; rw [def_Sl];
      exact Finset.mem_sort (· ≤ ·)
    -- Take three elements of S
    rcases List.takeHead3 Sl_card with ⟨a, b, c, Sl', eq_Sl⟩
    have abc_mem : a ∈ S ∧ b ∈ S ∧ c ∈ S := by
      rw [← mem_Sl, ← mem_Sl, ← mem_Sl] <;> rw [eq_Sl] <;> simp
    have abc_lt : a < b ∧ b < c := by
      have sorted := S.sort_sorted_lt
      rw [← def_Sl, eq_Sl] at sorted
      simp at sorted; tauto
    refine' ⟨a, b, b, c, _, ⟨_, _⟩⟩
    exact ⟨abc_lt.left, le_refl b, abc_lt.right⟩
    use 1, 1, [a], [a, b], [b]; simp; tauto
    use 1, 1, [b], [b, c], [c]; simp; tauto
  · intro S hS cap4_free cup_free
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

theorem main (n : ℕ) (C : Config γ) (S : Finset γ) (hS : Nat.choose (n + 2) 2 + 2 ≤ S.card) :
    C.HasNCap 4 S ∨ C.HasNGon (n + 3) S :=
  by
  by_cases has_cap4 : C.HasNCap 4 S; left; exact has_cap4
  by_cases has_cup : C.HasNCup (n + 3) S
  · right; apply ncup_is_ngon _ has_cup; simp
  rcases C.main_lemma n S hS has_cap4 has_cup with ⟨p, q, r, s, laced⟩
  right; exact C.hasInterweavedLaced_hasNGon has_cap4 laced
