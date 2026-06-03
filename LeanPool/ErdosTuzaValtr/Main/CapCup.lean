/-
Copyright (c) 2026 Jineon Baek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jineon Baek
-/

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.Ring.RingNF
import LeanPool.ErdosTuzaValtr.Config.Default
import LeanPool.ErdosTuzaValtr.Etv.Default

/-!
# LeanPool.ErdosTuzaValtr.Main.CapCup

Imported Lean Pool material for `LeanPool.ErdosTuzaValtr.Main.CapCup`.
-/

noncomputable section

namespace Config

variable {α : Type _} [LinearOrder α] (C : Config α)

theorem has_cap2_cup2 {S : Finset α} (hS : 1 < S.card) : C.HasNCap 2 S ∧ C.HasNCup 2 S := by
  set l := S.sort (· ≤ ·) with eq_l
  have hl : 2 ≤ l.length := by rw [eq_l, Finset.length_sort]; exact hS
  rcases List.takeHead2 hl with ⟨a, b, t, eq_ab⟩
  have sorted : l.Pairwise (· < ·) := (Finset.sortedLT_sort S).pairwise
  rw [eq_ab] at sorted
  have a_lt_b : a < b := (List.pairwise_cons.mp sorted).1 b (by simp)
  have a_in_S : a ∈ S := by
    have : a ∈ l := by rw [eq_ab]; simp
    rwa [eq_l, Finset.mem_sort] at this
  have b_in_S : b ∈ S := by
    have : b ∈ l := by rw [eq_ab]; simp
    rwa [eq_l, Finset.mem_sort] at this
  refine ⟨⟨[a, b], ⟨?_, rfl⟩, ?_⟩, ⟨[a, b], ⟨?_, rfl⟩, ?_⟩⟩
  · rw [Cap.pair]; exact a_lt_b
  · rw [List.cons_in, List.cons_in]; exact ⟨a_in_S, b_in_S, List.nil_in⟩
  · rw [Cup.pair]; exact a_lt_b
  · rw [List.cons_in, List.cons_in]; exact ⟨a_in_S, b_in_S, List.nil_in⟩

theorem binom_eq (a b : ℕ) :
    (a + b + 2).choose (a + 1) = (a + b + 1).choose a + (a + b + 1).choose (a + 1) :=
  rfl

theorem cap_cup (a b : ℕ) (S : Finset α) (hS : Nat.choose (a + b) a < S.card) :
    C.HasNCap (a + 2) S ∨ C.HasNCup (b + 2) S := by
  classical
  revert a b S hS
  refine Nat.pincerRecursion ?_ ?_ ?_
  -- case b = 0
  · intro a S hS
    rw [Nat.add_zero, Nat.choose_self] at hS
    right
    exact (C.has_cap2_cup2 hS).right
  -- case a = 0
  · intro a S hS
    rw [Nat.zero_add, Nat.choose_zero_right] at hS
    left
    exact (C.has_cap2_cup2 hS).left
  -- diagonal induction
  · intro a b
    set sz_ab1 := (a + (b + 1)).choose a with eq_sz_ab1
    set sz_a1b := (a + 1 + b).choose (a + 1) with eq_sz_a1b
    set sz_a1b1 := (a + 1 + (b + 1)).choose (a + 1) with eq_sz_a1b1
    have eq_sz : sz_a1b1 = sz_ab1 + sz_a1b := by
      rw [eq_sz_ab1, eq_sz_a1b, eq_sz_a1b1]
      rw [show a + 1 + (b + 1) = (a + (b + 1)) + 1 by ring,
        show a + 1 + b = a + (b + 1) by ring, Nat.choose_succ_succ (a + (b + 1)) a]
    -- numerical details now not relevant
    clear eq_sz_ab1 eq_sz_a1b eq_sz_a1b1
    intro hab1 ha1b S hS
    set is_start_of_cap : α → Prop := fun p =>
      ∃ c, C.Cap c ∧ c.In S ∧ c.length = a + 2 ∧ p ∈ c.head? with def_is_start_of_cap
    set T := Finset.filter is_start_of_cap S with def_T
    have eq_card : (S \ T).card + T.card = S.card :=
      by
      apply Finset.card_sdiff_add_card_eq_card
      rw [def_T]; exact S.filter_subset is_start_of_cap
    have sz_cases : sz_ab1 < (S \ T).card ∨ sz_a1b < T.card := by by_contra! h; omega
    rcases sz_cases with sz_cases | sz_cases
    -- case sz_ab1 < (S \ T).card
    · rcases hab1 (S \ T) sz_cases with hcap | hcup
      · rcases hcap with ⟨c, ⟨c_cap, c_length⟩, c_in⟩
        have c_nnil : c ≠ [] := by
          intro eq_c
          subst eq_c
          simp only [List.length_nil] at c_length
          omega
        rcases List.takeHead c_nnil with ⟨ch, ct, eq_c⟩
        have h : ch ∈ S \ T := c_in ch (by rw [eq_c]; simp)
        rw [def_T, Finset.mem_sdiff, Finset.mem_filter] at h
        obtain ⟨c_in_S, h⟩ := h
        exfalso
        apply h
        refine ⟨c_in_S, c, c_cap, ?_, ?_, ?_⟩
        · intro x hx
          exact Finset.sdiff_subset (c_in x hx)
        · rw [c_length]
        · rw [eq_c]; simp
      · right
        refine hasNCup_supset ?_ hcup
        exact Finset.sdiff_subset
    -- case sz_a1b < T.card
    · rcases ha1b T sz_cases with hcap | hcup
      · left
        refine hasNCap_supset ?_ hcap
        rw [def_T]
        exact Finset.filter_subset _ _
      · rcases hcup with ⟨cl, ⟨cl_cup, cl_length⟩, cl_in_T⟩
        have cl_sz2 : 2 ≤ cl.length := by rw [cl_length]; omega
        rcases List.takeLast2 cl_sz2 with ⟨p, q, cl', eq_cl⟩
        clear cl_sz2
        have q_in_T : q ∈ T := cl_in_T q (by rw [eq_cl]; simp)
        rw [def_T, Finset.mem_filter] at q_in_T
        obtain ⟨q_in_S, q_st⟩ := q_in_T
        rcases q_st with ⟨cr, cr_cap, cr_in_S, cr_length, cr_head⟩
        have cr_sz2 : 2 ≤ cr.length := by rw [cr_length]; omega
        rcases List.takeHead2 cr_sz2 with ⟨q', r, cr', eq_cr⟩
        clear cr_sz2
        rw [eq_cr, List.head?_cons, Option.mem_some_iff] at cr_head
        subst q'
        by_cases hpqr : C.Cup3 p q r
        · right
          refine ⟨cl ++ [r], ⟨?_, ?_⟩, ?_⟩
          · rw [eq_cl, List.append_assoc]
            rw [show [p, q] ++ [r] = [p, q, r] from rfl, Cup.append_cons3]
            rw [eq_cr] at cr_cap
            refine ⟨?_, ?_, ?_⟩
            · rw [← eq_cl]; exact cl_cup
            · exact hpqr
            · rw [Cup.pair]; exact cr_cap.left.rel_head
          · rw [List.length_append, List.length_singleton, cl_length]
          · rw [List.append_in, List.cons_in]
            refine ⟨?_, ?_, List.nil_in⟩
            · exact List.in_superset (by rw [def_T]; exact Finset.filter_subset _ _) cl_in_T
            · rw [eq_cr, List.cons_in, List.cons_in] at cr_in_S
              exact cr_in_S.2.1
        · left
          refine ⟨p::cr, ⟨?_, ?_⟩, ?_⟩
          · rw [eq_cr]
            rw [show p :: q :: r :: cr' = [] ++ p :: q :: r :: cr' from rfl, Cap.append_cons3]
            refine ⟨?_, hpqr, ?_⟩
            · rw [List.nil_append, Cap.pair]
              rw [eq_cl] at cl_cup
              have h_infix : [p, q] <:+: cl' ++ [p, q] := ⟨cl', [], by simp⟩
              exact List.isChain_pair.mp (cl_cup.left.infix h_infix)
            · rw [eq_cr] at cr_cap
              exact cr_cap
          · rw [List.length_cons, cr_length]
          · rw [List.cons_in]
            refine ⟨?_, cr_in_S⟩
            apply Finset.filter_subset is_start_of_cap
            rw [← def_T]
            exact cl_in_T p (by rw [eq_cl]; simp)

end Config
