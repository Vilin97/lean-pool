/-
Copyright (c) 2026 Jineon Baek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jineon Baek
-/

import Mathlib.Order.Basic
import LeanPool.ErdosTuzaValtr.Lib.List.Default
import LeanPool.ErdosTuzaValtr.Etv.Default
import LeanPool.ErdosTuzaValtr.Main.Lemmas.JoinN2N2

open OrderDual

variable {α : Type _} [LinearOrder α] (C : Config α)

theorem Config.hasInterweavedLaced_hasNGon_ff {n : ℕ} {S : Finset α} (cap4_free : ¬C.HasNCap 4 S)
    {p q r s : α} (label : C.Label S) (q_lt_r : q < r) (sqr : ¬label.Slope q r) :
    C.HasInterweavedLaced (n + 2) S p q r s → C.HasNGon (n + 3) S :=
  by
  intro h; rcases h with ⟨⟨p_lt_q, q_le_r, r_lt_s⟩, ⟨pr_laced, qs_laced⟩⟩
  rcases pr_laced with
    ⟨a, b, cp, c1, cr, hcp, hc1, hcr,
      ⟨⟨cp_in_S, c1_in_S, cr_in_S⟩, eq_ab, cp_last, c1_head, c1_last, cr_head⟩⟩
  rcases qs_laced with
    ⟨c, d, cq, c2, cs, hcq, hc2, hcs,
      ⟨⟨cq_in_S, c2_in_S, cs_in_S⟩, eq_cd, cq_last, c2_head, c2_last, cs_head⟩⟩
  have p_in_S : p ∈ S := by
    apply c1_in_S
    exact List.mem_of_mem_head? c1_head
  have q_in_S : q ∈ S := by
    apply c2_in_S
    exact List.mem_of_mem_head? c2_head
  have r_in_S : r ∈ S := by
    apply c1_in_S
    exact List.mem_of_mem_getLast? c1_last
  have s_in_S : s ∈ S := by
    apply c2_in_S
    exact List.mem_of_mem_getLast? c2_last
  have label := cap4FreeLabel cap4_free
  by_cases spq : label.Slope p q; swap
  · apply ncup_is_ngon; linarith
    use p::c2; constructor
    apply hc2.extend_left spq <;> assumption
    simp; tauto
  -- (spq : ¬label.Slope p q) from now on
  by_cases cpqr : C.Cup3 p q r
  · apply ncup_is_ngon; linarith
    use cp ++ q::cr; constructor; swap; simp; tauto
    have cp_nnil : cp ≠ [] := by intro h; subst h; simp at cp_last
    rcases List.takeLast cp_nnil with ⟨p, cp', eq_cp⟩
    rw [eq_cp] at cp_last; simp at cp_last; subst cp_last
    -- idea: implement a lemma for taking explicit head
    -- from a statement like this
    have cr_nnil : cr ≠ [] := by intro h; subst h; simp at cr_head
    rcases List.takeHead cr_nnil with ⟨r, cr', eq_cr⟩; constructor
    rw [eq_cr] at cr_head; simp at cr_head; subst cr_head
    rw [eq_cp, eq_cr]; simp
    refine' ⟨_, _, _⟩; swap; assumption
    have eq : cp' ++ [p, q] = cp' ++ [p] ++ [q] := by simp
    rw [eq]; rw [← eq_cp]
    apply hcp.left.extend_right spq <;> try assumption
    rw [eq_cp]; simp
    rw [← eq_cr]
    apply hcr.left.extend_left sqr <;> try assumption
    rw [eq_cr]; simp
    simp; rw [hcp.right, hcr.right]; linarith
  · use[p, q, r], c1; constructor; swap; simp; tauto
    constructor; swap; rw [hc1.right]; simp; linarith
    rw [Config.Gon]; simp
    cases' hc1 with c1_cup c1_length; rw [c1_length]
    simp at c1_head c1_last
    have h2n : 2 ≤ n + 2 := le_add_self; tauto

theorem Config.hasInterweavedLaced_hasNGon_tt {n : ℕ} {S : Finset α} (cap4_free : ¬C.HasNCap 4 S)
    {p q r s : α} (label : C.Label S) (q_lt_r : q < r) (sqr : label.Slope q r) :
    C.HasInterweavedLaced (n + 2) S p q r s → C.HasNGon (n + 3) S :=
  by
  rw [← Mirror.hasInterweavedLaced, ← Mirror.hasNGon]
  have srq := sqr; rw [← Mirror_slope] at srq
  rw [← Mirror.hasNCap] at cap4_free
  apply C.Mirror.hasInterweavedLaced_hasNGon_ff <;> assumption

theorem Config.hasInterweavedLaced_hasNGon {n : ℕ} {S : Finset α} (cap4_free : ¬C.HasNCap 4 S)
    {p q r s : α} : C.HasInterweavedLaced (n + 2) S p q r s → C.HasNGon (n + 3) S :=
  by
  intro h; have q_le_r : q ≤ r := by rw [Config.HasInterweavedLaced] at h <;> tauto
  rw [le_iff_eq_or_lt] at q_le_r
  rcases q_le_r with q_eq_r | q_lt_r
  · subst q_eq_r; rcases h with ⟨-, pr_laced, qs_laced⟩
    rcases pr_laced with ⟨-, -, -, c1, -, -, hc1, -, ⟨-, c1_in_S, -⟩, -, ⟨-, c1_head, c1_last, -⟩⟩
    rcases qs_laced with ⟨-, -, -, c2, -, -, hc2, -, ⟨-, c2_in_S, -⟩, -, ⟨-, c2_head, c2_last, -⟩⟩
    apply C.join_n2_n2 S cap4_free hc1 c1_in_S hc2 c2_in_S q c1_last c2_head
  have label := cap4FreeLabel cap4_free
  by_cases sqr : label.Slope q r
  · revert h
    apply C.hasInterweavedLaced_hasNGon_tt <;> assumption
  · revert h
    apply C.hasInterweavedLaced_hasNGon_ff <;> assumption
