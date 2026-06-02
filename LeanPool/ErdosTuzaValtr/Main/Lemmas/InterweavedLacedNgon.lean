/-
Copyright (c) 2026 Jineon Baek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jineon Baek
-/

import Mathlib.Order.Basic
import LeanPool.ErdosTuzaValtr.Lib.List.Default
import LeanPool.ErdosTuzaValtr.Etv.Default
import LeanPool.ErdosTuzaValtr.Main.Lemmas.JoinN2N2

/-!
# LeanPool.ErdosTuzaValtr.Main.Lemmas.InterweavedLacedNgon

Imported Lean Pool material for `LeanPool.ErdosTuzaValtr.Main.Lemmas.InterweavedLacedNgon`.
-/

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
  by_cases spq : label.Slope p q
  swap
  · apply ncup_is_ngon (by omega)
    refine ⟨p :: c2, hc2.extend_left spq p_in_S p_lt_q c2_in_S c2_head, ?_⟩
    rw [List.cons_in]
    exact ⟨p_in_S, c2_in_S⟩
  -- (spq : label.Slope p q) from now on
  have cp_nnil : cp ≠ [] := by
    rintro rfl
    exact absurd cp_last (Option.not_mem_none p)
  rcases List.takeLast cp_nnil with ⟨p', cp', eq_cp⟩
  rw [eq_cp, List.getLast?_concat, Option.mem_some_iff] at cp_last
  subst p'
  have cr_nnil : cr ≠ [] := by
    rintro rfl
    exact absurd cr_head (Option.not_mem_none r)
  rcases List.takeHead cr_nnil with ⟨r', cr', eq_cr⟩
  rw [eq_cr, List.head?_cons, Option.mem_some_iff] at cr_head
  subst r'
  have cp_last' : p ∈ cp.getLast? := by rw [eq_cp, List.getLast?_concat]; rfl
  have cr_head' : r ∈ cr.head? := by rw [eq_cr, List.head?_cons]; rfl
  by_cases cpqr : C.Cup3 p q r
  · apply ncup_is_ngon (by omega)
    refine ⟨cp ++ q :: cr, ?_, ?_⟩
    · rw [Config.NCup]
      refine ⟨?_, ?_⟩
      · rw [eq_cp, eq_cr,
          show (cp' ++ [p]) ++ q :: r :: cr' = cp' ++ p :: q :: r :: cr' by simp,
          Config.Cup.append_cons3]
        refine ⟨?_, cpqr, ?_⟩
        · rw [show cp' ++ [p, q] = (cp' ++ [p]) ++ [q] by simp, ← eq_cp]
          exact hcp.left.extend_right spq p_lt_q q_in_S cp_in_S cp_last'
        · rw [← eq_cr]
          exact hcr.left.extend_left sqr q_in_S q_lt_r cr_in_S cr_head'
      · rw [List.length_append, List.length_cons, hcp.2, hcr.2]
        omega
    · rw [List.append_in, List.cons_in]
      exact ⟨cp_in_S, q_in_S, cr_in_S⟩
  · refine ⟨[p, q, r], c1, ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩, ?_, c1_in_S⟩
    · simp
    · refine ⟨?_, ?_⟩
      · rw [List.isChain_cons_cons, List.isChain_cons_cons]
        exact ⟨p_lt_q, q_lt_r, List.isChain_singleton r⟩
      · rw [show ([p, q, r] : List α) = [] ++ p :: q :: r :: [] by simp,
          List.chain3'_append_cons3]
        exact ⟨List.chain3'_pair p q, cpqr, List.chain3'_pair q r⟩
    · rw [hc1.2]; omega
    · exact hc1.left
    · rw [List.head?_cons]; exact c1_head.symm
    · rw [List.getLast?_cons_cons, List.getLast?_cons_cons, List.getLast?_singleton]
      exact c1_last.symm
    · simp only [List.length_cons, List.length_nil]
      rw [hc1.2]; omega
    · rw [List.cons_in, List.cons_in, List.cons_in]
      exact ⟨p_in_S, q_in_S, r_in_S, List.nil_in⟩

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
  intro h; have q_le_r : q ≤ r := by rw [Config.HasInterweavedLaced] at h; tauto
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
