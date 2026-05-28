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

open scoped Classical

noncomputable section

variable {α : Type _} [LinearOrder α] (C : Config α)

namespace Config

def delta (n : ℕ) (S : Finset α) : Finset α :=
  S.filter fun p => C.beta S p < n ∧ p = (S.filter fun q => C.beta S q = C.beta S p).min

theorem delta_card (n : ℕ) (S : Finset α) : (C.delta n S).card ≤ n :=
  by
  rw [← Finset.card_range n]
  apply Finset.card_le_card_of_injOn (C.beta S)
  · rw [delta]; intro a; rw [Finset.mem_filter]
    intro h; rcases h with ⟨_, h', _⟩; simp at h' ⊢; exact h'
  · intro x hx y hy hxy
    rw [delta, Finset.mem_coe, Finset.mem_filter] at hx hy
    rcases hx with ⟨x_in_S, bx_lt_n, x_min⟩
    rcases hy with ⟨y_in_S, by_lt_n, y_min⟩
    rw [← WithTop.coe_eq_coe, x_min, y_min, hxy]

theorem not_mem_delta {n : ℕ} {S : Finset α} {p' : α} (h : p' ∈ S \ C.delta n S) :
    n ≤ C.beta S p' ∨ ∃ p, p ∈ C.delta n S ∧ C.beta S p = C.beta S p' ∧ p < p' :=
  by
  rw [delta, Finset.mem_sdiff, Finset.mem_filter, not_and, not_and_or] at h
  cases' h with p'_in_S aux; have h := aux p'_in_S; clear aux
  by_cases bp_n : C.beta S p' < n; swap
  · left; exact not_lt.mp bp_n
  rcases h with h | h; exact absurd bp_n h
  right
  set row := S.filter fun q => C.beta S q = C.beta S p' with def_row
  have row_nonempty : row.Nonempty := by
    use p'; rw [def_row]; rw [Finset.mem_filter]
    constructor; assumption; exact rfl
  have row_in_S : row ⊆ S := Finset.filter_subset _ _
  set p := row.min' row_nonempty with def_p
  have p_in_row : p ∈ row := Finset.min'_mem _ row_nonempty
  have bp_eq_bp' : C.beta S p = C.beta S p' :=
    by
    rw [def_row] at p_in_row; rw [Finset.mem_filter] at p_in_row
    exact p_in_row.right
  have p'_in_row : p' ∈ row := by
    rw [def_row]; rw [Finset.mem_filter]; constructor; assumption
    exact rfl
  exists p; refine' ⟨_, bp_eq_bp', _⟩
  · rw [delta]; simp only [Finset.mem_filter]
    rw [bp_eq_bp']; rw [← def_row]
    refine' ⟨row_in_S p_in_row, bp_n, _⟩
    rw [def_p]; exact Finset.coe_min' _
  · rw [← Finset.coe_min' row_nonempty] at h
    suffices p_le_p' : p ≤ p' by
      rw [le_iff_lt_or_eq] at p_le_p'
      rcases p_le_p' with p_lt_p' | p_eq_p'
      assumption; exfalso; apply h; rw [← def_p, p_eq_p']
    rw [def_p]; exact Finset.min'_le _ _ p'_in_row

theorem find_join {n : ℕ} {S : Finset α} (l : C.Label S) (cup_free : ¬C.HasNCup (n + 4) S)
    (no_join : ¬C.HasJoin (n + 3) (n + 2) S) (o p : α) (c : List α) (m : ℕ) (o_in_S : o ∈ S)
    (p_in_S : p ∈ S) (o_le_p : o ≤ p) (c_in_S : c.In S) (c_ncup : C.NCup m c) (c_head : p ∈ c.head?)
    (le_m : n + 2 ≤ m) (ho : n + 2 ≤ C.beta S o) : False :=
  by
  rw [le_iff_lt_or_eq] at o_le_p; cases' o_le_p with o_lt_p o_eq_p
  · rcases C.betaCup S o_in_S with ⟨d, d_in_S, d_ncup, d_last⟩
    by_cases sop : l.Slope o p
    · apply cup_free
      have dp_ncup := d_ncup.extend_right sop o_lt_p p_in_S d_in_S d_last
      have ineq : n + 4 ≤ C.beta S o + 1 + 1 := by linarith
      apply hasNCup_le ineq; use d ++ [p]
      constructor; exact dp_ncup; simp; tauto
    · apply no_join
      rcases d_ncup.take_right_with_last (n + 3) o (by simp) (by linarith) d_last with
        ⟨d', d'_in_d, d'_ncup, d'_last⟩
      have oc_ncup := c_ncup.extend_left sop o_in_S o_lt_p c_in_S c_head
      rcases oc_ncup.take_left_with_head (n + 2) o (by simp) (by linarith) (by simp) with
        ⟨c', c'_in_oc, c'_ncup, c'_head⟩
      use o, d', c'
      have d'_in_S := List.subset_in d'_in_d d_in_S
      have c'_in_S := List.subset_in c'_in_oc (by simp <;> tauto)
      tauto
  · subst o_eq_p; apply no_join
    rcases C.betaCup S o_in_S with ⟨d, d_in_S, d_ncup, d_last⟩
    rcases d_ncup.take_right_with_last (n + 3) o (by simp) (by linarith) d_last with
      ⟨d', d'_in_d, d'_ncup, d'_last⟩
    rcases c_ncup.take_left_with_head (n + 2) o (by simp) (by linarith) c_head with
      ⟨c', c'_in_c, c'_ncup, c'_head⟩
    use o, d', c'
    have d'_in_S := List.subset_in d'_in_d d_in_S
    have c'_in_S := List.subset_in c'_in_c c_in_S
    tauto

theorem laced_extension {n : ℕ} {S D : Finset α} (l : C.Label S) (cup_free : ¬C.HasNCup (n + 4) S)
    (def_D : D = C.delta (n + 2) S) (no_join : ¬C.HasJoin (n + 3) (n + 2) S) {p' r : α}
    (p'r_laced : C.HasLaced (n + 2) (S \ D) p' r) :
    l.alpha p' = 1 ∧
      ∃ p : α, C.HasLaced (n + 3) S p r ∧ p < p' ∧ l.alpha p = 0 ∧ C.beta S p = C.beta S p' :=
  by
  rcases p'r_laced with
    ⟨a, b, cp', c, cr, cp'_cup, c_cup, cr_cup, ⟨cp'_in_SD, c_in_SD, cr_in_SD⟩, eq_ab, cp'_last,
      c_head, c_last, cr_head⟩
  have p'_in_SD := c_in_SD _ (List.mem_of_mem_head? c_head)
  have p'_in_S := Finset.sdiff_subset p'_in_SD
  have c_in_S := List.in_superset Finset.sdiff_subset c_in_SD
  have cr_in_S := List.in_superset Finset.sdiff_subset cr_in_SD
  rw [def_D] at p'_in_SD
  rcases C.not_mem_delta p'_in_SD with (p'_beta | ⟨p, p_in_delta, eq_p, p_lt_p'⟩)
  · exfalso; apply C.find_join l cup_free no_join p' p' c <;> try assumption <;> try simp
    simp
    simp
  have p_in_S : p ∈ S := by rw [delta, Finset.mem_filter] at p_in_delta; exact p_in_delta.left
  have ap_lt_ap' := (l.beta_eq_alpha_inc p_in_S p'_in_S eq_p).mp p_lt_p'
  have ap' : l.alpha p' = 1 :=
    by
    cases' Nat.lt_or_ge (l.alpha p') 2 with ap' ap'; linarith
    exfalso; apply cup_free
    have has_cup := l.add_alpha p'_in_S c_in_S c_cup c_head
    apply hasNCup_le _ has_cup; linarith
  have ap : l.alpha p = 0 := by linarith
  refine' ⟨ap', ⟨p, _, p_lt_p', ap, eq_p⟩⟩
  · have a_le_bp : a ≤ C.beta S p := by
      rw [eq_p]
      -- Take the head o' of cp'
      have cp'_nnil : cp' ≠ [] := by intro h; subst h; simp at cp'_last
      rcases List.takeHead cp'_nnil with ⟨o', cp'', eq_cp'⟩
      have o'_le_p' : o' ≤ p' :=
        cp'_cup.head?_le_getLast? o' p' (by rw [eq_cp'] <;> simp) (by assumption)
      have o'_in_SD : o' ∈ S \ D := by apply cp'_in_SD <;> rw [eq_cp'] <;> simp
      have o'_in_S : o' ∈ S := Finset.sdiff_subset o'_in_SD
      rw [def_D] at o'_in_SD
      -- Locate o in delta having the same row as o'
      rcases C.not_mem_delta o'_in_SD with (le_beta | ⟨o, o_in_delta, eq_o, o_lt_o'⟩)
      · exfalso; apply C.find_join l cup_free no_join o' p' c <;> try assumption <;> try simp
        simp
      have o_in_S : o ∈ S := by
        rw [Config.delta] at o_in_delta <;> exact Finset.mem_of_mem_filter _ o_in_delta
      -- Show that the slope of o and o' is ff
      by_cases soo' : l.Slope o o'
      · have inc := slope_tt_inc_beta soo' o_in_S o'_in_S o_lt_o'
        rw [eq_o] at inc; simp at inc
      -- extend cp' to left with o
      have cp'_in_S := List.in_superset Finset.sdiff_subset cp'_in_SD
      have ocp'_cup : C.NCup (a + 1) (o::cp') :=
        by
        apply cp'_cup.extend_left soo' <;> try assumption
        rw [eq_cp']; simp
      apply Nat.le_of_add_le_add_right; rw [← ocp'_cup.right]
      apply C.cup_length_le_beta
      simp; constructor <;> assumption; exact ocp'_cup.left
      apply List.mem_getLast?_cons; assumption
    rw [Config.HasLaced]
    rcases C.betaCup S p_in_S with ⟨cp, cp_in_S, cp_cup, cp_last⟩
    rcases cp_cup.take_right_with_last (a + 1) p (by simp) (by linarith) cp_last with
      ⟨dp, dp_in_cp, dp_cup, dp_last⟩
    have dp_in_S : dp.In S := List.subset_in dp_in_cp cp_in_S
    have spp' : ¬l.Slope p p' := by
      intro spp'
      have ineq := slope_tt_inc_beta spp' p_in_S p'_in_S p_lt_p'; linarith
    have pc_cup := c_cup.extend_left spp' p_in_S p_lt_p' c_in_S c_head
    use a + 1, b, dp, p::c, cr, dp_cup, pc_cup, cr_cup
    refine'
        ⟨⟨_, by simp <;> tauto, _⟩, by linarith, _, by simp, List.mem_getLast?_cons c_last, _⟩ <;>
      assumption

theorem main_induction_wlog (n : ℕ) : C.MainGoal n → C.MainGoalWlog (n + 1) :=
  by
  intro ih S no_join S_card cap4_free cup_free
  have l : C.Label S := cap4FreeLabel cap4_free
  set D := C.delta (n + 2) S with def_D
  have D_card := C.delta_card (n + 2) S; rw [← def_D] at D_card
  have SD_card : (n + 2).choose 2 + 2 ≤ (S \ D).card :=
    by
    apply Nat.le_of_add_le_add_right
    rw [Finset.card_sdiff_add_card]
    apply le_trans _ (Finset.card_le_card Finset.subset_union_left)
    apply le_trans _ S_card
    apply le_trans (Nat.add_le_add_left D_card _) _
    rw [Nat.add_right_comm]; apply le_of_eq
    rw [Nat.add_right_comm n 1 2]; simp; apply symm; rw [Nat.choose]; simp
    rw [Nat.add_comm]
  have t := ih (S \ D) SD_card ?_ ?_
  swap;
  · intro h; rcases h with ⟨c, ⟨_, c_in⟩⟩
    apply cap4_free; use c; constructor; assumption
    apply List.in_superset _ c_in; exact Finset.sdiff_subset
  swap;
  · intro h; rcases h with ⟨c, ⟨c_cup, c_in⟩⟩
    rcases c_cup.cons_head_tail with ⟨p, c', eq_c, -⟩
    have p_in_c : p ∈ c := by rw [eq_c] <;> left <;> exact rfl
    have p_in_SD : p ∈ S \ D := c_in _ p_in_c
    rw [def_D] at p_in_SD
    have p_in_S : p ∈ S := Finset.sdiff_subset p_in_SD
    have c_in_S : c.In S := fun a ha => Finset.sdiff_subset (c_in a ha)
    rcases C.not_mem_delta p_in_SD with (le_bp | ⟨o, o_in_delta, bo_eq_bp, o_lt_p⟩)
    · apply C.find_join l cup_free no_join p p c <;> try assumption <;> try simp
      simp
      rw [eq_c]; simp
      simp
    · have o_in_S : o ∈ S := by
        rw [delta, Finset.mem_filter] at o_in_delta
        exact o_in_delta.left
      have ao_lt_ap := (l.beta_eq_alpha_inc o_in_S p_in_S bo_eq_bp).mp o_lt_p
      have has_cup := l.add_alpha p_in_S c_in_S c_cup (by rw [eq_c] <;> simp)
      apply cup_free; ring_nf at has_cup ⊢
      apply hasNCup_le _ has_cup; linarith
  · rcases t with ⟨p', q', r, s, ⟨⟨p'_lt_q', q'_le_r, r_lt_s⟩, ⟨p'r_laced, q's_laced⟩⟩⟩
    rcases C.laced_extension l cup_free def_D no_join p'r_laced with
      ⟨ap', ⟨p, pr_laced, p_lt_p', ap, bp⟩⟩
    rcases C.laced_extension l cup_free def_D no_join q's_laced with
      ⟨aq', ⟨q, qs_laced, q_lt_q', aq, bq⟩⟩
    rcases pr_laced.mem_ends with ⟨p_in_S, r_in_S⟩
    rcases qs_laced.mem_ends with ⟨q_in_S, s_in_S⟩
    have p'_in_S := Finset.sdiff_subset p'r_laced.mem_ends.left
    have q'_in_S := Finset.sdiff_subset q's_laced.mem_ends.left
    refine' ⟨p, q, r, s, ⟨⟨_, _, r_lt_s⟩, pr_laced, qs_laced⟩⟩
    · have ap_eq_aq := Eq.trans ap aq.symm
      rw [C.alpha_eq_beta_inc p_in_S q_in_S ap_eq_aq]
      rw [bp, bq]
      have ap'_eq_aq' := Eq.trans ap' aq'.symm
      rw [← C.alpha_eq_beta_inc p'_in_S q'_in_S ap'_eq_aq']
      exact p'_lt_q'
    · apply le_of_lt
      exact lt_of_lt_of_le q_lt_q' q'_le_r

end Config
