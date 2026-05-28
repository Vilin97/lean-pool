/-
Copyright (c) 2026 Jineon Baek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jineon Baek
-/

import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Sublists
import Mathlib.Data.List.Chain
import LeanPool.ErdosTuzaValtr.Etv.Defs
import LeanPool.ErdosTuzaValtr.Etv.Label

open scoped Classical

noncomputable section

variable {α : Type _} [LinearOrder α] {C : Config α} {S : Finset α} (l : C.Label S)

private theorem mem_imply_nnil {α : Type _} (a : α) {l : List α} (ha : a ∈ l) : l ≠ [] := by
  intro eq; subst eq; simp at ha

namespace Config.Label

def IsAlphaCup (a : α) (c : List α) : Prop :=
  (c ++ [a]).In S ∧ (c ++ [a]).Sorted (· < ·) ∧ (c ++ [a]).Chain' (l.Slopeᶜ)

theorem alphaCup_is_cup (c : List α) (c_in_S : c.In S) (c_sorted : c.Sorted (· < ·))
    (c_chain : c.Chain' (l.Slopeᶜ)) : C.Cup c :=
  by
  induction' c with h0 c ih; simp
  cases' c with h1 c; simp
  cases' c with h2 c
  · simp; simp at c_sorted; assumption
  simp; refine' ⟨_, _, _⟩
  simp at c_sorted <;> tauto
  simp at c_in_S c_chain c_sorted <;> apply l.extend_left <;> tauto
  apply ih <;> simp at c_in_S c_chain c_sorted ⊢ <;> tauto

def alphaCups' (a : α) : List (List α) :=
  (S.sort (· ≤ ·)).sublists.filter (l.IsAlphaCup a)

def alphaCup' (a : α) : Option (List α) :=
  (l.alphaCups' a).argmax List.length

def alphaCup'_isSome {a : α} (ha : a ∈ S) : Option.isSome (l.alphaCup' a) = true :=
  by
  rw [← Option.ne_none_iff_isSome, Config.Label.alphaCup']; simp
  apply mem_imply_nnil []; simp [IsAlphaCup, alphaCups']
  exact ha

-- one off from actual definition
def alpha (a : α) : ℕ :=
  if ha : a ∈ S then (Option.get _ (l.alphaCup'_isSome ha)).length else 0

-- APIs for alpha: First, existence of a cup with length alpha + 1
def alphaCup {a : α} (ha : a ∈ S) :
    Σ' c : List α,
      c.length = l.alpha a + 1 ∧ c.In S ∧ c.Sorted (· < ·) ∧ c.Chain' (l.Slopeᶜ) ∧ a ∈ c.getLast? :=
  by
  have some := l.alphaCup'_isSome ha
  set c := Option.get _ some with def_c
  rw [alpha]; rw [dif_pos ha]; rw [← def_c]
  have h_argmax := Option.get_mem some
  rw [← def_c, alphaCup'] at h_argmax
  have c_alpha_cup := List.argmax_mem h_argmax
  simp [alphaCups', IsAlphaCup] at c_alpha_cup
  use c ++ [a]; simp; tauto

-- Next, maximality of the cup with length alpha + 1
def cup_length_le_alpha {a : α} {c : List α} (c_in_S : c.In S) (c_sorted : c.Sorted (· < ·))
    (c_chain : c.Chain' (l.Slopeᶜ)) (c_last : a ∈ c.getLast?) : c.length ≤ l.alpha a + 1 :=
  by
  have ha : a ∈ S := c_in_S _ (List.mem_of_mem_getLast? c_last)
  have some := l.alphaCup'_isSome ha
  set d := Option.get _ some with def_d
  rw [alpha]; rw [dif_pos ha]; rw [← def_d]
  have h_argmax := Option.get_mem some
  rw [← def_d, alphaCup'] at h_argmax
  rcases List.takeLast' c_last with ⟨c', eq_c⟩
  subst eq_c; simp
  have c'_alpha_cup : c' ∈ l.alphaCups' a :=
    by
    rw [alphaCups']; simp; constructor
    · apply List.sublist_of_subperm_of_sorted _ _ (Finset.sort_sorted_lt S)
      apply List.Nodup.subperm
      apply @List.Nodup.sublist _ _ (c' ++ [a])
      simp; exact List.Sorted.nodup c_sorted
      intro a ha; simp; simp at c_in_S; exact c_in_S.left _ ha
      apply List.Pairwise.sublist _ c_sorted; simp
    · refine' ⟨_, _, _⟩ <;> assumption
  exact List.le_of_mem_argmax c'_alpha_cup h_argmax

theorem add_alpha {a : α} (ha : a ∈ S) {n : ℕ} {c : List α} (c_in_S : c.In S) (c_cup : C.NCup n c)
    (c_head : a ∈ c.head?) : C.HasNCup (n + l.alpha a) S :=
  by
  rcases l.alphaCup ha with ⟨d, d_length, d_in_S, d_sorted, d_chain, d_last⟩
  have d_cup : C.Cup d := l.alphaCup_is_cup _ d_in_S d_sorted d_chain
  rcases List.takeLast' d_last with ⟨d', eq_d⟩
  rcases List.takeHead' c_head with ⟨c', eq_c⟩
  use d' ++ a::c'
  by_cases hd' : d' = []
  · subst hd'; simp at eq_d; subst eq_d; simp at d_length; rw [d_length]
    rw [← eq_c]; constructor <;> simp <;> assumption
  rcases List.takeLast hd' with ⟨p, d'', eq_d'⟩
  cases' c' with q c''
  · subst eq_c; cases' c_cup with _ c_len; simp at c_len
    subst c_len; rw [← eq_d]; refine' ⟨⟨_, _⟩, _⟩
    assumption; rw [d_length]; exact add_comm _ _; assumption
  rw [eq_d']; constructor
  · rw [Config.NCup]; constructor; simp; refine' ⟨_, _, _⟩
    convert d_cup; rw [eq_d, eq_d']; simp
    rw [eq_d'] at eq_d; simp at eq_d
    rw [eq_d] at d_chain d_sorted d_in_S
    rw [eq_c] at c_in_S c_cup
    rw [List.Sorted] at d_sorted
    rw [Config.NCup, Config.Cup] at c_cup
    apply l.extend_left
    simp at d_in_S <;> tauto; simp at d_in_S <;> tauto
    have t := @List.Pairwise.sublist _ [p, a] (d'' ++ [p, a]) _ ?_ d_sorted
    simp at t; exact t; simp
    simp at d_chain <;> tauto
    simp at c_in_S <;> tauto
    simp at c_cup <;> tauto
    rw [← eq_c]; exact c_cup.left
    rw [eq_d] at d_length; simp at d_length
    rw [← eq_c]; rw [← eq_d']; simp; rw [d_length]
    rw [c_cup.right]; exact add_comm _ _
  · rw [← eq_c]; rw [← eq_d']; simp; rw [eq_d] at d_in_S
    simp at d_in_S; tauto

end Config.Label

namespace Config

variable (C) (S)

def IsBetaCup (a : α) (c : List α) : Prop :=
  (c ++ [a]).In S ∧ C.Cup (c ++ [a])

instance decidableIsBetaCup (a : α) (c : List α) : Decidable (C.IsBetaCup S a c) := by
  rw [IsBetaCup] <;> infer_instance

def betaCups' (a : α) : List (List α) :=
  (S.sort (· ≤ ·)).sublists.filter (C.IsBetaCup S a)

def betaCup' (a : α) : Option (List α) :=
  (C.betaCups' S a).argmax List.length

def betaCup'_isSome {a : α} (ha : a ∈ S) : Option.isSome (C.betaCup' S a) :=
  by
  rw [← Option.ne_none_iff_isSome]; rw [Config.betaCup']; simp
  apply mem_imply_nnil []; simp [IsBetaCup, betaCups']; exact ha

-- one off from actual definition
def beta (a : α) : ℕ :=
  if ha : a ∈ S then (Option.get _ (C.betaCup'_isSome S ha)).length else 0

-- APIs for beta: First, existence of a cup with length alpha + 1
def betaCup {a : α} (ha : a ∈ S) :
    Σ' c : List α, c.In S ∧ C.NCup (C.beta S a + 1) c ∧ a ∈ c.getLast? :=
  by
  have some := C.betaCup'_isSome S ha
  set c := Option.get _ some with def_c
  rw [beta]; rw [dif_pos ha]; rw [← def_c]
  have h_argmax := Option.get_mem some
  rw [← def_c, betaCup'] at h_argmax
  have c_beta_cup := List.argmax_mem h_argmax
  simp [betaCups', IsBetaCup] at c_beta_cup
  use c ++ [a]; simp [Config.NCup]; tauto

theorem has_beta_cup {a : α} (ha : a ∈ S) : C.HasNCup (C.beta S a + 1) S :=
  by
  rcases C.betaCup S ha with ⟨c, c_in, c_cup, -⟩
  use c

-- Next, maximality of the cup with length alpha + 1
def cup_length_le_beta {a : α} {c : List α} (c_in_S : c.In S) (c_cup : C.Cup c)
    (c_last : a ∈ c.getLast?) : c.length ≤ C.beta S a + 1 :=
  by
  have ha : a ∈ S := c_in_S _ (List.mem_of_mem_getLast? c_last)
  have some := C.betaCup'_isSome S ha
  set d := Option.get _ some with def_d
  rw [beta]; rw [dif_pos ha]; rw [← def_d]
  have h_argmax := Option.get_mem some
  rw [← def_d, betaCup'] at h_argmax
  rcases List.takeLast' c_last with ⟨c', eq_c⟩
  subst eq_c; simp
  have c_sorted := List.chain'_iff_pairwise.mp c_cup.left
  have c'_beta_cup : c' ∈ C.betaCups' S a :=
    by
    rw [betaCups']; simp; constructor
    · apply List.sublist_of_subperm_of_sorted _ _ (Finset.sort_sorted_lt S)
      apply List.Nodup.subperm
      apply @List.Nodup.sublist _ _ (c' ++ [a]); simp
      exact List.Sorted.nodup c_sorted
      intro a ha; simp; simp at c_in_S; exact c_in_S.left _ ha
      apply List.Pairwise.sublist _ c_sorted; simp
    · constructor <;> assumption
  exact List.le_of_mem_argmax c'_beta_cup h_argmax

end Config

theorem Config.Label.alpha_le_beta {a : α} (ha : a ∈ S) : l.alpha a ≤ C.beta S a :=
  by
  rcases l.alphaCup ha with ⟨c, c_length, c_in, c_sorted, c_chain, c_last⟩
  have c_cup := l.alphaCup_is_cup _ c_in c_sorted c_chain
  have ineq := C.cup_length_le_beta S c_in c_cup c_last
  rw [c_length] at ineq; simp at ineq; exact ineq

variable {l}

theorem slope_ff_inc_alpha {a b : α} (sab : ¬l.Slope a b) (ha : a ∈ S) (hb : b ∈ S)
    (a_le_b : a < b) : l.alpha a < l.alpha b :=
  by
  rcases l.alphaCup ha with ⟨c, c_length, c_in, c_sorted, c_chain, c_last⟩
  rcases List.takeLast' c_last with ⟨c', c_eq⟩
  rw [Nat.lt_iff_add_one_le, ← add_le_add_iff_right 1]
  set d := c ++ [b] with def_d
  have d_length : d.length = l.alpha a + 1 + 1 := by simp [def_d, c_length]
  rw [← d_length]
  apply l.cup_length_le_alpha
  · rw [def_d]; simp; tauto
  · rw [def_d, c_eq, List.Sorted, ← List.chain'_iff_pairwise]
    simp; rw [List.chain'_iff_pairwise, ← List.Sorted]
    rw [← c_eq]; exact ⟨c_sorted, a_le_b⟩
  · rw [def_d, c_eq]; simp; rw [← c_eq]
    exact ⟨c_chain, sab⟩
  · rw [def_d]; simp

theorem slope_tt_inc_beta {a b : α} (sab : l.Slope a b) (ha : a ∈ S) (hb : b ∈ S) (a_le_b : a < b) :
    C.beta S a < C.beta S b :=
  by
  rcases C.betaCup S ha with ⟨c, c_in, ⟨c_cup, c_length⟩, c_last⟩
  rcases List.takeLast' c_last with ⟨c', c_eq⟩
  rw [Nat.lt_iff_add_one_le, ← add_le_add_iff_right 1]
  set d := c ++ [b] with def_d
  have d_length : d.length = C.beta S a + 1 + 1 := by simp [def_d, c_length]
  rw [← d_length]
  apply C.cup_length_le_beta S <;> rw [def_d]
  simp; constructor <;> assumption
  apply c_cup.extend_right sab <;> try assumption
  simp

variable (C)

theorem Config.alpha_eq_beta_inc {a b : α} (ha : a ∈ S) (hb : b ∈ S) (h : l.alpha a = l.alpha b) :
    a < b ↔ C.beta S a < C.beta S b := by
  constructor
  · intro hab
    by_cases hl : l.Slope a b
    apply slope_tt_inc_beta hl <;> assumption
    have h' := slope_ff_inc_alpha hl ha hb hab
    rw [h] at h'; simp at h'
  · intro hab
    rcases lt_trichotomy a b with (a_lt_b | a_eq_b | b_lt_a)
    exact a_lt_b
    subst a_eq_b; simp at hab
    exfalso; by_cases hl : l.Slope b a
    have h' := slope_tt_inc_beta hl hb ha b_lt_a
    have h'' := lt_trans h' hab; simp at h''
    have h' := slope_ff_inc_alpha hl hb ha b_lt_a
    rw [h] at h'; simp at h'

variable {C} (l)

theorem Config.Label.beta_eq_alpha_inc {a b : α} (ha : a ∈ S) (hb : b ∈ S)
    (h : C.beta S a = C.beta S b) : a < b ↔ l.alpha a < l.alpha b :=
  by
  constructor
  · intro hab
    by_cases hl : l.Slope a b
    have h' := slope_tt_inc_beta hl ha hb hab
    rw [h] at h'; simp at h'
    apply slope_ff_inc_alpha hl <;> assumption
  · intro hab
    rcases lt_trichotomy a b with (a_lt_b | a_eq_b | b_lt_a)
    exact a_lt_b
    subst a_eq_b; simp at hab
    exfalso; by_cases hl : l.Slope b a
    have h' := slope_tt_inc_beta hl hb ha b_lt_a
    rw [h] at h'; simp at h'
    have h' := slope_ff_inc_alpha hl hb ha b_lt_a
    have h'' := lt_trans h' hab; simp at h''
