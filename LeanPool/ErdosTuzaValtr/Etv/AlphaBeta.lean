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

/-!
# LeanPool.ErdosTuzaValtr.Etv.AlphaBeta

Imported Lean Pool material for `LeanPool.ErdosTuzaValtr.Etv.AlphaBeta`.
-/

noncomputable section

variable {α : Type _} [LinearOrder α] {C : Config α} {S : Finset α} (l : C.Label S)

private theorem mem_imply_nnil {α : Type _} (a : α) {l : List α} (ha : a ∈ l) : l ≠ [] := by
  rintro rfl; simp at ha

namespace Config
namespace Label

/-- A candidate alpha-cup ending at `a`: in `S`, strictly sorted, with non-slope edges. -/
def IsAlphaCup (a : α) (c : List α) : Prop :=
  (c ++ [a]).In S ∧ (c ++ [a]).Pairwise (· < ·) ∧ (c ++ [a]).IsChain (l.Slopeᶜ)

theorem alphaCup_is_cup (c : List α) (c_in_S : c.In S) (c_sorted : c.Pairwise (· < ·))
    (c_chain : c.IsChain (l.Slopeᶜ)) : C.Cup c := by
  induction c with
  | nil => exact Cup.nil
  | cons h0 c ih =>
    cases c with
    | nil => exact Cup.singleton h0
    | cons h1 c =>
      have h0_lt_h1 : h0 < h1 := (List.pairwise_cons.mp c_sorted).1 h1 (by simp)
      cases c with
      | nil => rw [Cup.pair]; exact h0_lt_h1
      | cons h2 c =>
        have tail_in : (h1 :: h2 :: c).In S := fun x hx => c_in_S x (by simp [hx])
        have tail_sorted : (h1 :: h2 :: c).Pairwise (· < ·) := (List.pairwise_cons.mp c_sorted).2
        have tail_chain : (h1 :: h2 :: c).IsChain (l.Slopeᶜ) :=
          (List.isChain_cons_cons.mp c_chain).2
        have h1_lt_h2 : h1 < h2 := (List.pairwise_cons.mp tail_sorted).1 h2 (by simp)
        have h_slope : (l.Slopeᶜ) h0 h1 := (List.isChain_cons_cons.mp c_chain).1
        rw [Cup.cons3]
        refine ⟨h0_lt_h1, ?_, ih tail_in tail_sorted tail_chain⟩
        exact l.extend_left (c_in_S h0 (by simp)) (c_in_S h1 (by simp)) h0_lt_h1 h_slope
          (c_in_S h2 (by simp)) h1_lt_h2

open Classical in
/-- All alpha-cups ending at `a`, drawn from sublists of the sorted `S`. -/
def alphaCups' (a : α) : List (List α) :=
  (S.sort (· ≤ ·)).sublists.filter (l.IsAlphaCup a)

/-- A longest alpha-cup ending at `a`, if one exists. -/
def alphaCup' (a : α) : Option (List α) :=
  (l.alphaCups' a).argmax List.length

theorem alphaCup'_isSome {a : α} (ha : a ∈ S) : Option.isSome (l.alphaCup' a) = true := by
  rw [← Option.ne_none_iff_isSome, Config.Label.alphaCup']
  simp only [ne_eq, List.argmax_eq_none]
  apply mem_imply_nnil []
  simp only [alphaCups', IsAlphaCup, List.append_in, List.cons_in, List.nil_in, and_true,
    List.mem_filter, List.mem_sublists, List.nil_sublist, List.nil_append, List.pairwise_cons,
    List.not_mem_nil, IsEmpty.forall_iff, implies_true, List.Pairwise.nil, and_self,
    List.IsChain.singleton, decide_eq_true_eq, true_and]
  exact ha

/-- One less than the length of a longest alpha-cup ending at `a` (zero off `S`). -/
-- one off from actual definition
def alpha (a : α) : ℕ :=
  if ha : a ∈ S then (Option.get _ (l.alphaCup'_isSome ha)).length else 0

/-- A witnessing alpha-cup of length `alpha a + 1` ending at `a`. -/
-- APIs for alpha: First, existence of a cup with length alpha + 1
def alphaCup {a : α} (ha : a ∈ S) :
    Σ' c : List α,
      c.length = l.alpha a + 1 ∧
        c.In S ∧ c.Pairwise (· < ·) ∧ c.IsChain (l.Slopeᶜ) ∧ a ∈ c.getLast? :=
  by
  have some := l.alphaCup'_isSome ha
  set c := Option.get _ some with def_c
  rw [alpha, dif_pos ha, ← def_c]
  have h_argmax := Option.get_mem some
  rw [← def_c, alphaCup'] at h_argmax
  have c_alpha_cup := List.argmax_mem h_argmax
  simp only [alphaCups', IsAlphaCup, List.append_in, List.cons_in, List.nil_in, and_true,
    List.mem_filter, List.mem_sublists, decide_eq_true_eq] at c_alpha_cup
  use c ++ [a]
  simp only [List.length_append, List.length_cons, List.length_nil, zero_add,
    List.append_in, List.cons_in, List.nil_in, and_true,
    List.getLast?_append, List.getLast?_singleton, Option.some_or, Option.mem_def, true_and]
  tauto

-- Next, maximality of the cup with length alpha + 1
theorem cup_length_le_alpha {a : α} {c : List α} (c_in_S : c.In S) (c_sorted : c.Pairwise (· < ·))
    (c_chain : c.IsChain (l.Slopeᶜ)) (c_last : a ∈ c.getLast?) : c.length ≤ l.alpha a + 1 := by
  classical
  have ha : a ∈ S := c_in_S _ (List.mem_of_mem_getLast? c_last)
  have some := l.alphaCup'_isSome ha
  set d := Option.get _ some with def_d
  rw [alpha, dif_pos ha, ← def_d]
  have h_argmax := Option.get_mem some
  rw [← def_d, alphaCup'] at h_argmax
  rcases List.takeLast' c_last with ⟨c', eq_c⟩
  subst eq_c
  simp only [List.length_append, List.length_cons, List.length_nil, zero_add,
    add_le_add_iff_right, ge_iff_le]
  have c'_pairwise : c'.Pairwise (· < ·) := (c_sorted.sublist (List.sublist_append_left c' [a]))
  have c'_alpha_cup : c' ∈ l.alphaCups' a := by
    rw [alphaCups', List.mem_filter, List.mem_sublists]
    refine ⟨?_, ?_⟩
    · apply List.sublist_of_subperm_of_pairwise _ c'_pairwise ((Finset.sortedLT_sort S).pairwise)
      apply List.Nodup.subperm c'_pairwise.nodup
      intro x hx
      rw [Finset.mem_sort]
      rw [List.append_in, List.cons_in] at c_in_S
      exact c_in_S.1 x hx
    · rw [decide_eq_true_eq]
      exact ⟨c_in_S, c_sorted, c_chain⟩
  exact List.le_of_mem_argmax c'_alpha_cup h_argmax

theorem add_alpha {a : α} (ha : a ∈ S) {n : ℕ} {c : List α} (c_in_S : c.In S) (c_cup : C.NCup n c)
    (c_head : a ∈ c.head?) : C.HasNCup (n + l.alpha a) S := by
  rcases l.alphaCup ha with ⟨d, d_length, d_in_S, d_sorted, d_chain, d_last⟩
  have d_cup : C.Cup d := l.alphaCup_is_cup _ d_in_S d_sorted d_chain
  rcases List.takeLast' d_last with ⟨d', eq_d⟩
  rcases List.takeHead' c_head with ⟨c', eq_c⟩
  have alpha_eq : d'.length = l.alpha a := by
    rw [eq_d, List.length_append, List.length_singleton] at d_length
    omega
  refine ⟨d' ++ a::c', ?_, ?_⟩
  swap
  · intro x hx
    rw [List.mem_append] at hx
    rcases hx with hxd | hxc
    · exact d_in_S x (by rw [eq_d, List.mem_append]; exact Or.inl hxd)
    · exact c_in_S x (by rw [eq_c]; exact hxc)
  cases c' with
  | nil =>
    rw [Config.NCup, ← eq_d]
    refine ⟨d_cup, ?_⟩
    obtain ⟨_, c_len⟩ := c_cup
    rw [eq_c, List.length_cons, List.length_nil] at c_len
    rw [d_length]
    omega
  | cons q c'' =>
    rcases List.eq_nil_or_concat d' with hd' | ⟨d'', p, eq_d'⟩
    · rw [hd', List.nil_append, ← eq_c]
      rw [Config.NCup]
      refine ⟨c_cup.left, ?_⟩
      rw [hd', List.length_nil] at alpha_eq
      rw [c_cup.right]
      omega
    · rw [Config.NCup]
      rw [eq_d', List.concat_eq_append,
        show (d'' ++ [p]) ++ a :: q :: c'' = d'' ++ p :: a :: q :: c'' by simp]
      rw [eq_d', List.concat_eq_append, List.append_assoc] at eq_d
      rw [eq_d] at d_cup d_in_S d_sorted d_chain
      rw [eq_c] at c_in_S c_cup
      refine ⟨?_, ?_⟩
      · rw [Cup.append_cons3]
        refine ⟨d_cup, ?_, c_cup.left⟩
        apply l.extend_left (d_in_S p (by simp)) (d_in_S a (by simp))
        · exact (List.pairwise_cons.mp (List.pairwise_append.mp d_sorted).2.1).1 a (by simp)
        · exact (List.isChain_append_cons_cons.mp d_chain).2.1
        · exact c_in_S q (by simp)
        · exact (List.isChain_cons_cons.mp c_cup.left.left).1
      · have hcl := c_cup.right
        rw [eq_d', List.concat_eq_append] at alpha_eq
        simp only [List.length_append, List.length_cons, List.length_nil] at alpha_eq hcl ⊢
        omega

end Label
end Config

namespace Config

variable (C) (S)

/-- A candidate beta-cup ending at `a`: a cup in `S` ending at `a`. -/
def IsBetaCup (a : α) (c : List α) : Prop :=
  (c ++ [a]).In S ∧ C.Cup (c ++ [a])

open Classical in
instance decidableIsBetaCup (a : α) (c : List α) : Decidable (C.IsBetaCup S a c) := by
  rw [IsBetaCup]; infer_instance

/-- All beta-cups ending at `a`, drawn from sublists of the sorted `S`. -/
def betaCups' (a : α) : List (List α) :=
  (S.sort (· ≤ ·)).sublists.filter (C.IsBetaCup S a)

/-- A longest beta-cup ending at `a`, if one exists. -/
def betaCup' (a : α) : Option (List α) :=
  (C.betaCups' S a).argmax List.length

theorem betaCup'_isSome {a : α} (ha : a ∈ S) : Option.isSome (C.betaCup' S a) := by
  rw [← Option.ne_none_iff_isSome, Config.betaCup']
  simp only [ne_eq, List.argmax_eq_none]
  apply mem_imply_nnil []
  simp only [betaCups', IsBetaCup, List.append_in, List.cons_in, List.nil_in, and_true,
    List.mem_filter, List.mem_sublists, List.nil_sublist, List.nil_append, Cup.singleton,
    decide_eq_true_eq, true_and]
  exact ha

/-- One less than the length of a longest beta-cup ending at `a` (zero off `S`). -/
-- one off from actual definition
def beta (a : α) : ℕ :=
  if ha : a ∈ S then (Option.get _ (C.betaCup'_isSome S ha)).length else 0

/-- A witnessing beta-cup of length `beta a + 1` ending at `a`. -/
-- APIs for beta: First, existence of a cup with length alpha + 1
def betaCup {a : α} (ha : a ∈ S) :
    Σ' c : List α, c.In S ∧ C.NCup (C.beta S a + 1) c ∧ a ∈ c.getLast? :=
  by
  have some := C.betaCup'_isSome S ha
  set c := Option.get _ some with def_c
  rw [beta, dif_pos ha, ← def_c]
  have h_argmax := Option.get_mem some
  rw [← def_c, betaCup'] at h_argmax
  have c_beta_cup := List.argmax_mem h_argmax
  simp only [betaCups', IsBetaCup, List.append_in, List.cons_in, List.nil_in, and_true,
    List.mem_filter, List.mem_sublists, decide_eq_true_eq] at c_beta_cup
  use c ++ [a]
  simp only [List.append_in, List.cons_in, List.nil_in, and_true, NCup, List.length_append,
    List.length_cons, List.length_nil, zero_add, List.getLast?_append,
    List.getLast?_singleton, Option.some_or, Option.mem_def]
  tauto

theorem has_beta_cup {a : α} (ha : a ∈ S) : C.HasNCup (C.beta S a + 1) S :=
  by
  rcases C.betaCup S ha with ⟨c, c_in, c_cup, -⟩
  use c

-- Next, maximality of the cup with length alpha + 1
theorem cup_length_le_beta {a : α} {c : List α} (c_in_S : c.In S) (c_cup : C.Cup c)
    (c_last : a ∈ c.getLast?) : c.length ≤ C.beta S a + 1 := by
  have ha : a ∈ S := c_in_S _ (List.mem_of_mem_getLast? c_last)
  have some := C.betaCup'_isSome S ha
  set d := Option.get _ some with def_d
  rw [beta, dif_pos ha, ← def_d]
  have h_argmax := Option.get_mem some
  rw [← def_d, betaCup'] at h_argmax
  rcases List.takeLast' c_last with ⟨c', eq_c⟩
  subst eq_c
  simp only [List.length_append, List.length_cons, List.length_nil, zero_add,
    add_le_add_iff_right, ge_iff_le]
  have c_sorted := List.isChain_iff_pairwise.mp c_cup.left
  have c'_pairwise : c'.Pairwise (· < ·) := (c_sorted.sublist (List.sublist_append_left c' [a]))
  have c'_beta_cup : c' ∈ C.betaCups' S a := by
    rw [betaCups', List.mem_filter, List.mem_sublists]
    refine ⟨?_, ?_⟩
    · apply List.sublist_of_subperm_of_pairwise _ c'_pairwise ((Finset.sortedLT_sort S).pairwise)
      apply List.Nodup.subperm c'_pairwise.nodup
      intro x hx
      rw [Finset.mem_sort]
      rw [List.append_in, List.cons_in] at c_in_S
      exact c_in_S.1 x hx
    · rw [decide_eq_true_eq]
      exact ⟨c_in_S, c_cup⟩
  exact List.le_of_mem_argmax c'_beta_cup h_argmax

end Config

theorem Config.Label.alpha_le_beta {a : α} (ha : a ∈ S) : l.alpha a ≤ C.beta S a := by
  rcases l.alphaCup ha with ⟨c, c_length, c_in, c_sorted, c_chain, c_last⟩
  have c_cup := l.alphaCup_is_cup _ c_in c_sorted c_chain
  have ineq := C.cup_length_le_beta S c_in c_cup c_last
  rw [c_length] at ineq
  omega

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
  · rw [def_d, ← List.isChain_iff_pairwise]
    apply (List.isChain_iff_pairwise.mpr c_sorted).append (List.isChain_singleton b)
    intro x hx y hy
    rw [List.head?_singleton, Option.mem_some_iff] at hy
    rw [c_eq, List.getLast?_concat, Option.mem_some_iff] at hx
    rw [← hx, ← hy]; exact a_le_b
  · rw [def_d, c_eq]
    simp only [List.append_assoc, List.cons_append, List.nil_append,
      List.isChain_append_cons_cons, Pi.compl_apply, compl_iff_not, List.IsChain.singleton,
      and_true]
    rw [← c_eq]
    exact ⟨c_chain, sab⟩
  · rw [def_d]; simp

theorem slope_tt_inc_beta {a b : α} (sab : l.Slope a b) (ha : a ∈ S) (hb : b ∈ S) (a_le_b : a < b) :
    C.beta S a < C.beta S b := by
  rcases C.betaCup S ha with ⟨c, c_in, ⟨c_cup, c_length⟩, c_last⟩
  rcases List.takeLast' c_last with ⟨c', c_eq⟩
  rw [Nat.lt_iff_add_one_le, ← add_le_add_iff_right 1]
  set d := c ++ [b] with def_d
  have d_length : d.length = C.beta S a + 1 + 1 := by
    rw [def_d, List.length_append, List.length_singleton, c_length]
  rw [← d_length]
  apply C.cup_length_le_beta S
  · rw [def_d, List.append_in, List.cons_in]
    exact ⟨c_in, hb, List.nil_in⟩
  · rw [def_d]
    exact c_cup.extend_right sab a_le_b hb c_in c_last
  · rw [def_d, List.getLast?_append, List.getLast?_singleton]
    rfl

variable (C)

theorem Config.alpha_eq_beta_inc {a b : α} (ha : a ∈ S) (hb : b ∈ S) (h : l.alpha a = l.alpha b) :
    a < b ↔ C.beta S a < C.beta S b := by
  constructor
  · intro hab
    by_cases hl : l.Slope a b
    · exact slope_tt_inc_beta hl ha hb hab
    · have h' := slope_ff_inc_alpha hl ha hb hab
      rw [h] at h'
      exact absurd h' (lt_irrefl _)
  · intro hab
    rcases lt_trichotomy a b with (a_lt_b | a_eq_b | b_lt_a)
    · exact a_lt_b
    · subst a_eq_b; exact absurd hab (lt_irrefl _)
    · exfalso
      by_cases hl : l.Slope b a
      · have h' := slope_tt_inc_beta hl hb ha b_lt_a
        exact absurd (lt_trans h' hab) (lt_irrefl _)
      · have h' := slope_ff_inc_alpha hl hb ha b_lt_a
        rw [h] at h'
        exact absurd h' (lt_irrefl _)

variable {C} (l)

theorem Config.Label.beta_eq_alpha_inc {a b : α} (ha : a ∈ S) (hb : b ∈ S)
    (h : C.beta S a = C.beta S b) : a < b ↔ l.alpha a < l.alpha b := by
  constructor
  · intro hab
    by_cases hl : l.Slope a b
    · have h' := slope_tt_inc_beta hl ha hb hab
      rw [h] at h'
      exact absurd h' (lt_irrefl _)
    · exact slope_ff_inc_alpha hl ha hb hab
  · intro hab
    rcases lt_trichotomy a b with (a_lt_b | a_eq_b | b_lt_a)
    · exact a_lt_b
    · subst a_eq_b; exact absurd hab (lt_irrefl _)
    · exfalso
      by_cases hl : l.Slope b a
      · have h' := slope_tt_inc_beta hl hb ha b_lt_a
        rw [h] at h'
        exact absurd h' (lt_irrefl _)
      · have h' := slope_ff_inc_alpha hl hb ha b_lt_a
        exact absurd (lt_trans h' hab) (lt_irrefl _)
