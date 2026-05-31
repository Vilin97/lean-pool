/-
Copyright (c) 2026 Jineon Baek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jineon Baek
-/

import Mathlib.Data.Finset.Basic
import LeanPool.ErdosTuzaValtr.Lib.Core.Rel3
import LeanPool.ErdosTuzaValtr.Config.Default

variable {α : Type _} [LinearOrder α] (C : Config α)

/-- A labeling of the edges of `S` by a slope predicate compatible with the cup relation. -/
structure Config.Label (S : Finset α) where
  /-- The slope predicate assigning a direction to each ordered edge. -/
  Slope : α → α → Prop
  -- The direction looks odd, but it is written in perspective of
  -- _where_ the edge ab is placed
  /-- An edge of negative slope extends to the left into a 3-cup. -/
  extend_left :
    ∀ {a b : α}, a ∈ S → b ∈ S → a < b → ¬Slope a b → ∀ {c : α}, c ∈ S → b < c → C.Cup3 a b c
  /-- An edge of positive slope extends to the right into a 3-cup. -/
  extend_right :
    ∀ {a b : α}, a ∈ S → b ∈ S → a < b → Slope a b → ∀ {c : α}, c ∈ S → c < a → C.Cup3 c a b

/-- The canonical slope on a finset: `a, b` has this slope when every earlier
point forms a 3-cup with `a, b`. -/
def Cap4FreeSlope (S : Finset α) (a b : α) : Prop :=
  ∀ c : S, ↑c < a → C.Cup3 c a b

instance decidableCap4FreeSlope (S : Finset α) :
    DecidableRel (Cap4FreeSlope C S) := fun a b => by
  rw [Cap4FreeSlope]; simp only [Subtype.forall]; infer_instance

variable {C}

/-- The canonical labeling of a cap-4-free finset by `Cap4FreeSlope`. -/
def cap4FreeLabel {S : Finset α} (h : ¬C.HasNCap 4 S) : C.Label S :=
  by
  use Cap4FreeSlope C S
  · intro a b ha hb hab hn c hc hbc
    by_contra h'; apply hn; intro d hd
    by_contra h''; apply h; use[d, a, b, c]; simp [Config.NCap]; tauto
  · intro a b ha hb hab hy c hc hca
    exact hy ⟨c, hc⟩ hca

variable {C : Config α} {S : Finset α} {label : C.Label S}

protected theorem Config.Cup.extend_left {l : List α} (l_cup : C.Cup l) {a b : α}
    (s_ab : ¬label.Slope a b) (ha : a ∈ S) (hab : a < b) (l_in_S : l.In S)
    (b_head_l : b ∈ l.head?) : C.Cup (a::l) := by
  cases l with
  | nil => exact absurd b_head_l (Option.not_mem_none b)
  | cons b' l =>
    rw [List.head?_cons, Option.mem_some_iff] at b_head_l
    subst b_head_l
    cases l with
    | nil => rw [Cup.pair]; exact hab
    | cons c l =>
      rw [List.cons_in, List.cons_in] at l_in_S
      rw [Cup.cons3]
      refine ⟨hab, ?_, l_cup⟩
      have hc : c ∈ S := l_in_S.2.1
      have hbc : b' < c := l_cup.left.rel_head
      exact label.extend_left ha l_in_S.1 hab s_ab hc hbc

protected theorem Config.Cup.extend_right {l : List α} (l_cup : C.Cup l) {a b : α}
    (s_ab : label.Slope a b) (hab : a < b) (hb : b ∈ S) (l_in_S : l.In S)
    (a_last_l : a ∈ l.getLast?) : C.Cup (l ++ [b]) := by
  by_cases hl : 2 ≤ l.length
  · rcases List.takeLast2 hl with ⟨c, a', l', eq_l⟩
    rw [eq_l, List.getLast?_append_cons, List.getLast?_cons_cons, List.getLast?_singleton,
      Option.mem_some_iff] at a_last_l
    rw [a_last_l] at eq_l
    subst eq_l
    rw [List.append_assoc]
    have h_infix : [c, a] <:+: l' ++ [c, a] := ⟨l', [], by simp⟩
    have hca : c < a := List.isChain_pair.mp (l_cup.left.infix h_infix)
    rw [List.append_in] at l_in_S
    have ha_mem : a ∈ S := l_in_S.2 a (by simp)
    have hc : c ∈ S := l_in_S.2 c (by simp)
    rw [show ([c, a] ++ [b]) = [c, a, b] from rfl, Cup.append_cons3]
    exact ⟨l_cup, label.extend_right ha_mem hb hab s_ab hc hca, by rw [Cup.pair]; exact hab⟩
  · cases l with
    | nil => exact absurd a_last_l (Option.not_mem_none a)
    | cons p l =>
      cases l with
      | nil =>
        rw [List.getLast?_singleton, Option.mem_some_iff] at a_last_l
        subst a_last_l
        rw [List.singleton_append, Cup.pair]
        exact hab
      | cons q l =>
        exact absurd (by simp [List.length_cons] : 2 ≤ (p :: q :: l).length) hl

protected theorem Config.NCup.extend_left {n : ℕ} {l : List α} (l_ncup : C.NCup n l) {a b : α}
    (s_ab : ¬label.Slope a b) (ha : a ∈ S) (hab : a < b) (l_in_S : l.In S)
    (b_head_l : b ∈ l.head?) : C.NCup (n + 1) (a::l) :=
  ⟨l_ncup.left.extend_left s_ab ha hab l_in_S b_head_l, by
    rw [List.length_cons, l_ncup.right]⟩

protected theorem Config.NCup.extend_right {n : ℕ} {l : List α} (l_ncup : C.NCup n l) {a b : α}
    (s_ab : label.Slope a b) (hab : a < b) (hb : b ∈ S) (l_in_S : l.In S)
    (a_last_l : a ∈ l.getLast?) : C.NCup (n + 1) (l ++ [b]) :=
  ⟨l_ncup.left.extend_right s_ab hab hb l_in_S a_last_l, by
    rw [List.length_append, List.length_singleton, l_ncup.right]⟩

variable (label)

open OrderDual

/-- The mirror labeling on the order dual, induced by negating the mirrored slope. -/
protected def Config.Label.Mirror : C.Mirror.Label S.Mirror :=
  ⟨fun a b => ¬Mirror2 label.Slope a b,
    by
    intro a b a_in_S b_in_S hab hslope c c_in_S hbc
    simp only [Mirror2, not_not] at hslope
    simp only [Mirror, Mirror3]
    simp only [Finset.Mirror, Finset.mem_image] at a_in_S b_in_S c_in_S
    rcases a_in_S with ⟨oa, ⟨oa_in_S, oa_eq⟩⟩
    rcases b_in_S with ⟨ob, ⟨ob_in_S, ob_eq⟩⟩
    rcases c_in_S with ⟨oc, ⟨oc_in_S, oc_eq⟩⟩
    rw [← oa_eq] at hab
    rw [← ob_eq] at hab hbc
    rw [← oc_eq] at hbc
    simp only [toDual_lt_toDual] at hab hbc
    rw [← oa_eq, ← ob_eq, ← oc_eq]; simp only [ofDual_toDual]
    rw [← oa_eq, ← ob_eq] at hslope; simp only [ofDual_toDual] at hslope
    apply label.extend_right <;> tauto,
    by
    intro a b a_in_S b_in_S hab hslope c c_in_S hca
    simp only [Mirror2] at hslope
    simp only [Mirror, Mirror3]
    simp only [Finset.Mirror, Finset.mem_image] at a_in_S b_in_S c_in_S
    rcases a_in_S with ⟨oa, ⟨oa_in_S, oa_eq⟩⟩
    rcases b_in_S with ⟨ob, ⟨ob_in_S, ob_eq⟩⟩
    rcases c_in_S with ⟨oc, ⟨oc_in_S, oc_eq⟩⟩
    rw [← oa_eq] at hab hca
    rw [← ob_eq] at hab
    rw [← oc_eq] at hca
    simp only [toDual_lt_toDual] at hab hca
    rw [← oa_eq, ← ob_eq, ← oc_eq]; simp only [ofDual_toDual]
    rw [← oa_eq, ← ob_eq] at hslope; simp only [ofDual_toDual] at hslope
    apply label.extend_left <;> tauto⟩

variable {label}

theorem Mirror_slope {a b : α} : ¬label.Mirror.Slope (toDual b) (toDual a) ↔ label.Slope a b := by
  rw [Config.Label.Mirror]
  simp only [not_not]
  rw [Mirror2]
  simp only [ofDual_toDual]
