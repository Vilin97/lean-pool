/-
Copyright (c) 2026 Martin Dvořák. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Dvořák
-/
import LeanPool.Chomsky.Classes.Unrestricted.Basics.Lifting
import LeanPool.Chomsky.Utilities.ListUtils
import Mathlib.Tactic.Linarith


variable {T : Type}

def unionGrammar (g₁ g₂ : Grammar T) : Grammar T :=
  Grammar.mk (Option (g₁.nt ⊕ g₂.nt)) none (
    ⟨[], none, [], [Symbol.nonterminal (some ◩g₁.initial)]⟩ :: (
    ⟨[], none, [], [Symbol.nonterminal (some ◪g₂.initial)]⟩ :: (
    g₁.rules.map (liftRule (some ∘ Sum.inl)) ++
    g₂.rules.map (liftRule (some ∘ Sum.inr)))))


variable {g₁ g₂ : Grammar T}

private def oN₁_of_N : (unionGrammar g₁ g₂).nt → Option g₁.nt
  | none => none
  | some ◩n => some n
  | some ◪_ => none

private def oN₂_of_N : (unionGrammar g₁ g₂).nt → Option g₂.nt
  | none => none
  | some ◩_ => none
  | some ◪n => some n


def lg₁ : LiftedGrammar T :=
  LiftedGrammar.mk
    g₁
    (unionGrammar g₁ g₂)
    (Option.some ∘ Sum.inl)
    oN₁_of_N
    (by
      intro x y hyp
      apply Sum.inl_injective
      apply Option.some_injective
      exact hyp
    )
    (by
      intro x y hyp
      cases' x with x'
      · right
        rfl
      cases' x' with x''; swap
      · right
        rfl
      cases' y with y'
      · rw [hyp]
        right
        rfl
      cases' y' with y''; swap
      · tauto
      left
      simp only [oN₁_of_N, Option.some.injEq] at hyp
      apply congr_arg
      apply congr_arg
      exact hyp
    )
    (by
      intro
      rfl
    )
    (by
      intro r hyp
      apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      apply List.mem_append_left
      rw [List.mem_map]
      use r
    )
    (by
      rintro r ⟨rin, n₁, rnt⟩
      simp only [unionGrammar, List.mem_cons, List.mem_append, List.mem_map] at rin
      rcases rin with req₁ | req₂ | rin₁ | rin₂
      · exfalso
        rw [req₁] at rnt
        exact Option.noConfusion rnt
      · exfalso
        rw [req₂] at rnt
        exact Option.noConfusion rnt
      · exact rin₁
      · exfalso
        rcases rin₂ with ⟨r₂, r₂_in, r₂_lift⟩
        rw [←r₂_lift] at rnt
        have rnti := Option.some.inj rnt
        exact Sum.noConfusion rnti
    )

def lg₂ : LiftedGrammar T :=
  LiftedGrammar.mk
    g₂
    (unionGrammar g₁ g₂)
    (Option.some ∘ Sum.inr)
    oN₂_of_N
    (by
      intro x y hyp
      apply Sum.inr_injective
      apply Option.some_injective
      exact hyp
    )
    (by
      intro x y hyp
      cases' x with x'
      · right
        rfl
      cases' x' with _ x''
      · right
        rfl
      cases' y with y'
      · rw [hyp]
        right
        rfl
      cases' y' with _ y''
      · tauto
      left
      simp only [oN₂_of_N, Option.some.injEq] at hyp
      apply congr_arg
      apply congr_arg
      exact hyp
    )
    (by
      intro
      rfl
    )
    (by
      intro r hyp
      apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      apply List.mem_append_right
      rw [List.mem_map]
      use r
    )
    (by
      rintro r ⟨rin, n₁, rnt⟩
      simp only [unionGrammar, List.mem_cons, List.mem_append, List.mem_map] at rin
      rcases rin with req₁ | req₂ | rin₁ | rin₂
      · exfalso
        rw [req₁] at rnt
        exact Option.noConfusion rnt
      · exfalso
        rw [req₂] at rnt
        exact Option.noConfusion rnt
      · exfalso
        rcases rin₁ with ⟨r₁, r₁_in, r₁_lift⟩
        rw [←r₁_lift] at rnt
        have rnti := Option.some.inj rnt
        exact Sum.noConfusion rnti
      · exact rin₂
    )


lemma in_L₁_or_L₂_of_in_union {w : List T}
    (hwgg : w ∈ (unionGrammar g₁ g₂).language) :
  w ∈ g₁.language ∨ w ∈ g₂.language :=
by
  unfold Grammar.language at hwgg ⊢
  rw [Set.mem_setOf_eq] at hwgg ⊢
  rw [Set.mem_setOf_eq]
  have hggw := gr_eq_or_tran_deri_of_deri hwgg
  clear hwgg
  cases' hggw with hggw₁ hggw₂
  · exfalso
    have zeroth := congr_arg (·[0]?) hggw₁
    cases w
    · exact Option.noConfusion zeroth
    · simp at zeroth
  rcases hggw₂ with ⟨i, ⟨r, rin, u, v, bef, aft⟩, deri⟩
  have uv_nil : u = [] ∧ v = []
  · have bef_len := congr_arg List.length bef
    clear * - bef_len
    rw [List.length_singleton] at bef_len
    repeat rw [List.length_append] at bef_len
    rw [List.length_singleton] at bef_len
    constructor <;>
    · rw [←List.length_eq_zero_iff]
      linarith
  rw [uv_nil.left, List.nil_append, uv_nil.right, List.append_nil] at bef aft
  have same_nt : (unionGrammar g₁ g₂).initial = r.inputN
  · clear * - bef
    have elemeq : [Symbol.nonterminal (unionGrammar g₁ g₂).initial] = [Symbol.nonterminal r.inputN]
    · have bef_len := congr_arg List.length bef
      rw [List.length_append_append, List.length_singleton, List.length_singleton] at bef_len
      have rl_first : r.inputL.length = 0
      · clear * - bef_len
        linarith
      have rl_third : r.inputR.length = 0
      · clear * - bef_len
        linarith
      rw [List.length_eq_zero_iff] at rl_first rl_third
      rwa [rl_first, rl_third] at bef
    exact Symbol.nonterminal.inj (List.head_eq_of_cons_eq elemeq)
  simp only [unionGrammar, List.mem_cons, List.mem_append, List.mem_map] at rin
  rcases rin with req₁ | req₂ | rin₁ | rin₂
  · rw [req₁] at aft
    dsimp only at aft
    rw [aft] at deri
    left
    have sinked := sink_deri lg₁ deri
    clear * - sinked
    specialize sinked (by
        simp only [GoodString, List.mem_singleton, forall_eq]
        use g₁.initial
        rfl)
    convert sinked
    unfold sinkString
    rw [List.filterMap_map]
    convert_to w.map Symbol.terminal = w.filterMap (Option.some ∘ Symbol.terminal)
    rw [←List.filterMap_map, List.filterMap_some]
  · rw [req₂] at aft
    dsimp only at aft
    rw [aft] at deri
    right
    have sinked := sink_deri lg₂ deri
    clear * - sinked
    specialize sinked (by
        simp only [GoodString, List.mem_singleton, forall_eq]
        use g₂.initial
        rfl)
    convert sinked
    unfold sinkString
    rw [List.filterMap_map]
    convert_to w.map Symbol.terminal = w.filterMap (Option.some ∘ Symbol.terminal)
    rw [←List.filterMap_map, List.filterMap_some]
  · suffices True = False by contradiction
    rcases rin₁ with ⟨r₁, -, r_of_r₁⟩
    convert
      congr_arg
        (Symbol.nonterminal (liftRule (Option.some ∘ Sum.inl) r₁).inputN ∈ ·)
        bef.symm
    · rw [true_iff]
      apply List.mem_append_left
      apply List.mem_append_right
      rw [List.mem_singleton, r_of_r₁]
    · rw [List.mem_singleton, Symbol.nonterminal.injEq]
      simp [liftRule, unionGrammar]
  · suffices True = False by contradiction
    rcases rin₂ with ⟨r₂, -, r_of_r₂⟩
    convert
      congr_arg
        (Symbol.nonterminal (liftRule (Option.some ∘ Sum.inr) r₂).inputN ∈ ·)
        bef.symm
    · rw [true_iff]
      apply List.mem_append_left
      apply List.mem_append_right
      rw [List.mem_singleton, r_of_r₂]
    · rw [List.mem_singleton, Symbol.nonterminal.injEq]
      simp [liftRule, unionGrammar]

lemma in_union_of_in_L₁ {w : List T} (hwg : w ∈ g₁.language) :
  w ∈ (unionGrammar g₁ g₂).language :=
by
  unfold Grammar.language at hwg ⊢
  rw [Set.mem_setOf_eq] at hwg ⊢
  apply gr_deri_of_tran_deri
  · refine ⟨⟨[], none, [], [Symbol.nonterminal (some ◩g₁.initial)]⟩, ?_, [], [], rfl, rfl⟩
    apply List.mem_cons_self
  convert lift_deri lg₁ hwg
  symm
  apply List.map_map

lemma in_union_of_in_L₂ {w : List T} (hwg : w ∈ g₂.language) :
  w ∈ (unionGrammar g₁ g₂).language :=
by
  apply gr_deri_of_tran_deri
  · refine ⟨⟨[], none, [], [Symbol.nonterminal (some ◪g₂.initial)]⟩, ?_, [], [], rfl, rfl⟩
    apply List.mem_cons_of_mem
    apply List.mem_cons_self
  convert lift_deri lg₂ hwg
  symm
  apply List.map_map

/-- The class of grammar-generated languages is closed under union. -/
theorem GG_of_GG_u_GG (L₁ : Language T) (L₂ : Language T) :
  L₁.IsGG ∧ L₂.IsGG → (L₁ + L₂).IsGG :=
by
  rintro ⟨⟨g₁, rfl⟩, ⟨g₂, rfl⟩⟩
  use unionGrammar g₁ g₂
  exact Set.eq_of_subset_of_subset ↓in_L₁_or_L₂_of_in_union ↓(·.casesOn in_union_of_in_L₁ in_union_of_in_L₂)

