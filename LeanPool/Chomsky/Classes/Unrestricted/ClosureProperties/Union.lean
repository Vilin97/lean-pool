/-
Copyright (c) 2026 Martin Dvořák. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Dvořák
-/
import LeanPool.Chomsky.Classes.Unrestricted.Basics.Lifting
import LeanPool.Chomsky.Utilities.ListUtils
import Mathlib.Tactic.Linarith

/-!
# Union

Closure of general-grammar languages under union.
-/

open scoped Chomsky

namespace Chomsky


variable {T : Type}

private lemma filterMap_sinkSymbol_terminals {N N₀ : Type} (f : N → Option N₀) (w : List T) :
    w.map Symbol.terminal = (w.map Symbol.terminal).filterMap (sinkSymbol f) := by
  induction w with
  | nil => rfl
  | cons h t ih =>
    rw [List.map_cons, List.map_cons, List.filterMap_cons]
    rw [show sinkSymbol f (Symbol.terminal h) = some (Symbol.terminal h) from rfl, ← ih]

/-- The grammar generating the union of two languages. -/
def unionGrammar (g₁ g₂ : Grammar T) : Grammar T :=
  Grammar.mk (Option (g₁.nt ⊕ g₂.nt)) none (
    ⟨[], none, [], [Symbol.nonterminal (some ◄g₁.initial)]⟩ :: (
    ⟨[], none, [], [Symbol.nonterminal (some ▶g₂.initial)]⟩ :: (
    g₁.rules.map (liftRule (some ∘ Sum.inl)) ++
    g₂.rules.map (liftRule (some ∘ Sum.inr)))))


variable {g₁ g₂ : Grammar T}

@[simp]
lemma unionGrammar_initial : (unionGrammar g₁ g₂).initial = none :=
  rfl

@[simp]
lemma unionGrammar_rules :
    (unionGrammar g₁ g₂).rules =
      ⟨[], none, [], [Symbol.nonterminal (some ◄g₁.initial)]⟩ ::
      ⟨[], none, [], [Symbol.nonterminal (some ▶g₂.initial)]⟩ ::
      (g₁.rules.map (liftRule (some ∘ Sum.inl)) ++ g₂.rules.map (liftRule (some ∘ Sum.inr))) :=
  rfl

private def oN₁_of_N : (unionGrammar g₁ g₂).nt → Option g₁.nt
  | none => none
  | some ◄n => some n
  | some ▶_ => none

private def oN₂_of_N : (unionGrammar g₁ g₂).nt → Option g₂.nt
  | none => none
  | some ◄_ => none
  | some ▶n => some n


/-- The lifted-grammar witness for the first component. -/
def lg₁ : LiftedGrammar T :=
  LiftedGrammar.mk
    g₁
    (unionGrammar g₁ g₂)
    (Option.some ∘ Sum.inl)
    oN₁_of_N
    (by
      intro x y hyp
      exact Sum.inl_injective (Option.some_injective _ hyp)
    )
    (by
      intro x y hyp
      rcases x with _ | (x' | x') <;> rcases y with _ | (y' | y') <;>
        simp_all [oN₁_of_N]
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
      exact List.mem_map.mpr ⟨r, hyp, rfl⟩
    )
    (by
      rintro r ⟨rin, n₁, rnt⟩
      rw [unionGrammar_rules, List.mem_cons, List.mem_cons] at rin
      obtain req₁ | req₂ | rin₃ := rin
      on_goal 3 => obtain rin₁ | rin₂ := List.mem_append.mp rin₃
      · exfalso
        rw [req₁] at rnt
        exact absurd rnt (Option.some_ne_none _)
      · exfalso
        rw [req₂] at rnt
        exact absurd rnt (Option.some_ne_none _)
      · exact List.mem_map.mp rin₁
      · exfalso
        rcases List.mem_map.mp rin₂ with ⟨r₂, r₂_in, r₂_lift⟩
        rw [←r₂_lift] at rnt
        have rnti := Option.some.inj rnt
        simp only [reduceCtorEq] at rnti
    )

/-- The lifted-grammar witness for the second component. -/
def lg₂ : LiftedGrammar T :=
  LiftedGrammar.mk
    g₂
    (unionGrammar g₁ g₂)
    (Option.some ∘ Sum.inr)
    oN₂_of_N
    (by
      intro x y hyp
      exact Sum.inr_injective (Option.some_injective _ hyp)
    )
    (by
      intro x y hyp
      rcases x with _ | (x' | x') <;> rcases y with _ | (y' | y') <;>
        simp_all [oN₂_of_N]
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
      exact List.mem_map.mpr ⟨r, hyp, rfl⟩
    )
    (by
      rintro r ⟨rin, n₁, rnt⟩
      rw [unionGrammar_rules, List.mem_cons, List.mem_cons] at rin
      obtain req₁ | req₂ | rin₃ := rin
      on_goal 3 => obtain rin₁ | rin₂ := List.mem_append.mp rin₃
      · exfalso
        rw [req₁] at rnt
        exact absurd rnt (Option.some_ne_none _)
      · exfalso
        rw [req₂] at rnt
        exact absurd rnt (Option.some_ne_none _)
      · exfalso
        rcases List.mem_map.mp rin₁ with ⟨r₁, r₁_in, r₁_lift⟩
        rw [←r₁_lift] at rnt
        have rnti := Option.some.inj rnt
        simp only [reduceCtorEq] at rnti
      · exact List.mem_map.mp rin₂
    )


private lemma good_initial_singleton {G : LiftedGrammar T} {a : Symbol T G.g.nt}
    (ha : GoodLetter a) :
  GoodString [a] := by
  intro b hb
  rw [List.mem_singleton] at hb
  exact hb ▸ ha

lemma in_L₁_or_L₂_of_in_union {w : List T}
    (hwgg : w ∈ (unionGrammar g₁ g₂).language) :
  w ∈ g₁.language ∨ w ∈ g₂.language :=
by
  unfold Grammar.language at hwgg ⊢
  have hggw := gr_eq_or_tran_deri_of_deri hwgg
  clear hwgg
  rcases hggw with hggw₁ | hggw₂
  · exfalso
    have zeroth := congr_arg (·[0]?) hggw₁
    cases w <;> simp at zeroth
  rcases hggw₂ with ⟨i, ⟨r, rin, u, v, bef, aft⟩, deri⟩
  have uv_nil : u = [] ∧ v = [] := by
    have bef_len := congr_arg List.length bef
    clear * - bef_len
    simp only [List.append_assoc, List.length_append, List.length_cons, List.length_nil,
      List.singleton_append] at bef_len
    refine ⟨?_, ?_⟩ <;>
    · rw [← List.length_eq_zero_iff]; omega
  rw [uv_nil.left, List.nil_append, uv_nil.right, List.append_nil] at bef aft
  have same_nt : (unionGrammar g₁ g₂).initial = r.inputN := by
    have bef_len := congr_arg List.length bef
    have rl_first : r.inputL.length = 0 ∧ r.inputR.length = 0 := by
      clear * - bef_len
      simp only [List.append_assoc, List.length_append, List.length_cons, List.length_nil,
        List.singleton_append] at bef_len
      omega
    simp only [List.length_eq_zero_iff] at rl_first
    rw [rl_first.left, rl_first.right, List.nil_append, List.append_nil] at bef
    exact Symbol.nonterminal.inj (List.head_eq_of_cons_eq bef)
  simp only [unionGrammar_rules, List.mem_cons] at rin
  obtain req₁ | req₂ | rin₃ := rin
  on_goal 3 => obtain rin₁ | rin₂ := List.mem_append.mp rin₃
  · rw [req₁] at aft
    dsimp only at aft
    rw [aft] at deri
    left
    change g₁.Derives _ _
    have sinked := sink_deri lg₁ deri (good_initial_singleton ⟨g₁.initial, rfl⟩)
    convert sinked
    all_goals first
      | rfl
      | (unfold sinkString
         exact heq_of_eq (filterMap_sinkSymbol_terminals lg₁.sinkNt w))
  · rw [req₂] at aft
    dsimp only at aft
    rw [aft] at deri
    right
    change g₂.Derives _ _
    have sinked := sink_deri lg₂ deri (good_initial_singleton ⟨g₂.initial, rfl⟩)
    convert sinked
    all_goals first
      | rfl
      | (unfold sinkString
         exact heq_of_eq (filterMap_sinkSymbol_terminals lg₂.sinkNt w))
  · exfalso
    rcases List.mem_map.mp rin₁ with ⟨r₁, -, r_of_r₁⟩
    rw [← r_of_r₁, unionGrammar_initial] at same_nt
    simp only [liftRule, Function.comp_apply] at same_nt
    exact absurd same_nt (Option.some_ne_none _).symm
  · exfalso
    rcases List.mem_map.mp rin₂ with ⟨r₂, -, r_of_r₂⟩
    rw [← r_of_r₂, unionGrammar_initial] at same_nt
    simp only [liftRule, Function.comp_apply] at same_nt
    exact absurd same_nt (Option.some_ne_none _).symm

lemma in_union_of_in_L₁ {w : List T} (hwg : w ∈ g₁.language) :
  w ∈ (unionGrammar g₁ g₂).language :=
by
  unfold Grammar.language at hwg ⊢
  apply gr_deri_of_tran_deri
  · refine ⟨⟨[], none, [], [Symbol.nonterminal (some ◄g₁.initial)]⟩, ?_, [], [], rfl, rfl⟩
    apply List.mem_cons_self
  convert lift_deri lg₁ hwg
  all_goals first
    | rfl
    | (apply heq_of_eq
       change _ = List.map (liftSymbol _) (w.map Symbol.terminal)
       rw [List.map_map]
       rfl)

lemma in_union_of_in_L₂ {w : List T} (hwg : w ∈ g₂.language) :
  w ∈ (unionGrammar g₁ g₂).language :=
by
  apply gr_deri_of_tran_deri
  · refine ⟨⟨[], none, [], [Symbol.nonterminal (some ▶g₂.initial)]⟩, ?_, [], [], rfl, rfl⟩
    apply List.mem_cons_of_mem
    apply List.mem_cons_self
  convert lift_deri lg₂ hwg
  all_goals first
    | rfl
    | (apply heq_of_eq
       change _ = List.map (liftSymbol _) (w.map Symbol.terminal)
       rw [List.map_map]
       rfl)

/-- The class of grammar-generated languages is closed under union. -/
theorem GG_of_GG_u_GG (L₁ : Language T) (L₂ : Language T) :
  Language.IsGG L₁ ∧ Language.IsGG L₂ → Language.IsGG (L₁ + L₂) :=
by
  rintro ⟨⟨g₁, rfl⟩, ⟨g₂, rfl⟩⟩
  use unionGrammar g₁ g₂
  exact Set.eq_of_subset_of_subset ↓in_L₁_or_L₂_of_in_union
    ↓(·.casesOn in_union_of_in_L₁ in_union_of_in_L₂)

end Chomsky
