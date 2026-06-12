/-
Copyright (c) 2026 Martin Dvořák. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Dvořák
-/
import LeanPool.Chomsky.Classes.Unrestricted.Basics.Toolbox
import LeanPool.Chomsky.Utilities.ListUtils

/-!
# Lifting

Lifting and sinking of grammar derivations along nonterminal embeddings.
-/

namespace Chomsky


section functions_lift_sink

variable {N N₀ T : Type}

/-- Lift a symbol along a nonterminal embedding. -/
def liftSymbol (f : N₀ → N) : Symbol T N₀ → Symbol T N
  | Symbol.terminal t => Symbol.terminal t
  | Symbol.nonterminal n => Symbol.nonterminal (f n)

/-- Sink a symbol along a nonterminal projection. -/
def sinkSymbol (f : N → Option N₀) : Symbol T N → Option (Symbol T N₀)
  | Symbol.terminal t => some (Symbol.terminal t)
  | Symbol.nonterminal n => Option.map Symbol.nonterminal (f n)

/-- Lift a string of symbols along a nonterminal embedding. -/
def liftString (f : N₀ → N) : List (Symbol T N₀) → List (Symbol T N) :=
  List.map (liftSymbol f)

/-- Sink a string of symbols along a nonterminal projection. -/
def sinkString (f : N → Option N₀) : List (Symbol T N) → List (Symbol T N₀) :=
  List.filterMap (sinkSymbol f)

/-- Lift a rewrite rule along a nonterminal embedding. -/
def liftRule (f : N₀ → N) : Grule T N₀ → Grule T N :=
  fun r : Grule T N₀ => Grule.mk
    (liftString f r.inputL)
    (f r.inputN)
    (liftString f r.inputR)
    (liftString f r.output)

end functions_lift_sink


section lifting_conditions

/-- A grammar together with an embedding of another grammar's nonterminals into it. -/
structure LiftedGrammar (T : Type) where
  /-- The smaller grammar being embedded. -/
  g₀ : Grammar T
  /-- The larger grammar. -/
  g : Grammar T
  /-- The embedding of nonterminals from the smaller into the larger grammar. -/
  liftNt : g₀.nt → g.nt
  /-- The partial inverse of the nonterminal embedding. -/
  sinkNt : g.nt → Option g₀.nt
  lift_inj : liftNt.Injective
  sink_inj : ∀ x y : g.nt, sinkNt x = sinkNt y → x = y ∨ sinkNt x = none
  sinkNt_liftNt : ∀ n₀ : g₀.nt, sinkNt (liftNt n₀) = some n₀
  corresponding_rules : ∀ r : Grule T g₀.nt, r ∈ g₀.rules → liftRule liftNt r ∈ g.rules
  preimage_of_rules :
    ∀ r : Grule T g.nt,
      (r ∈ g.rules ∧ ∃ n₀ : g₀.nt, liftNt n₀ = r.inputN) →
        (∃ r₀ ∈ g₀.rules, liftRule liftNt r₀ = r)

private lemma lifted_grammar_inverse {T : Type} {G : LiftedGrammar T} {x : G.g.nt} {n₀ : G.g₀.nt}
    (hGxn₀ : G.sinkNt x = some n₀) :
  (Option.map G.liftNt (G.sinkNt x) = x) :=
by
  rw [hGxn₀, Option.map_some]
  apply congr_arg
  symm
  by_contra x_neq
  have inje := G.sink_inj x (G.liftNt n₀)
  rw [G.sinkNt_liftNt] at inje
  rcases inje hGxn₀ with case_valu | case_none
  · exact x_neq case_valu
  rw [hGxn₀] at case_none
  exact absurd case_none (Option.some_ne_none n₀)

end lifting_conditions


section translating_derivations

variable {T : Type}

lemma lift_tran {G : LiftedGrammar T} {w₁ w₂ : List (Symbol T G.g₀.nt)}
    (hGww : G.g₀.Transforms w₁ w₂) :
  G.g.Transforms (liftString G.liftNt w₁) (liftString G.liftNt w₂) :=
match hGww with
  | ⟨r, rin, u, v, bef, aft⟩ => ⟨
    liftRule G.liftNt r,
    G.corresponding_rules r rin,
    liftString G.liftNt u,
    liftString G.liftNt v,
    by simpa [liftString, liftRule, liftSymbol, List.map_append] using
      congr_arg (liftString G.liftNt) bef,
    by simpa [liftString, liftRule, liftSymbol, List.map_append] using
      congr_arg (liftString G.liftNt) aft⟩

lemma lift_deri (G : LiftedGrammar T) {w₁ w₂ : List (Symbol T G.g₀.nt)}
    (hGww : G.g₀.Derives w₁ w₂) :
  G.g.Derives (liftString G.liftNt w₁) (liftString G.liftNt w₂) :=
by
  induction hGww with
  | refl => exact gr_deri_self
  | tail _ orig ih => exact gr_deri_of_deri_tran ih (lift_tran orig)

/-- Predicate selecting symbols that lie in the image of the embedding. -/
def GoodLetter {G : LiftedGrammar T} : Symbol T G.g.nt → Prop
  | Symbol.terminal _ => True
  | Symbol.nonterminal n => ∃ n₀ : G.g₀.nt, G.sinkNt n = n₀

/-- Predicate selecting strings all of whose symbols are good. -/
def GoodString {G : LiftedGrammar T} (s : List (Symbol T G.g.nt)) : Prop :=
  ∀ a ∈ s, GoodLetter a

lemma sink_tran {G : LiftedGrammar T} {w₁ w₂ : List (Symbol T G.g.nt)}
    (hGww : G.g.Transforms w₁ w₂) (hw₁ : GoodString w₁) :
  G.g₀.Transforms (sinkString G.sinkNt w₁) (sinkString G.sinkNt w₂) ∧ GoodString w₂ :=
by
  rcases hGww with ⟨r, rin, u, v, bef, aft⟩
  rcases G.preimage_of_rules r (by
      constructor
      · exact rin
      rw [bef] at hw₁
      obtain ⟨n₀, hn₀⟩ : GoodLetter (Symbol.nonterminal r.inputN) := by
        apply hw₁ (Symbol.nonterminal r.inputN)
        apply List.mem_append_left
        apply List.mem_append_left
        apply List.mem_append_right
        rw [List.mem_singleton]
      use n₀
      have almost := congr_arg (Option.map G.liftNt) hn₀
      rw [lifted_grammar_inverse hn₀, Option.map_some] at almost
      apply Option.some_injective
      exact almost.symm
    )
    with ⟨r₀, pre_in, preimage⟩
  constructor; swap
  · rw [bef] at hw₁
    rw [aft]
    unfold GoodString at hw₁ ⊢
    rw [←preimage]
    clear * - hw₁
    rw [List.forall_mem_append_append] at hw₁ ⊢
    rw [List.forall_mem_append_append] at hw₁
    constructor
    · exact hw₁.left.left
    constructor; swap
    · exact hw₁.right.right
    intro a a_in_ros
    cases a
    · simp [GoodLetter]
    dsimp only [liftRule, liftString] at a_in_ros
    rw [List.mem_map] at a_in_ros
    rcases a_in_ros with ⟨s, -, a_from_s⟩
    rw [←a_from_s]
    cases s with
    | terminal s' =>
      exfalso
      clear * - a_from_s
      simp [liftSymbol] at a_from_s
    | nonterminal s'' =>
      simp only [GoodLetter, liftSymbol]
      use s''
      exact G.sinkNt_liftNt s''
  use r₀
  constructor
  · exact pre_in
  use sinkString G.sinkNt u
  use sinkString G.sinkNt v
  have correct_inverse :
      sinkSymbol G.sinkNt ∘ liftSymbol G.liftNt = @Option.some (Symbol T G.g₀.nt) := by
    ext1 x
    cases x
    · rfl
    rewrite [Function.comp_apply, liftSymbol, sinkSymbol, G.sinkNt_liftNt]
    rfl
  constructor
  · have sink_bef := congr_arg (sinkString G.sinkNt) bef
    unfold sinkString at *
    rw [List.filterMap_append_append] at sink_bef
    rw [List.filterMap_append_append] at sink_bef
    convert sink_bef <;> rw [←preimage] <;> unfold liftRule <;> dsimp only <;>
      clear * - correct_inverse
    · unfold liftString
      rw [List.filterMap_map, correct_inverse, List.filterMap_some]
    · change
        [Symbol.nonterminal r₀.inputN] =
        List.filterMap (sinkSymbol G.sinkNt)
          (List.map (liftSymbol G.liftNt) [Symbol.nonterminal r₀.inputN])
      rw [List.filterMap_map, correct_inverse, List.filterMap_some]
    · unfold liftString
      rw [List.filterMap_map, correct_inverse, List.filterMap_some]
  · have sink_aft := congr_arg (sinkString G.sinkNt) aft
    unfold sinkString at *
    rw [List.filterMap_append_append] at sink_aft
    convert sink_aft
    rw [←preimage]
    clear * - correct_inverse
    dsimp only [liftRule, liftString]
    rw [List.filterMap_map, correct_inverse, List.filterMap_some]

private lemma sink_deri_aux {G : LiftedGrammar T} {w₁ w₂ : List (Symbol T G.g.nt)}
    (hGww : G.g.Derives w₁ w₂) (hw₁ : GoodString w₁) :
  G.g₀.Derives (sinkString G.sinkNt w₁) (sinkString G.sinkNt w₂) ∧ GoodString w₂ :=
by
  induction hGww with
  | refl => exact ⟨gr_deri_self, hw₁⟩
  | tail _ orig ih =>
    have both := sink_tran orig ih.right
    exact ⟨gr_deri_of_deri_tran ih.left both.left, both.right⟩

lemma sink_deri (G : LiftedGrammar T) {w₁ w₂ : List (Symbol T G.g.nt)}
    (hGww : G.g.Derives w₁ w₂) (hw₁ : GoodString w₁) :
  G.g₀.Derives (sinkString G.sinkNt w₁) (sinkString G.sinkNt w₂) :=
(sink_deri_aux hGww hw₁).left

end translating_derivations

end Chomsky
