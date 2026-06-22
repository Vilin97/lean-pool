/-
Copyright (c) 2026 Martin Dvořák. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Dvořák
-/
import LeanPool.Chomsky.Classes.Unrestricted.Basics.Definition

/-!
# Kuroda

The Kuroda normal form for general grammars.
-/

namespace Chomsky


/-- Transformation rule for a grammar in the Kuroda Normal Form. -/
inductive KurodaRule (T N : Type)
  | two_two (A B C D : N) : KurodaRule T N
  | one_two (A B C : N) : KurodaRule T N
  | one_one (A : N) (t : T) : KurodaRule T N
  | one_nil (A : N) : KurodaRule T N

/-- Grammar in the Kuroda Normal Form that generates words
    over the alphabet `T` (a type of terminals). -/
structure KurodaGrammar (T : Type) where
  /-- The type of nonterminals. -/
  nt : Type
  /-- The initial nonterminal symbol. -/
  initial : nt
  /-- The Kuroda-normal-form rules. -/
  rules : List (KurodaRule T nt)

variable {T : Type}

/-- One step of transformation by a grammar in the Kuroda Normal Form. -/
def KurodaGrammar.Transforms (g : KurodaGrammar T) (w₁ w₂ : List (Symbol T g.nt)) : Prop :=
  ∃ r : KurodaRule T g.nt,
    r ∈ g.rules ∧
    ∃ u v : List (Symbol T g.nt),
      match r with
      | KurodaRule.two_two A B C D =>
          w₁ = u ++ [Symbol.nonterminal A, Symbol.nonterminal B] ++ v ∧
          w₂ = u ++ [Symbol.nonterminal C, Symbol.nonterminal D] ++ v
      | KurodaRule.one_two A B C =>
          w₁ = u ++ [Symbol.nonterminal A] ++ v ∧
          w₂ = u ++ [Symbol.nonterminal B, Symbol.nonterminal C] ++ v
      | KurodaRule.one_one A t =>
          w₁ = u ++ [Symbol.nonterminal A] ++ v ∧
          w₂ = u ++ [Symbol.terminal t] ++ v
      | KurodaRule.one_nil A =>
          w₁ = u ++ [Symbol.nonterminal A] ++ v ∧
          w₂ = u ++ v

/-- Any number of steps of transformation by a grammar in the Kuroda Normal Form. -/
def KurodaGrammar.Derives (g : KurodaGrammar T) :
    List (Symbol T g.nt) → List (Symbol T g.nt) → Prop :=
  Relation.ReflTransGen g.Transforms

/-- The set of words that can be derived from the initial nonterminal. -/
def KurodaGrammar.language (g : KurodaGrammar T) : Language T :=
  { w : List T | g.Derives [Symbol.nonterminal g.initial] (w.map Symbol.terminal) }

-- end of definition

/-- Convert a Kuroda-normal-form rule into an ordinary general-grammar rewrite rule. -/
def gruleOfKurodaRule {N : Type} : KurodaRule T N → Grule T N
  | KurodaRule.two_two A B C D =>
      Grule.mk ([] : List (Symbol T N)) A [Symbol.nonterminal B]
        [Symbol.nonterminal C, Symbol.nonterminal D]
  | KurodaRule.one_two A B C =>
      Grule.mk ([] : List (Symbol T N)) A ([] : List (Symbol T N))
        [Symbol.nonterminal B, Symbol.nonterminal C]
  | KurodaRule.one_one A t =>
      Grule.mk ([] : List (Symbol T N)) A ([] : List (Symbol T N)) [Symbol.terminal t]
  | KurodaRule.one_nil A =>
      Grule.mk ([] : List (Symbol T N)) A ([] : List (Symbol T N)) ([] : List (Symbol T N))

/-- The general grammar obtained from a Kuroda-normal-form grammar. -/
def grammarOfKurodaGrammar (k : KurodaGrammar T) : Grammar T :=
  Grammar.mk k.nt k.initial (k.rules.map gruleOfKurodaRule)

lemma KurodaGrammar.tran_iff (k : KurodaGrammar T) (w₁ w₂ : List (Symbol T k.nt)) :
  k.Transforms w₁ w₂ ↔ (grammarOfKurodaGrammar k).Transforms w₁ w₂ :=
by
  have align : (grammarOfKurodaGrammar k).Transforms w₁ w₂ ↔
      Grammar.Transforms (T := T) ⟨k.nt, k.initial, k.rules.map gruleOfKurodaRule⟩ w₁ w₂ := Iff.rfl
  rw [align]
  constructor
  · rintro ⟨r, rin, u, v, hruv⟩
    cases r <;>
      · obtain ⟨bef, aft⟩ := hruv
        exact ⟨gruleOfKurodaRule _, List.mem_map.mpr ⟨_, rin, rfl⟩, u, v,
          by rw [bef]; simp [gruleOfKurodaRule], by rw [aft]; simp [gruleOfKurodaRule]⟩
  · rintro ⟨r, rin, u, v, hruv⟩
    obtain ⟨r₀, rink, rfl⟩ := List.mem_map.mp rin
    refine ⟨r₀, rink, u, v, ?_⟩
    obtain ⟨bef, aft⟩ := hruv
    cases r₀ <;>
      simp_all [gruleOfKurodaRule]
lemma KurodaGrammar.tran_rel_eq (k : KurodaGrammar T) :
  k.Transforms = (grammarOfKurodaGrammar k).Transforms :=
by
  ext
  apply KurodaGrammar.tran_iff

lemma KurodaGrammar.deri_iff (k : KurodaGrammar T) (w₁ w₂ : List (Symbol T k.nt)) :
  k.Derives w₁ w₂ ↔ (grammarOfKurodaGrammar k).Derives w₁ w₂ :=
by
  unfold KurodaGrammar.Derives
  rw [KurodaGrammar.tran_rel_eq]
  rfl

lemma KurodaGrammar.lang_eq (k : KurodaGrammar T) :
  k.language = (grammarOfKurodaGrammar k).language :=
by
  ext
  apply KurodaGrammar.deri_iff

end Chomsky
