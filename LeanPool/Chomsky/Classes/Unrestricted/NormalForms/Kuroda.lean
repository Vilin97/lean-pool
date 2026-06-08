/-
Copyright (c) 2026 Martin Dvořák. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Dvořák
-/
import LeanPool.Chomsky.Classes.Unrestricted.Basics.Definition


/-- Transformation rule for a grammar in the Kuroda Normal Form. -/
inductive KurodaRule (T N : Type)
  | two_two (A B C D : N) : KurodaRule T N
  | one_two (A B C : N) : KurodaRule T N
  | one_one (A : N) (t : T) : KurodaRule T N
  | one_nil (A : N) : KurodaRule T N

/-- Grammar in the Kuroda Normal Form that generates words
    over the alphabet `T` (a type of terminals). -/
structure KurodaGrammar (T : Type) where
  nt : Type
  initial : nt
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
def KurodaGrammar.Derives (g : KurodaGrammar T) : List (Symbol T g.nt) → List (Symbol T g.nt) → Prop :=
  Relation.ReflTransGen g.Transforms

/-- The set of words that can be derived from the initial nonterminal. -/
def KurodaGrammar.language (g : KurodaGrammar T) : Language T :=
  { w : List T | g.Derives [Symbol.nonterminal g.initial] (w.map Symbol.terminal) }

-- end of definition

def grule_of_kurodaRule {N : Type} : KurodaRule T N → Grule T N
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

def grammar_of_kurodaGrammar (k : KurodaGrammar T) : Grammar T :=
  Grammar.mk k.nt k.initial (k.rules.map grule_of_kurodaRule)

lemma KurodaGrammar.tran_iff (k : KurodaGrammar T) (w₁ w₂ : List (Symbol T k.nt)) :
  k.Transforms w₁ w₂ ↔ (grammar_of_kurodaGrammar k).Transforms w₁ w₂ :=
by
  have align : (grammar_of_kurodaGrammar k).Transforms w₁ w₂ ↔
      Grammar.Transforms (T := T) ⟨k.nt, k.initial, k.rules.map grule_of_kurodaRule⟩ w₁ w₂ := Iff.rfl
  rw [align]
  constructor
  · rintro ⟨r, rin, u, v, hruv⟩
    cases r with
    | two_two A B C D =>
      obtain ⟨bef, aft⟩ := hruv
      exact ⟨grule_of_kurodaRule (.two_two A B C D), List.mem_map.mpr ⟨_, rin, rfl⟩, u, v,
        by rw [bef]; simp [grule_of_kurodaRule], by rw [aft]; simp [grule_of_kurodaRule]⟩
    | one_two A B C =>
      obtain ⟨bef, aft⟩ := hruv
      exact ⟨grule_of_kurodaRule (.one_two A B C), List.mem_map.mpr ⟨_, rin, rfl⟩, u, v,
        by rw [bef]; simp [grule_of_kurodaRule], by rw [aft]; simp [grule_of_kurodaRule]⟩
    | one_one A t =>
      obtain ⟨bef, aft⟩ := hruv
      exact ⟨grule_of_kurodaRule (.one_one A t), List.mem_map.mpr ⟨_, rin, rfl⟩, u, v,
        by rw [bef]; simp [grule_of_kurodaRule], by rw [aft]; simp [grule_of_kurodaRule]⟩
    | one_nil A =>
      obtain ⟨bef, aft⟩ := hruv
      exact ⟨grule_of_kurodaRule (.one_nil A), List.mem_map.mpr ⟨_, rin, rfl⟩, u, v,
        by rw [bef]; simp [grule_of_kurodaRule], by rw [aft]; simp [grule_of_kurodaRule]⟩
  · rintro ⟨r, rin, u, v, hruv⟩
    obtain ⟨r₀, rink, rfl⟩ := List.mem_map.mp rin
    cases r₀ with
    | two_two A B C D =>
      obtain ⟨bef, aft⟩ := hruv
      refine ⟨.two_two A B C D, rink, u, v, ?_, ?_⟩
      · rw [show (grule_of_kurodaRule (KurodaRule.two_two A B C D)).inputL = [] from rfl,
          show (grule_of_kurodaRule (KurodaRule.two_two A B C D)).inputN = A from rfl,
          show (grule_of_kurodaRule (KurodaRule.two_two A B C D)).inputR =
            [Symbol.nonterminal B] from rfl] at bef
        rw [bef]; simp
      · rw [show (grule_of_kurodaRule (KurodaRule.two_two A B C D)).output =
          [Symbol.nonterminal C, Symbol.nonterminal D] from rfl] at aft
        exact aft
    | one_two A B C =>
      obtain ⟨bef, aft⟩ := hruv
      refine ⟨.one_two A B C, rink, u, v, ?_, ?_⟩
      · rw [show (grule_of_kurodaRule (KurodaRule.one_two A B C)).inputL = [] from rfl,
          show (grule_of_kurodaRule (KurodaRule.one_two A B C)).inputN = A from rfl,
          show (grule_of_kurodaRule (KurodaRule.one_two A B C)).inputR = [] from rfl] at bef
        rw [bef]; simp
      · rw [show (grule_of_kurodaRule (KurodaRule.one_two A B C)).output =
          [Symbol.nonterminal B, Symbol.nonterminal C] from rfl] at aft
        exact aft
    | one_one A t =>
      obtain ⟨bef, aft⟩ := hruv
      refine ⟨.one_one A t, rink, u, v, ?_, ?_⟩
      · rw [show (grule_of_kurodaRule (KurodaRule.one_one A t)).inputL = [] from rfl,
          show (grule_of_kurodaRule (KurodaRule.one_one A t)).inputN = A from rfl,
          show (grule_of_kurodaRule (KurodaRule.one_one A t)).inputR = [] from rfl] at bef
        rw [bef]; simp
      · rw [show (grule_of_kurodaRule (KurodaRule.one_one A t)).output =
          [Symbol.terminal t] from rfl] at aft
        exact aft
    | one_nil A =>
      obtain ⟨bef, aft⟩ := hruv
      refine ⟨.one_nil A, rink, u, v, ?_, ?_⟩
      · rw [show (grule_of_kurodaRule (KurodaRule.one_nil A)).inputL = [] from rfl,
          show (grule_of_kurodaRule (KurodaRule.one_nil A)).inputN = A from rfl,
          show (grule_of_kurodaRule (KurodaRule.one_nil A)).inputR = [] from rfl] at bef
        rw [bef]; simp
      · rw [show (grule_of_kurodaRule (KurodaRule.one_nil A)).output = [] from rfl] at aft
        rw [aft]; simp
lemma KurodaGrammar.tran_rel_eq (k : KurodaGrammar T) :
  k.Transforms = (grammar_of_kurodaGrammar k).Transforms :=
by
  ext
  apply KurodaGrammar.tran_iff

lemma KurodaGrammar.deri_iff (k : KurodaGrammar T) (w₁ w₂ : List (Symbol T k.nt)) :
  k.Derives w₁ w₂ ↔ (grammar_of_kurodaGrammar k).Derives w₁ w₂ :=
by
  unfold KurodaGrammar.Derives
  rw [KurodaGrammar.tran_rel_eq]
  rfl

lemma KurodaGrammar.lang_eq (k : KurodaGrammar T) :
  k.language = (grammar_of_kurodaGrammar k).language :=
by
  ext
  apply KurodaGrammar.deri_iff
