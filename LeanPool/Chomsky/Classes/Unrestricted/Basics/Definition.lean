/-
Copyright (c) 2026 Martin Dvořák. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Dvořák
-/
import LeanPool.Chomsky.Basic
import Mathlib.Computability.Language

/-!
# Definition

Definition of general (unrestricted) grammars and their derivation relation.
-/

namespace Chomsky


/-- Rewrite rule for a grammar without any restrictions. -/
structure Grule (T N : Type) where
  /-- The part of the left-hand side to the left of the rewritten nonterminal. -/
  inputL : List (Symbol T N)
  /-- The nonterminal rewritten by this rule. -/
  inputN : N
  /-- The part of the left-hand side to the right of the rewritten nonterminal. -/
  inputR : List (Symbol T N)
  /-- The string the rule rewrites the matched portion to. -/
  output : List (Symbol T N)

/-- Grammar (unrestricted) that generates words over the alphabet `T` (a type of terminals). -/
structure Grammar (T : Type) where
  /-- The type of nonterminals. -/
  nt : Type
  /-- The initial nonterminal symbol. -/
  initial : nt
  /-- The rewrite rules of the grammar. -/
  rules : List (Grule T nt)

variable {T : Type}

/-- One step of grammatical transformation. -/
def Grammar.Transforms (g : Grammar T) (w₁ w₂ : List (Symbol T g.nt)) : Prop :=
  ∃ r : Grule T g.nt,
    r ∈ g.rules ∧
    ∃ u v : List (Symbol T g.nt),
      w₁ = u ++ r.inputL ++ [Symbol.nonterminal r.inputN] ++ r.inputR ++ v ∧
      w₂ = u ++ r.output ++ v

/-- Any number of steps of grammatical transformation. -/
def Grammar.Derives (g : Grammar T) : List (Symbol T g.nt) → List (Symbol T g.nt) → Prop :=
  Relation.ReflTransGen g.Transforms

/-- The set of words that can be derived from the initial nonterminal. -/
def Grammar.language (g : Grammar T) : Language T :=
  { w : List T | g.Derives [Symbol.nonterminal g.initial] (w.map Symbol.terminal) }

/-- Predicate "is grammar-generated"; defined by existence of a grammar for the given language. -/
def Language.IsGG (L : Language T) : Prop :=
  ∃ g : Grammar T, g.language = L

end Chomsky
