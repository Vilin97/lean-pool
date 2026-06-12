/-
Copyright (c) 2026 Martin Dvořák. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Dvořák
-/
import LeanPool.Chomsky.Classes.Unrestricted.Basics.Definition

/-!
# Definition

Definition of context-free grammars and their derivation relation.
-/

namespace Chomsky


/-- Context-free grammar that generates words over the alphabet `T` (a type of terminals). -/
structure CFG (T : Type) where
  /-- The type of nonterminals. -/
  nt : Type                              -- type of nonterminals
  /-- The initial nonterminal symbol. -/
  initial : nt                           -- initial symbol
  /-- The rewrite rules of the context-free grammar. -/
  rules : List (nt × List (Symbol T nt)) -- rewrite rules

variable {T : Type}

/-- One step of context-free transformation. -/
def CFG.Transforms (g : CFG T) (w₁ w₂ : List (Symbol T g.nt)) : Prop :=
  ∃ r : g.nt × List (Symbol T g.nt),
    r ∈ g.rules ∧
    ∃ u v : List (Symbol T g.nt),
      w₁ = u ++ [Symbol.nonterminal r.fst] ++ v ∧ w₂ = u ++ r.snd ++ v

/-- Any number of steps of context-free transformation. -/
def CFG.Derives (g : CFG T) : List (Symbol T g.nt) → List (Symbol T g.nt) → Prop :=
  Relation.ReflTransGen g.Transforms

/-- The set of words that can be derived from the initial nonterminal. -/
def CFG.language (g : CFG T) : Language T :=
  { w : List T | g.Derives [Symbol.nonterminal g.initial] (w.map Symbol.terminal) }

/-- Predicate "is context-free"; defined by existence of a context-free grammar for the given
language. -/
def Language.IsCF (L : Language T) : Prop :=
  ∃ g : CFG T, g.language = L

end Chomsky
