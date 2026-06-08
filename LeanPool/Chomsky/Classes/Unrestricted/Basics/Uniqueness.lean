/-
Copyright (c) 2026 Martin Dvořák. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Dvořák
-/
import LeanPool.Chomsky.Classes.Unrestricted.Basics.Definition

/-!
# Uniqueness

Uniqueness results for general-grammar derivations.
-/

namespace Chomsky

-- This file shows that our encoding of rules is not unique.

private inductive Ter
  | _x
  | _y

private inductive Non
  | _A
  | _B

private def x : Symbol Ter Non := Symbol.terminal Ter._x
private def y : Symbol Ter Non := Symbol.terminal Ter._y

private def A : Symbol Ter Non := Symbol.nonterminal Non._A
private def B : Symbol Ter Non := Symbol.nonterminal Non._B

private def myRule : Grule Ter Non := ⟨[A, x, y], ._B, [], [y, B, x]⟩
private def myRulf : Grule Ter Non := ⟨[], ._A, [x, y, B], [y, B, x]⟩

private def myGram : Grammar Ter := ⟨Non, ._A, [myRule]⟩
private def myGran : Grammar Ter := ⟨Non, ._A, [myRulf]⟩

example (u v : List (Symbol Ter Non)) : myGram.Transforms u v ↔ myGran.Transforms u v := by
  have e1 : myGram.Transforms u v ↔ ∃ p q : List (Symbol Ter Non),
      u = p ++ [A, x, y] ++ [Symbol.nonterminal Non._B] ++ [] ++ q ∧ v = p ++ [y, B, x] ++ q := by
    constructor
    · intro ⟨r, rin, p, q, bef, aft⟩
      obtain rfl : r = myRule := List.mem_singleton.mp (show r ∈ [myRule] from rin)
      exact ⟨p, q, bef, aft⟩
    · intro ⟨p, q, bef, aft⟩
      exact ⟨myRule, List.mem_of_mem_head? rfl, p, q, bef, aft⟩
  have e2 : myGran.Transforms u v ↔ ∃ p q : List (Symbol Ter Non),
      u = p ++ [] ++ [Symbol.nonterminal Non._A] ++ [x, y, B] ++ q ∧ v = p ++ [y, B, x] ++ q := by
    constructor
    · intro ⟨r, rin, p, q, bef, aft⟩
      obtain rfl : r = myRulf := List.mem_singleton.mp (show r ∈ [myRulf] from rin)
      exact ⟨p, q, bef, aft⟩
    · intro ⟨p, q, bef, aft⟩
      exact ⟨myRulf, List.mem_of_mem_head? rfl, p, q, bef, aft⟩
  rw [e1, e2]
  constructor <;> rintro ⟨p, q, bef, aft⟩ <;> exact ⟨p, q, by simp_all [A, B, x, y], aft⟩

end Chomsky
