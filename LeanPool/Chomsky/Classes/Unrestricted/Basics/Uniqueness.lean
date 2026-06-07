/-
Copyright (c) 2026 Martin Dvořák. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Dvořák
-/
import LeanPool.Chomsky.Classes.Unrestricted.Basics.Definition

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
  constructor
   <;> intro ⟨r, rin, p, q, bef, aft⟩
  · simp [myGram] at rin
    simp only [rin, myRule] at bef aft
    use myRulf, List.mem_of_mem_head? rfl, p, q
    simp [bef, aft, myRulf, A, B]
  · simp [myGran] at rin
    simp only [rin, myRulf] at bef aft
    use myRule, List.mem_of_mem_head? rfl, p, q
    simp [bef, aft, myRule, A, B]
