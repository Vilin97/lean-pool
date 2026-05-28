/-
Copyright (c) 2026 Siddhartha Gadgil, Anand Rao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Siddhartha Gadgil, Anand Rao
-/

namespace LeanPool.Polylean

/-!
## Decision by enumeration

For a type `X` that is finite (or more generally, *compact*), it is possible to
automatically decide any statement of the form `∀ x : X, P x` by enumeration
when `P` is a decidable predicate on `X`
(i.e., a predicate for the individual propositions `P x` are decidable for any given `x : X`).

## Overview

The `EnumDecide.decideForall` typeclass defines the property of a type being exhaustively checkable.

Results in this file include
- `EnumDecide.decideFin` - the type `Fin n` (the canonical finite set with
  `n` elements) is checkable for any `n : ℕ`.
- `EnumDecide.decideUnit` - the single-element type is exhaustively checkable.
- `EnumDecide.decideProd`, `EnumDecide.decideSum` - the product and direct sum
  of two exhaustively checkable types.
- `EnumDecide.funEnum` - the type of functions from an exhaustively checkable
  type to a type with decidable equality is exhaustively checkable.
-/

namespace EnumDecide

/--
It is possible to check whether a given decidable predicate holds for all natural
numbers below a given bound.
-/
def decideBelow (p : Nat → Prop) [DecidablePred p] (bound : Nat) :
    Decidable (∀ n : Nat, n < bound → p n) :=
    match bound with
    | 0 => by
      apply Decidable.isTrue
      intro n bd
      contradiction
    | k + 1 =>
      let prev := decideBelow p k
      match prev with
      | Decidable.isTrue hyp =>
        if c: p k then
          by
          apply Decidable.isTrue
          intro n bd
          cases Nat.eq_or_lt_of_le bd with
          | inl eql =>
            have eql' : n = k := by
                injection eql
            simp [eql']
            assumption
          | inr lt =>
            have lt' : n < k := by
                apply Nat.le_of_succ_le_succ
                assumption
            exact hyp n lt'
        else
          by
          apply Decidable.isFalse
          intro contra
          have lem : p k := by
            apply contra k
            apply Nat.le_refl
          contradiction
      | Decidable.isFalse hyp => by
        apply Decidable.isFalse
        intro contra
        have lem : ∀ (n : Nat), n < k → p n := by
          intro n bd
          have bd' : n < k + 1 := by
            apply Nat.le_succ_of_le
            exact bd
          exact contra n bd'
        contradiction

/--
It is possible to check whether a decidable predicate on `Fin m` holds below a
given natural-number bound.
-/
def decideBelowFin {m : Nat} (p : Fin m → Prop) [DecidablePred p] (bound : Nat) :
    Decidable (∀ n : Fin m, n < bound → p n) :=
    match bound with
    | 0 => by
      apply Decidable.isTrue
      intro n bd
      contradiction
    | k + 1 =>
      let prev := decideBelowFin p k
      match prev with
      | Decidable.isTrue hyp =>
        if ineq : k < m then
          if c: p ⟨k, ineq⟩ then
            by
            apply Decidable.isTrue
            intro n bd
            cases Nat.eq_or_lt_of_le bd with
            | inl eql =>
              have eql' : n = ⟨k, ineq⟩ := by
                  apply Fin.eq_of_val_eq
                  injection eql
              simp [eql']
              assumption
            | inr lt =>
              have lt' : n < k := by
                  apply Nat.le_of_succ_le_succ
                  assumption
              exact hyp n lt'
          else
            by
            apply Decidable.isFalse
            intro contra
            have lem : p ⟨k, ineq⟩ := by
              apply contra ⟨k, ineq⟩
              apply Nat.le_refl
            contradiction
        else
          by
          apply Decidable.isTrue
          intro ⟨n, nbd⟩ _
          have ineq' : m ≤ k := by
            apply Nat.le_of_succ_le_succ
            apply Nat.gt_of_not_le ineq
          have ineq'' := Nat.le_trans nbd ineq'
          exact hyp ⟨n, nbd⟩ ineq''
      | Decidable.isFalse hyp => by
        apply Decidable.isFalse
        intro contra
        have lem : ∀ (n : Fin m), n < k → p n := by
          intro n bd
          have bd' : n < k + 1 := by
            apply Nat.le_succ_of_le
            exact bd
          exact contra n bd'
        contradiction

/-- It is possible to decide whether a predicate holds for all elements of `Fin n`. -/
def decideFin {m : Nat} (p : Fin m → Prop) [DecidablePred p] :
    Decidable (∀ n : Fin m, p n) :=
  match decideBelowFin p m with
  | Decidable.isTrue hyp =>
    by
    apply Decidable.isTrue
    intro ⟨n, ineq⟩
    exact hyp ⟨n, ineq⟩ ineq
  | Decidable.isFalse hyp => by
    apply Decidable.isFalse
    intro contra
    apply hyp
    intro ⟨n, ineq⟩ _
    exact contra ⟨n, ineq⟩

/--
A typeclass for "exhaustively verifiable types", i.e., types for which it is
possible to decide whether a given (decidable) predicate holds for all its
elements.
-/
class DecideForall (α : Type _) where
  /-- Decide whether a decidable predicate holds for all elements. -/
  decideForall (p : α → Prop) [DecidablePred p]:
    Decidable (∀ x : α, p x)

instance {k : Nat} : DecideForall (Fin k) :=
  ⟨by apply decideFin⟩

instance {α : Type _} [dfa : DecideForall α] {p : α → Prop} [DecidablePred p] :
    Decidable (∀ x : α, p x) :=
  dfa.decideForall p

example : ∀ x : Fin 3, x + 0 = x := by decide

example : ∀ x y : Fin 3, x + y = y + x := by decide

example : ∀ x y z : Fin 3, (x + y) + z = x + (y + z) := by decide

@[reducible, instance]
def decideProd {α β : Type _} [dfa : DecideForall α] [dfb : DecideForall β]
    (p : α × β → Prop) [DecidablePred p] : Decidable (∀ xy : α × β, p xy) :=
    if c: (∀ x: α, ∀ y : β, p (x, y))
    then
      by
      apply Decidable.isTrue
      intro (x, y)
      exact c x y
    else
      by
      apply Decidable.isFalse
      intro contra
      apply c
      intro x y
      exact contra (x, y)

instance {α β : Type _} [dfa : DecideForall α] [dfb : DecideForall β] :
  DecideForall (α × β) :=
  ⟨by apply decideProd⟩

@[reducible, instance]
def decideUnit (p : Unit → Prop) [DecidablePred p] : Decidable (∀ x : Unit, p x) :=
   if c : p (()) then by
      apply Decidable.isTrue
      intro x
      have l : x = () := by rfl
      rw [l]
      exact c
    else by
      apply Decidable.isFalse
      intro contra
      apply c
      exact contra ()

instance : DecideForall Unit :=
  ⟨by apply decideUnit⟩

@[reducible, instance]
def decideSum {α β : Type _} [dfa : DecideForall α] [dfb : DecideForall β]
    (p : α ⊕ β → Prop) [DecidablePred p] : Decidable (∀ x : α ⊕ β, p x) :=
    if c: ∀x: α, p (Sum.inl x) then
       if c': ∀y: β , p (Sum.inr y) then
       by
        apply Decidable.isTrue
        intro x
        cases x with
        | inl a => exact c a
        | inr a => exact c' a
      else by
        apply Decidable.isFalse
        intro contra
        apply c'
        intro x
        exact contra (Sum.inr x)
    else by
      apply Decidable.isFalse
      intro contra
      apply c
      intro x
      exact contra (Sum.inl x)

instance {α β : Type _} [dfa : DecideForall α] [dfb : DecideForall β] :
  DecideForall (α ⊕ β) :=
  ⟨by apply decideSum⟩

instance funEnum {α β : Type _} [dfa : DecideForall α] [dfb : DecidableEq β] :
    DecidableEq (α → β) := fun f g =>
      if c: ∀ x: α, f x = g x then
        by
        apply Decidable.isTrue
        apply funext
        intro x
        exact c x
      else
        by
        apply Decidable.isFalse
        intro contra
        apply c
        intro x
        exact congrFun contra x


example : ∀ xy : (Fin 3) × (Fin 2),
      xy.1.val + xy.2.val = xy.2.val + xy.1.val := by decide
end EnumDecide
end LeanPool.Polylean
