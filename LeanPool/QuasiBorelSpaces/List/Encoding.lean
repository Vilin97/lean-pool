/-
Copyright (c) 2026 Anthony Vandikas, Kiarash Sotoudeh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthony Vandikas, Kiarash Sotoudeh
-/

import Mathlib.Tactic.Lemma
import Mathlib.Tactic.TypeStar
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Fin.Basic

/-!
# LeanPool.QuasiBorelSpaces.List.Encoding

Imported Lean Pool material for `LeanPool.QuasiBorelSpaces.List.Encoding`.
-/


namespace List

variable {A B C : Type*}

/--
We derive the `QuasiBorelSpace` instance for `List A`s from their encoding as
`(n : ℕ) × (Fin n → A)`.
-/
abbrev Encoding (A : Type*) :=
  (n : ℕ) × (Fin n → A)

namespace Encoding

/-- The encoded version of `[]`. -/
def nil : Encoding A := ⟨0, Fin.elim0⟩

/-- The encoded version of `· ∷ ·`. -/
def cons (x : A) (xs : Encoding A) : Encoding A :=
  ⟨xs.1 + 1, Fin.cases x xs.2⟩

/-- The encoded version of `List.foldr`. -/
def foldr (cons : A → B → B) (nil : B) : Encoding A → B
  | ⟨0, _⟩ => nil
  | ⟨n + 1, k⟩ => cons (k 0) (foldr cons nil ⟨n, fun i ↦ k i.succ⟩)

@[simp]
lemma foldr_nil {A B} (f : A → B → B) (z : B) : foldr f z nil = z := by
  simp only [nil, foldr]

@[simp]
lemma foldr_cons {A B}
    (f : A → B → B) (z : B) (x : A) (xs : Encoding A)
    : foldr f z (cons x xs) = f x (foldr f z xs) := by
  simp only [cons, foldr, Fin.cases_zero, Fin.cases_succ]

@[simp]
lemma nil_ne_cons (x : A) (xs : Encoding A) : nil ≠ cons x xs := by
  simp only [
    nil, cons, ne_eq, Sigma.mk.injEq, Nat.right_eq_add, Nat.add_eq_zero_iff,
    Nat.succ_ne_self, and_false, false_and, not_false_eq_true]

@[simp]
lemma cons_ne_nil (x : A) (xs : Encoding A) : cons x xs ≠ nil := by
  simp only [
    nil, cons, ne_eq, Sigma.mk.injEq, Nat.add_eq_zero_iff,
    Nat.succ_ne_self, and_false, false_and, not_false_eq_true]

@[simp]
lemma cons_inj_iff (x y : A) (xs ys : Encoding A) : cons x xs = cons y ys ↔ x = y ∧ xs = ys := by
  rcases xs
  rcases ys
  simp only [cons, Sigma.mk.injEq, Nat.add_right_cancel_iff]
  apply Iff.intro
  · simp only [and_imp]
    intro rfl h₁
    simp only [heq_eq_eq, funext_iff] at h₁
    have h₂ := h₁ 0
    have h₃ (n) := h₁ (Fin.succ n)
    simp only [Fin.cases_zero] at h₂
    simp only [Fin.cases_succ] at h₃
    simp only [h₂, heq_eq_eq, funext_iff, h₃, implies_true, and_self]
  · rintro ⟨rfl, rfl, rfl⟩
    simp only [heq_eq_eq, and_self]

/-- Encodes a `List A` as an `Encoding A`. -/
def encode : List A → Encoding A :=
  List.foldr Encoding.cons Encoding.nil

@[simp]
lemma encode_nil {A} : encode (A := A) [] = Encoding.nil := by
  rfl

@[simp]
lemma encode_cons {A} (x : A) (xs : List A) : encode (x :: xs) = Encoding.cons x (encode xs) := by
  rfl

@[simp]
lemma encode_injective : Function.Injective (encode (A := A)) := by
  intro xs ys h
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => simp only
    | cons y ys => simp only [encode_nil, encode_cons, Encoding.nil_ne_cons] at h
  | cons x xs ih =>
    cases ys with
    | nil => simp only [encode_cons, encode_nil, Encoding.cons_ne_nil] at h
    | cons y ys =>
      simp_all only [encode_cons, Encoding.cons_inj_iff, cons.injEq, true_and]
      grind

end Encoding

end List
