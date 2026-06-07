/-
Copyright (c) 2026 György Kurucz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: György Kurucz
-/
import Mathlib.Data.Set.Basic
import Mathlib.Data.Finite.Defs

/-- A Linear Temporal Logic formula. -/
inductive LTL (AP : Type) where
| atom (p : AP)
| not (φ : LTL AP)
| or (φ₁ φ₂ : LTL AP)
| next (φ : LTL AP)
| until (φ₁ φ₂ : LTL AP)

/-- A letter is a set of atomic propositions. -/
abbrev Letter (AP : Type) := Set AP

/-- The language of a Linear Temporal Logic formula,
defined as a predicate over a word. -/
def LTL.language {AP} (f : LTL AP) (w : ℕ → Letter AP) : Prop :=
  match f with
  | .atom p => p ∈ w 0
  | .not φ => ¬language φ w
  | .or φ₁ φ₂ => language φ₁ w ∨ language φ₂ w
  | .next φ => language φ (fun j => w (j + 1))
  | .until φ₁ φ₂ =>
    ∃ i, language φ₂ (fun j => w (j + i)) ∧
    ∀ k < i, language φ₁ (fun j => w (j + k))

/-- A Büchi automaton, on some letter type `S`. -/
structure NBW (S : Type) where
  /-- The type of states. -/
  Q : Type
  /-- The set of starting states. -/
  q₀ : Set Q
  /-- The transition relation. -/
  δ : Q → S → Q → Prop
  /-- The set of accepting states. A run is accepting
  if it visits states in `F` infinitely often. -/
  F : Set Q

/-- Whether the sequence of states `p` is a run on the
word `w` on the Büchi automaton `A`. -/
def NBW.run {S} (A : NBW S) (p : ℕ → A.Q) (w : ℕ → S) :=
  p 0 ∈ A.q₀ ∧ ∀ i, A.δ (p i) (w i) (p (i + 1))

/-- The language of a Büchi automaton,
defined as a predicate over a word. -/
def NBW.language {S} (A : NBW S) (w : ℕ → S) :=
  ∃ p, A.run p w ∧ ∀ i, ∃ j ≥ i, p j ∈ A.F

def for_any_LTL_formula_exists_an_equivalent_NBW_statement :=
  ∀ {AP} (φ : LTL AP), ∃ (A : NBW (Letter AP)), φ.language = A.language
