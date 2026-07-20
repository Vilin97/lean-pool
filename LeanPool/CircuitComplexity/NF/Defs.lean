/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import LeanPool.CircuitComplexity.Basic

/-! # Normal Forms — Core Definitions

This module defines Conjunctive Normal Form (CNF) and Disjunctive Normal Form (DNF)
Boolean formulas over `N` variables, together with their evaluation semantics,
complexity measures, and De Morgan negation duality.

## Main definitions

* `Literal` — a Boolean variable with a polarity flag (positive or negative)
* `CNF` — a conjunction of clauses (each clause is a disjunction of literals)
* `DNF` — a disjunction of terms (each term is a conjunction of literals)
* `CNF.complexity` — the number of clauses in a CNF formula
* `DNF.complexity` — the number of terms in a DNF formula
* `CNF.neg` / `DNF.neg` — De Morgan negation (CNF ↔ DNF)
-/

namespace CircuitComplexity


/-- A literal: a Boolean variable (by index) together with a polarity flag.

`polarity = true` represents the positive literal xᵢ;
`polarity = false` represents the negative literal ¬xᵢ. -/
structure Literal (N : Nat) where
  /-- The index of the variable this literal refers to. -/
  var : Fin N
  /-- `true` = positive literal (xᵢ); `false` = negative literal (¬xᵢ). -/
  polarity : Bool
  deriving DecidableEq

/-- Evaluate a literal on a bit assignment. -/
def Literal.eval (l : Literal N) (x : BitString N) : Bool :=
  if l.polarity then x l.var else !x l.var

/-- Negate a literal by flipping its polarity. -/
def Literal.neg (l : Literal N) : Literal N :=
  { l with polarity := !l.polarity }

/-- Negating a literal negates its evaluation. -/
theorem Literal.eval_neg (l : Literal N) (x : BitString N) :
    l.neg.eval x = !(l.eval x) := by
  simp only [Literal.neg, Literal.eval]
  cases l.polarity <;> simp

/-! ## CNF -/

/--
A CNF (Conjunctive Normal Form) formula over `N` Boolean variables.

A CNF is a conjunction of clauses, where each clause is a disjunction of literals.
-/
structure CNF (N : Nat) where
  /-- The clauses of the formula. Each clause is a list of literals. -/
  clauses : List (List (Literal N))

namespace CNF

/-- A CNF formula evaluates to `true` iff every clause contains at least one
satisfied literal. -/
def eval (φ : CNF N) (x : BitString N) : Bool :=
  φ.clauses.all fun clause => clause.any fun l => l.eval x

/-- The complexity of a CNF formula is its number of clauses. -/
def complexity (φ : CNF N) : Nat := φ.clauses.length

end CNF

/-! ## DNF -/

/--
A DNF (Disjunctive Normal Form) formula over `N` Boolean variables.

A DNF is a disjunction of terms, where each term is a conjunction of literals.
-/
structure DNF (N : Nat) where
  /-- The terms of the formula. Each term is a list of literals. -/
  terms : List (List (Literal N))

namespace DNF

/-- A DNF formula evaluates to `true` iff at least one term has all its
literals satisfied. -/
def eval (φ : DNF N) (x : BitString N) : Bool :=
  φ.terms.any fun term => term.all fun l => l.eval x

/-- The complexity of a DNF formula is its number of terms. -/
def complexity (φ : DNF N) : Nat := φ.terms.length

end DNF

/-! ## De Morgan Negation Duality -/

/-- Negate a CNF formula by flipping all literal polarities, producing a DNF.
By De Morgan's laws, `¬(∧ᵢ ∨ⱼ lᵢⱼ) = ∨ᵢ ∧ⱼ ¬lᵢⱼ`. -/
def CNF.neg (φ : CNF N) : DNF N :=
  ⟨φ.clauses.map (fun clause => clause.map Literal.neg)⟩

/-- Negate a DNF formula by flipping all literal polarities, producing a CNF.
By De Morgan's laws, `¬(∨ᵢ ∧ⱼ lᵢⱼ) = ∧ᵢ ∨ⱼ ¬lᵢⱼ`. -/
def DNF.neg (φ : DNF N) : CNF N :=
  ⟨φ.terms.map (fun term => term.map Literal.neg)⟩

/-- Negating a CNF formula negates its evaluation (De Morgan duality). -/
theorem CNF.eval_neg (φ : CNF N) (x : BitString N) :
    φ.neg.eval x = !(φ.eval x) := by
  simp only [CNF.neg, DNF.eval, CNF.eval, List.any_map, List.all_map, Function.comp_def,
    List.not_all_eq_any_not, List.not_any_eq_all_not, Literal.eval_neg]

/-- Negating a DNF formula negates its evaluation (De Morgan duality). -/
theorem DNF.eval_neg (φ : DNF N) (x : BitString N) :
    φ.neg.eval x = !(φ.eval x) := by
  simp only [DNF.neg, CNF.eval, DNF.eval, List.any_map, List.all_map, Function.comp_def,
    List.not_all_eq_any_not, List.not_any_eq_all_not, Literal.eval_neg]

/-- Negating a CNF preserves complexity. -/
theorem CNF.neg_complexity (φ : CNF N) : φ.neg.complexity = φ.complexity := by
  simp [CNF.neg, DNF.complexity, CNF.complexity, List.length_map]

end CircuitComplexity
