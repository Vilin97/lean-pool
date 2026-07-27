/-
Copyright (c) 2022 Mario Carneiro, 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Egor Lyfar
-/

import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Data.List.Basic

/-!
# Stable propositional semantics for LRAT certificates

Adapted from `Mathlib/Tactic/Sat/FromLRAT.lean` (Apache-2.0).  This
project-owned interface deliberately contains only the definitions and
soundness lemmas needed by the local LRAT elaborator.
-/

namespace Erdos97Octagon.LRAT

/-- A positive or negative occurrence of a zero-based propositional variable. -/
inductive Literal where
  | positive : ℕ → Literal
  | negative : ℕ → Literal

/-- Translate a nonzero DIMACS integer into a literal. -/
def Literal.ofInt (value : Int) : Literal :=
  if value < 0 then .negative (-value - 1).toNat else .positive (value - 1).toNat

/-- Reverse the polarity of a literal. -/
def Literal.negate : Literal → Literal
  | .positive index => .negative index
  | .negative index => .positive index

/-- A clause is a disjunction represented as a list of literals. -/
abbrev Clause := List Literal

/-- A formula is a conjunction represented as a list of clauses. -/
abbrev Formula := List Clause

/-- A single clause viewed as a formula. -/
def Formula.one (clause : Clause) : Formula := [clause]

/-- Conjoin two formulas. -/
def Formula.and (left right : Formula) : Formula := left ++ right

/-- Every clause in `smaller` also occurs in `larger`. -/
structure Formula.Subsumes (larger smaller : Formula) : Prop where
  property : ∀ clause, clause ∈ smaller → clause ∈ larger

theorem Formula.subsumesSelf (formula : Formula) : formula.Subsumes formula :=
  ⟨fun _ membership => membership⟩

theorem Formula.subsumesLeft
    (formula left right : Formula) (h : formula.Subsumes (left.and right)) :
    formula.Subsumes left :=
  ⟨fun _ membership => h.property _ <| List.mem_append.mpr <| Or.inl membership⟩

theorem Formula.subsumesRight
    (formula left right : Formula) (h : formula.Subsumes (left.and right)) :
    formula.Subsumes right :=
  ⟨fun _ membership => h.property _ <| List.mem_append.mpr <| Or.inr membership⟩

/-- A proposition-valued assignment of all propositional variables. -/
abbrev Valuation := ℕ → Prop

/-- The assertion that a literal is false in a valuation. -/
def Valuation.falsifies (valuation : Valuation) : Literal → Prop
  | .positive index => ¬ valuation index
  | .negative index => valuation index

/-- The assertion that at least one literal in a clause is true. -/
def Valuation.satisfies (valuation : Valuation) : Clause → Prop
  | [] => False
  | literal :: clause => valuation.falsifies literal → valuation.satisfies clause

/-- A clause is satisfied when its literals are not all false. -/
theorem Valuation.satisfiesOfNotAllFalsified
    (valuation : Valuation) (clause : Clause)
    (h : ¬ List.Forall valuation.falsifies clause) :
    valuation.satisfies clause := by
  induction clause with
  | nil => simp at h
  | cons literal remaining inductionHypothesis =>
      intro hliteral
      apply inductionHypothesis
      intro hremaining
      apply h
      simpa using And.intro hliteral hremaining

/-- The assertion that every clause in a formula is satisfied. -/
structure Valuation.SatisfiesFormula
    (valuation : Valuation) (formula : Formula) : Prop where
  property : ∀ clause, clause ∈ formula → valuation.satisfies clause

/-- A clause follows semantically from a formula. -/
def Formula.Proves (formula : Formula) (clause : Clause) : Prop :=
  ∀ valuation : Valuation, valuation.SatisfiesFormula formula →
    valuation.satisfies clause

/-- Membership in a formula proves a clause. -/
theorem Formula.provesOfSubsumes {formula : Formula} {clause : Clause}
    (h : formula.Subsumes (Formula.one clause)) : formula.Proves clause :=
  fun _ satisfies => satisfies.property _ <| h.property _ <| List.Mem.head ..

/-- The sound unit-propagation case split. -/
theorem Valuation.propagateCases {valuation : Valuation} {literal : Literal}
    (positiveCase : valuation.falsifies literal.negate → False)
    (negativeCase : valuation.falsifies literal → False) : False :=
  match literal with
  | .positive _ => negativeCase positiveCase
  | .negative _ => positiveCase negativeCase

end Erdos97Octagon.LRAT
