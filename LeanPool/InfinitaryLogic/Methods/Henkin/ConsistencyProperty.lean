/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Lomega1omega.Theory
import LeanPool.InfinitaryLogic.Lomega1omega.Operations
/-!
# Consistency Properties

This file defines the notion of a consistency property for Lω₁ω, following
Marker's axiomatization (C0)-(C7). A consistency property is a family of sets
of sentences satisfying closure conditions that guarantee model existence.

## Main Definitions

- `ConsistencyProperty`: A family of sets of Lω₁ω sentences satisfying the
  consistency axioms (C0)-(C7).

## References

- [Mar16], §4.1
- [Kei71]
-/

universe u v

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}}

open FirstOrder Structure

/-- A basic consistency property for Lω₁ω sentences, with only propositional and
infinitary connective axioms (C0)-(C4).

**Note**: This is insufficient for model existence on its own, since it allows
contradictory sets (e.g., containing both φ and ¬φ without containing ⊥).
Use `ConsistencyPropertyEq` for the full model existence theorem. -/
structure ConsistencyProperty (L : Language.{u, v}) where
  /-- The family of consistent sets. -/
  sets : Set (Set L.Sentenceω)
  /-- (C0a) No set in the family contains falsum. -/
  C0_no_falsum : ∀ S ∈ sets, (BoundedFormulaω.falsum : L.Sentenceω) ∉ S
  /-- (C0b) No set in the family contains both a sentence and its negation. -/
  C0_no_contradiction : ∀ S ∈ sets, ∀ φ : L.Sentenceω, ¬(φ ∈ S ∧ φ.not ∈ S)
  /-- (C1) Closure under implication decomposition: if φ → ψ ∈ S, then either
      S ∪ {¬φ} or S ∪ {ψ} is in the family. -/
  C1_imp : ∀ S ∈ sets, ∀ φ ψ : L.Sentenceω,
    BoundedFormulaω.imp φ ψ ∈ S →
    S ∪ {φ.not} ∈ sets ∨ S ∪ {ψ} ∈ sets
  /-- (C1') Negated implication decomposition: if ¬(φ → ψ) ∈ S, then both
      S ∪ {φ} and S ∪ {¬ψ} are in the family. This is the dual of C1, needed
      for the backward direction of the truth lemma. In model-theoretic terms:
      if φ → ψ is false in every model of S, then φ must be true and ψ false. -/
  C1_neg_imp : ∀ S ∈ sets, ∀ φ ψ : L.Sentenceω,
    (BoundedFormulaω.imp φ ψ).not ∈ S →
    S ∪ {φ} ∈ sets ∧ S ∪ {ψ.not} ∈ sets
  /-- (C2) Double negation elimination: if ¬¬φ ∈ S, then S ∪ {φ} is consistent. -/
  C2_not_not : ∀ S ∈ sets, ∀ φ : L.Sentenceω,
    φ.not.not ∈ S → S ∪ {φ} ∈ sets
  /-- (C3) Closure under countable conjunction: if ⋀ᵢ φᵢ ∈ S, then S ∪ {φₖ} is
      consistent for all k. -/
  C3_iInf : ∀ S ∈ sets, ∀ φs : ℕ → L.Sentenceω,
    BoundedFormulaω.iInf φs ∈ S → ∀ k, S ∪ {φs k} ∈ sets
  /-- (C3') Negated conjunction decomposition: if ¬(⋀ᵢ φᵢ) ∈ S, then there exists k
      such that S ∪ {¬φₖ} is consistent. This is the dual of C3. -/
  C3_neg_iInf : ∀ S ∈ sets, ∀ φs : ℕ → L.Sentenceω,
    (BoundedFormulaω.iInf φs).not ∈ S → ∃ k, S ∪ {(φs k).not} ∈ sets
  /-- (C4) Witness for countable disjunction: if ⋁ᵢ φᵢ ∈ S, then there exists k
      such that S ∪ {φₖ} is consistent. -/
  C4_iSup : ∀ S ∈ sets, ∀ φs : ℕ → L.Sentenceω,
    BoundedFormulaω.iSup φs ∈ S → ∃ k, S ∪ {φs k} ∈ sets
  /-- (C4') Negated disjunction decomposition: if ¬(⋁ᵢ φᵢ) ∈ S, then S ∪ {¬φₖ} is
      consistent for all k. This is the dual of C4. -/
  C4_neg_iSup : ∀ S ∈ sets, ∀ φs : ℕ → L.Sentenceω,
    (BoundedFormulaω.iSup φs).not ∈ S → ∀ k, S ∪ {(φs k).not} ∈ sets
  /-- (Extension) For any consistent S and sentence φ, either S ∪ {φ} or
      S ∪ {¬φ} is consistent. This ensures maximal consistent extensions decide
      every sentence. In the standard consistency property for satisfiable sets,
      this holds because any model of S satisfies either φ or ¬φ. -/
  extension : ∀ S ∈ sets, ∀ φ : L.Sentenceω, S ∪ {φ} ∈ sets ∨ S ∪ {φ.not} ∈ sets
  /-- Chain closure: the union of a nonempty ⊆-chain of consistent sets is
      consistent. This enables the Zorn's lemma argument for maximal consistent
      extensions. In standard presentations, this follows from the finite character
      of consistency (S is consistent iff every finite subset is). -/
  chain_closure : ∀ (chain : Set (Set L.Sentenceω)),
    chain ⊆ sets → IsChain (· ⊆ ·) chain → chain.Nonempty →
    ⋃₀ chain ∈ sets

/-- A consistency property with equality and quantifier axioms (C0)-(C7).

This extends `ConsistencyProperty` with the conditions needed for the Henkin
construction in the model existence theorem. Without these, `ConsistencyProperty`
alone is too weak to guarantee model existence (it allows contradictory sets
that contain both φ and ¬φ without containing ⊥).

**Design note**: Formulas with a "hole" (one free variable) are represented as
`L.Formulaω (Fin 1)` (= `BoundedFormulaω (Fin 1) 0`). Substitution of a closed
term `t : L.Term Empty` into such a formula uses `φ.subst (fun _ => t)`, which
produces a sentence (`Formulaω Empty = Sentenceω`). The quantifier axiom (C7)
requires Henkin witnesses — fresh constant symbols that witness existential
statements. Callers construct these via `L[[ℕ]]` (Mathlib's
`Language.withConstants`) for the standard Henkin construction. -/
structure ConsistencyPropertyEq (L : Language.{u, v}) extends ConsistencyProperty L where
  /-- (C5) Equality is reflexive: for any closed term t, S ∪ {t = t} is consistent. -/
  C5_eq_refl : ∀ S ∈ toConsistencyProperty.sets,
    ∀ t : L.Term (Empty ⊕ Fin 0), S ∪ {BoundedFormulaω.equal t t} ∈ toConsistencyProperty.sets
  /-- (C6) Substitution of equals: if t₁ = t₂ ∈ S and φ(t₁) ∈ S, then
      S ∪ {φ(t₂)} is consistent. Here φ is a formula with one free variable
      (`Fin 1`), and `φ.subst (fun _ => tᵢ)` substitutes a closed term to
      produce a sentence. -/
  C6_eq_subst : ∀ S ∈ toConsistencyProperty.sets,
    ∀ (t₁ t₂ : L.Term Empty) (φ : L.Formulaω (Fin 1)),
      BoundedFormulaω.equal
        (t₁.relabel (Sum.inl : Empty → Empty ⊕ Fin 0))
        (t₂.relabel (Sum.inl : Empty → Empty ⊕ Fin 0)) ∈ S →
      φ.subst (fun _ => t₁) ∈ S →
      S ∪ {φ.subst (fun _ => t₂)} ∈ toConsistencyProperty.sets
  /-- (C7) Quantifier witness: if ∃x φ(x) ∈ S, then there exists a closed term t
      such that S ∪ {φ(t)} is consistent. Here φ has one free variable (`Fin 1`),
      and the existential `(φ.relabel (Sum.inr : Fin 1 → Empty ⊕ Fin 1)).ex`
      converts it to a sentence with one bound variable and takes its existential.
      In the full Henkin construction, the witnesses come from Henkin constants. -/
  C7_quantifier : ∀ S ∈ toConsistencyProperty.sets,
    ∀ (φ : L.Formulaω (Fin 1)),
      (φ.relabel (Sum.inr : Fin 1 → Empty ⊕ Fin 1)).ex ∈ S →
      ∃ (t : L.Term Empty),
        S ∪ {φ.subst (fun _ => t)} ∈ toConsistencyProperty.sets
  /-- (C7') Universal instantiation: if ∀x φ(x) ∈ S, then S ∪ {φ(t)} is consistent
      for every closed term t. Here φ has one free variable (`Fin 1`),
      and `(φ.relabel (Sum.inr : Fin 1 → Empty ⊕ Fin 1)).all` converts it to a
      sentence with one bound variable and takes its universal quantification. -/
  C7_all : ∀ S ∈ toConsistencyProperty.sets,
    ∀ (φ : L.Formulaω (Fin 1)),
      (φ.relabel (Sum.inr : Fin 1 → Empty ⊕ Fin 1)).all ∈ S →
      ∀ (t : L.Term Empty),
        S ∪ {φ.subst (fun _ => t)} ∈ toConsistencyProperty.sets
  /-- (C7'') Negated universal decomposition: if ¬(∀x.φ(x)) ∈ S, then there exists a closed
      term t such that S ∪ {¬φ(t)} is consistent. This is the dual of C7_all, needed for the
      backward direction of the truth lemma's universal quantifier case. -/
  C7_neg_all : ∀ S ∈ toConsistencyProperty.sets,
    ∀ (φ : L.Formulaω (Fin 1)),
      ((φ.relabel (Sum.inr : Fin 1 → Empty ⊕ Fin 1)).all).not ∈ S →
      ∃ (t : L.Term Empty),
        S ∪ {(φ.subst (fun _ => t)).not} ∈ toConsistencyProperty.sets
  /-- (C7''') Negated existential decomposition: if ¬(∃x.φ(x)) ∈ S, then S ∪ {¬φ(t)} is
      consistent for every closed term t. This is the dual of C7_quantifier. -/
  C7_neg_ex : ∀ S ∈ toConsistencyProperty.sets,
    ∀ (φ : L.Formulaω (Fin 1)),
      ((φ.relabel (Sum.inr : Fin 1 → Empty ⊕ Fin 1)).ex).not ∈ S →
      ∀ (t : L.Term Empty),
        S ∪ {(φ.subst (fun _ => t)).not} ∈ toConsistencyProperty.sets
  /-- Direct universal instantiation for `BoundedFormulaω.all`: if `∀x.φ(x) ∈ S`,
      then S ∪ {φ(t)} is consistent for every closed term t. Here φ has one bound
      variable (type `BoundedFormulaω Empty 1`), and `φ.openBounds : Formulaω (Fin 1)`
      converts it to a formula with one free variable for substitution. -/
  C7_all_bound : ∀ S ∈ toConsistencyProperty.sets,
    ∀ (φ : L.BoundedFormulaω Empty 1),
      φ.all ∈ S →
      ∀ (t : L.Term Empty),
        S ∪ {(φ.openBounds).subst (fun _ => t)} ∈ toConsistencyProperty.sets
  /-- Direct negated universal for `BoundedFormulaω.all`: if ¬(∀x.φ(x)) ∈ S,
      then there exists a term t with S ∪ {¬φ(t)} consistent. -/
  C7_neg_all_bound : ∀ S ∈ toConsistencyProperty.sets,
    ∀ (φ : L.BoundedFormulaω Empty 1),
      φ.all.not ∈ S →
      ∃ (t : L.Term Empty),
        S ∪ {((φ.openBounds).subst (fun _ => t)).not} ∈ toConsistencyProperty.sets

end Language

end FirstOrder
