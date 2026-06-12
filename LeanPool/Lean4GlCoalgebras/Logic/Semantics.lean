/-
Copyright (c) 2026 Madeleine Gignoux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Madeleine Gignoux
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.FixedPoints
import Mathlib.Data.Set.Lattice
import LeanPool.Lean4GlCoalgebras.Logic.Syntax

/-! ## Semantics of GL

Here we supply the semantics of GL.
-/

namespace Lean4GlCoalgebras

/-- Kripke models for GL (note: we add the transitivity and con_wf conditions directly into our
    definition of a model, i.e. this is not a general definition of a Krike model!) -/
structure Model (α : Type) : Type where
  /-- Auxiliary declaration used in the GL coalgebra development. -/
  V : α → Nat → Prop
  /-- Auxiliary declaration used in the GL coalgebra development. -/
  R : α → α → Prop
  trans : ∀ {a b c : α}, R a b → R b c → R a c
  con_wf : WellFounded (Function.swap R)

/-- GL Models are irreflexive. -/
instance instModelIsIrref {α : Type} (M : Model α) : Std.Irrefl M.R where
  irrefl := fun a con ↦ (WellFounded.irrefl M.con_wf).irrefl a con

/-- Standard semantics for Kripke models. -/
@[simp]
def evaluate {α : Type} : Model α × α → Formula → Prop
  | (_, _), ⊥ => False
  | (_, _), ⊤ => True
  | (M, w), at n => M.V w n
  | (M, w), na n => ¬ M.V w n
  | (M, w), φ & ψ => evaluate (M, w) φ ∧ evaluate (M, w) ψ
  | (M, w), φ v ψ => evaluate (M, w) φ ∨ evaluate (M, w) ψ
  | (M, w), □ φ => ∀ (u : α), M.R w u → evaluate (M, u) φ
  | (M, w), ◇ φ => ∃ (u : α), M.R w u ∧ evaluate (M, u) φ

lemma evaluate_neg {α : Type} (M : Model α) (u : α) (φ : Formula) :
  ¬ evaluate (M, u) φ ↔ evaluate (M, u) (~φ) := by
  induction φ generalizing u <;> simp [Formula.neg, evaluate] <;> grind

@[simp]
lemma evaluate_and {α : Type} (M : Model α) (u : α) (φ ψ : Formula) :
  evaluate (M, u) (φ & ψ) ↔ (evaluate (M, u) φ ∧ evaluate (M, u) ψ) := by
  simp

lemma evaluate_imp {α : Type} (M : Model α) (u : α) (φ ψ : Formula) :
    evaluate (M, u) (φ ↣ ψ) ↔ (evaluate (M, u) φ → evaluate (M, u) ψ) := by
  simp [←evaluate_neg]
  tauto

/-- note: sequent are read disjunctively! -/
@[simp]
def evaluateSeq {α : Type} : Model α × α → Sequent → Prop :=
  fun M_u Γ ↦ ∃ φ ∈ Γ, evaluate M_u φ

/-- note: ignores the left/right annotation. -/
def evaluateSSeq {α : Type} : Model α × α → SplitSequent → Prop :=
  fun M_u Γ ↦ ∃ φ ∈ Γ, evaluate M_u (Sum.elim id id φ)

@[simp]
lemma not_evaluateSSeq {α : Type} {M_u : Model α × α} {Γ : SplitSequent} :
    ¬ evaluateSSeq M_u Γ ↔
      (∀ φ, Sum.inl φ ∈ Γ → ¬ evaluate M_u φ) ∧
        ∀ φ, Sum.inr φ ∈ Γ → ¬ evaluate M_u φ := by
  simp [evaluateSSeq]

/-- A formula is valid if it holds at every world in every GL model. -/
def Formula.isValid (φ : Formula) : Prop
  := ∀ (α : Type), ∀ M : Model α, ∀ u : α, evaluate ⟨M, u⟩ φ

/-- A sequent is valid if some formula in it holds at every world in every GL model. -/
def Sequent.isValid (Δ : Sequent) : Prop
  := ∀ (α : Type), ∀ M : Model α, ∀ u : α, evaluateSeq ⟨M, u⟩ Δ

/-- A split sequent is valid if some formula in it holds at every world in every GL model. -/
def SplitSequent.isValid (Δ : SplitSequent) : Prop
  := ∀ (α : Type), ∀ M : Model α, ∀ u : α, evaluateSSeq ⟨M, u⟩ Δ

/-- Auxiliary declaration used in the GL coalgebra development. -/
prefix:40 "⊨" => Formula.isValid
/-- Auxiliary declaration used in the GL coalgebra development. -/
prefix:40 "⊨" => Sequent.isValid
/-- Auxiliary declaration used in the GL coalgebra development. -/
prefix:40 "⊨" => SplitSequent.isValid

/-- Two formulas are semantically equivalent if their biconditional is valid. -/
def semEquiv : Formula → Formula → Prop := fun φ ψ ↦ ⊨ φ ⟷ ψ


/-- Model construction for substitution lemma. -/
def modelSubstitution {α} (M : Model α) (n : Nat) (φ : Formula) : Model α where
  V u k := if n = k then evaluate ⟨M, u⟩ φ else M.V u k
  R := M.R
  trans := M.trans
  con_wf := M.con_wf

/-- Substitution Lemma for modal logic! -/
lemma substitution_lemma {α} (M : Model α) (u : α) (n : Nat) (ψ : Formula)
  : ∀ φ, evaluate ⟨M, u⟩ (single n ψ φ) ↔ evaluate ⟨(modelSubstitution M n ψ), u⟩ φ := by
  intro φ
  induction φ generalizing u <;> simp_all [single, modelSubstitution] <;> try grind
  case atom k => aesop
  case negAtom k => if eq : k = n then simp [eq, evaluate_neg] else aesop

/-- Corollary of substitution lemma: If `φ` valid, then `φ[ψ/n]` is valid. -/
lemma single_preserves_validity (n : Nat) (φ ψ : Formula) : ⊨ φ → ⊨ single n ψ φ :=
  fun φ_val α M u ↦ (substitution_lemma M u n ψ φ).2 (φ_val α (modelSubstitution M n ψ) u)

/-- Corollary of substitution lemma: If `φ ⟷ ψ` valid, then `φ[χ/n] ⟷ ψ[χ/n]` is valid. -/
lemma single_preserves_sem_equiv (n : Nat) (χ φ ψ : Formula)
    (φ_equiv_ψ : ⊨ φ ⟷ ψ) : ⊨ (single n χ φ) ⟷ (single n χ ψ) := by
  convert single_preserves_validity n (φ ⟷ ψ) χ φ_equiv_ψ using 1
  simp [single_iff]
end Lean4GlCoalgebras
