/-
Copyright (c) 2026 Madeleine Gignoux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Madeleine Gignoux
-/

import LeanPool.Lean4GlCoalgebras.Logic.Syntax
import Mathlib.Data.Set.Defs
import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Functor.Const
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Defs
import Mathlib.CategoryTheory.Endofunctor.Algebra
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Basic
import Aesop
import Mathlib.Data.Setoid.Partition
import Mathlib.Data.Finset.Lattice.Basic

/-! ## Defining GL-ext+skip proof systems.

Here we define the GL-ext proof system along with finitization and basic properties. We use the
namespace ExtSkip to distinguish from our general GL-proofs.
-/

namespace Lean4GlCoalgebras

namespace ExtSkip

/-! # Basic components of the GL-ext+skip proof system.-/

/-- Rule applications for the GL-ext+skip proof system. -/
inductive RuleApp
  | skp : (Δ : SplitSequent) → RuleApp
  | cutₗ : (Δ : SplitSequent) → (A : Formula) → RuleApp
  | cutᵣ : (Δ : SplitSequent) → (A : Formula) → RuleApp
  | wkₗ : (Δ : SplitSequent) → (A : Formula) → (Sum.inl A) ∈ Δ → RuleApp
  | wkᵣ : (Δ : SplitSequent) → (A : Formula) → (Sum.inr A) ∈ Δ → RuleApp
  | topₗ : (Δ : SplitSequent) → (Sum.inl ⊤) ∈ Δ → RuleApp
  | topᵣ : (Δ : SplitSequent) → (Sum.inr ⊤) ∈ Δ → RuleApp
  | axₗₗ : (Δ : SplitSequent) → (n : Nat) → (Sum.inl (at n) ∈ Δ ∧ Sum.inl (na n) ∈ Δ) → RuleApp
  | axₗᵣ : (Δ : SplitSequent) → (n : Nat) → (Sum.inl (at n) ∈ Δ ∧ Sum.inr (na n) ∈ Δ) → RuleApp
  | axᵣₗ : (Δ : SplitSequent) → (n : Nat) → (Sum.inr (at n) ∈ Δ ∧ Sum.inl (na n) ∈ Δ) → RuleApp
  | axᵣᵣ : (Δ : SplitSequent) → (n : Nat) → (Sum.inr (at n) ∈ Δ ∧ Sum.inr (na n) ∈ Δ) → RuleApp
  | andₗ : (Δ : SplitSequent) → (A : Formula) → (B : Formula) → Sum.inl (A & B) ∈ Δ → RuleApp
  | andᵣ : (Δ : SplitSequent) → (A : Formula) → (B : Formula) → Sum.inr (A & B) ∈ Δ → RuleApp
  | orₗ : (Δ : SplitSequent) → (A : Formula) → (B : Formula) → Sum.inl (A v B) ∈ Δ → RuleApp
  | orᵣ : (Δ : SplitSequent) → (A : Formula) → (B : Formula) → Sum.inr (A v B) ∈ Δ → RuleApp
  | boxₗ : (Δ : SplitSequent) → (A : Formula) → Sum.inl (□ A) ∈ Δ → RuleApp
  | boxᵣ : (Δ : SplitSequent) → (A : Formula) → Sum.inr (□ A) ∈ Δ → RuleApp

/-- Endofunctor for the GL-ext+skip proof system. -/
@[simp] def T : (CategoryTheory.Functor Type Type) where
  obj := fun X ↦ (RuleApp × List X)
  map := fun {X Y} f ↦
    TypeCat.ofHom fun x ↦
      match x with
      | (r, A) => (r, A.map (CategoryTheory.ConcreteCategory.hom f))
  map_id := by aesop_cat
  map_comp := by aesop_cat

/-- Given a RuleApp, obtain the principal formulas. -/
def fₚ : RuleApp → SplitSequent
  | RuleApp.skp _ => ∅
  | RuleApp.cutₗ _ _ => ∅
  | RuleApp.cutᵣ _ _ => ∅
  | RuleApp.wkₗ _ A _ => {Sum.inl A}
  | RuleApp.wkᵣ _ A _ => {Sum.inr A}
  | RuleApp.topₗ _ _ => {Sum.inl ⊤}
  | RuleApp.topᵣ _ _ => {Sum.inr ⊤}
  | RuleApp.axₗₗ _ n _ => {Sum.inl (at n), Sum.inl (na n)}
  | RuleApp.axₗᵣ _ n _ => {Sum.inl (at n), Sum.inr (na n)}
  | RuleApp.axᵣₗ _ n _ => {Sum.inr (at n), Sum.inl (na n)}
  | RuleApp.axᵣᵣ _ n _ => {Sum.inr (at n), Sum.inr (na n)}
  | RuleApp.andₗ _ A B _ => {Sum.inl (A & B)}
  | RuleApp.andᵣ _ A B _ => {Sum.inr (A & B)}
  | RuleApp.orₗ _ A B _ => {Sum.inl (A v B)}
  | RuleApp.orᵣ _ A B _ => {Sum.inr (A v B)}
  | RuleApp.boxₗ _ A _ => {Sum.inl (□ A)}
  | RuleApp.boxᵣ _ A _ => {Sum.inr (□ A)}

/-- Given a RuleApp, obtain the split sequent. -/
def f : RuleApp → SplitSequent
  | RuleApp.skp Δ => Δ
  | RuleApp.cutₗ Δ _ => Δ
  | RuleApp.cutᵣ Δ _ => Δ
  | RuleApp.wkₗ Δ _ _ => Δ
  | RuleApp.wkᵣ Δ _ _ => Δ
  | RuleApp.topₗ Δ _ => Δ
  | RuleApp.topᵣ Δ _ => Δ
  | RuleApp.axₗₗ Δ _ _ => Δ
  | RuleApp.axₗᵣ Δ _ _ => Δ
  | RuleApp.axᵣₗ Δ _ _ => Δ
  | RuleApp.axᵣᵣ Δ _ _ => Δ
  | RuleApp.andₗ Δ _ _ _ => Δ
  | RuleApp.andᵣ Δ _ _ _ => Δ
  | RuleApp.orₗ Δ _ _ _ => Δ
  | RuleApp.orᵣ Δ _ _ _ => Δ
  | RuleApp.boxₗ Δ _ _ => Δ
  | RuleApp.boxᵣ Δ _ _ => Δ

/-- Given a RuleApp, obtain the non-principal formulas. -/
def fₙ : RuleApp → SplitSequent := fun r ↦ f r \ fₚ r

/-- Relating principal formulas, non-principal formulas, and the split sequent. -/
lemma fₙ_alternate (r : RuleApp) : fₙ r = match r with
  | RuleApp.skp Δ => Δ
  | RuleApp.cutₗ Δ _ => Δ
  | RuleApp.cutᵣ Δ _ => Δ
  | RuleApp.wkₗ Δ A _ =>  Δ \ {Sum.inl A}
  | RuleApp.wkᵣ Δ A _ =>  Δ \ {Sum.inr A}
  | RuleApp.topₗ Δ _ => Δ \ {Sum.inl ⊤}
  | RuleApp.topᵣ Δ _ => Δ \ {Sum.inr ⊤}
  | RuleApp.axₗₗ Δ n _ => Δ \ {Sum.inl (at n), Sum.inl (na n)}
  | RuleApp.axₗᵣ Δ n _ => Δ \ {Sum.inl (at n), Sum.inr (na n)}
  | RuleApp.axᵣₗ Δ n _ => Δ \ {Sum.inr (at n), Sum.inl (na n)}
  | RuleApp.axᵣᵣ Δ n _ => Δ \ {Sum.inr (at n), Sum.inr (na n)}
  | RuleApp.andₗ Δ A B _ => Δ \ {Sum.inl (A & B)}
  | RuleApp.andᵣ Δ A B _ => Δ \ {Sum.inr (A & B)}
  | RuleApp.orₗ Δ A B _ => Δ \ {Sum.inl (A v B)}
  | RuleApp.orᵣ Δ A B _ => Δ \ {Sum.inr (A v B)}
  | RuleApp.boxₗ Δ A _ => Δ \ {Sum.inl (□ A)}
  | RuleApp.boxᵣ Δ A _ => Δ \ {Sum.inr (□ A)} := by cases r <;> simp [fₙ, f, fₚ]

/-- Auxiliary declaration used in the GL coalgebra development. -/
def RuleApp.isBox : RuleApp → Prop
  | RuleApp.boxₗ _ _ _ => true
  | RuleApp.boxᵣ _ _ _ => true
  | _ => false

/-- Get RuleApp of a node (first projection). -/
def r {X : Type} (α : X → T.obj X) (x : X) := (α x).1

/-- Get premises of a node (second projection). -/
def p {X : Type} (α : X → T.obj X) (x : X) := (α x).2

/-- Edge relation induced by `p`. -/
def edge {X : Type} (α : X → T.obj X) (x y : X) : Prop := y ∈ p α x

/-- Definition of GL-ext+skip proof. -/
structure Proof where
  /-- Auxiliary declaration used in the GL coalgebra development. -/
  X : Type
  /-- Auxiliary declaration used in the GL coalgebra development. -/
  α : X → T.obj X
  step : ∀ (x : X), match r α x with
    | RuleApp.skp _ => (p α x).map (fun x ↦ f (r α x)) = [(f (r α x))]
    | RuleApp.cutₗ _ A =>
        (p α x).map (fun x ↦ f (r α x)) =
          [(fₙ (r α x)).filterRight ∪ {Sum.inl A},
            (fₙ (r α x)).filterLeft ∪ {Sum.inr (~A)}]
    | RuleApp.cutᵣ _ A =>
        (p α x).map (fun x ↦ f (r α x)) =
          [(fₙ (r α x)).filterLeft ∪ {Sum.inr A},
            (fₙ (r α x)).filterRight ∪ {Sum.inl (~A)}]
    | RuleApp.wkₗ _ _ _ => (p α x).map (fun x ↦ f (r α x)) = [fₙ (r α x)]
    | RuleApp.wkᵣ _ _ _ => (p α x).map (fun x ↦ f (r α x)) = [fₙ (r α x)]
    | RuleApp.topₗ _ _ => p α x = ∅
    | RuleApp.topᵣ _ _ => p α x = ∅
    | RuleApp.axₗₗ _ _ _ => p α x = ∅
    | RuleApp.axₗᵣ _ _ _ => p α x = ∅
    | RuleApp.axᵣₗ _ _ _ => p α x = ∅
    | RuleApp.axᵣᵣ _ _ _ => p α x = ∅
    | RuleApp.andₗ _ A B _ =>
        (p α x).map (fun x ↦ f (r α x)) =
          [(fₙ (r α x)) ∪ {Sum.inl A}, (fₙ (r α x)) ∪ {Sum.inl B}]
    | RuleApp.andᵣ _ A B _ =>
        (p α x).map (fun x ↦ f (r α x)) =
          [(fₙ (r α x)) ∪ {Sum.inr A}, (fₙ (r α x)) ∪ {Sum.inr B}]
    | RuleApp.orₗ _ A B _ =>
        (p α x).map (fun x ↦ f (r α x)) =
          [(fₙ (r α x)) ∪ {Sum.inl A, Sum.inl B}]
    | RuleApp.orᵣ _ A B _ =>
        (p α x).map (fun x ↦ f (r α x)) =
          [(fₙ (r α x)) ∪ {Sum.inr A, Sum.inr B}]
    | RuleApp.boxₗ _ A _ =>
        (p α x).map (fun x ↦ f (r α x)) = [(fₙ (r α x)).D ∪ {Sum.inl A}]
    | RuleApp.boxᵣ _ A _ =>
        (p α x).map (fun x ↦ f (r α x)) = [(fₙ (r α x)).D ∪ {Sum.inr A}]
  path : ∀ x, ∀ f : {f : ℕ → X // f 0 = x ∧ ∀ (n : ℕ), edge α (f n) (f (n + 1))},
    ∀ n, ∃ m, (r α (f.1 (n + m))).isBox

/-- Auxiliary declaration used in the GL coalgebra development. -/
def proves (𝕏 : Proof) (Δ : SplitSequent) : Prop := ∃ x : 𝕏.X, f (r 𝕏.α x) = Δ
/-- Auxiliary declaration used in the GL coalgebra development. -/
def SplitSequent.isTrue (Δ : SplitSequent) : Prop := ∃ (𝕏 : Proof), proves 𝕏 Δ

/-- Auxiliary declaration used in the GL coalgebra development. -/
infixr:6 "⊢" => proves
/-- Auxiliary declaration used in the GL coalgebra development. -/
prefix:40 "⊢" => SplitSequent.isTrue

end ExtSkip
end Lean4GlCoalgebras
