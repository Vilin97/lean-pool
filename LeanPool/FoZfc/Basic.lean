/-
Copyright (c) 2026 Tetsuya Ishiu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuya Ishiu
-/

import Mathlib.Data.Set.Basic
import Mathlib.ModelTheory.Basic
import Mathlib.ModelTheory.Syntax
import Mathlib.ModelTheory.Semantics
import Mathlib.Data.Fin.Tuple.Basic

/-!
# The Basics of First Order Language of ZFC set theory

## Main Definitions

- A `FirstOrder.Language.LZFC` defines the language of ZFC set theory.
  It consists only of the binary relation ∈'.
- A `FirstOrder.ZFC.fv'` defines the free variable with index k.
  The first argument is implicitly determined.
- A `FirstOrder.ZFC.bv'` defines the bounded variable with index (k : Fin n).
  The first argument is implicitly determined.
- A `FirstOrder.ZFC.bv''` defines the bounded variable with index (k : ℕ).
  The first argument is implicitly determined.
- A `FirsOrder.ZFC.ModelSets` is a class of models of set theory.

## Notations

- ∈' is the symbol to mean "is an element of".
- ∉' is the symbol to mean "is not an element of".
- ≠' is the symbol to mean "is not equal to".
  Recall that =' is defined as FirstOrder.Language.Term.bdEqual.
- ∈ is the actual relation to mean "is an element of".
- ∉ is the actual relation to mean "is not an element of".

## Implimentation notes

- Most of the relations have the theorems named "realize_*".
  They prove the relationship between the internal and external expressions.

-/

namespace FirstOrder
open FirstOrder.Language
open FirstOrder.Language.BoundedFormula

-- u for universe, v for free variable indexes
universe u v

/-- Relation symbols for LSet. -/
inductive LSetRel : ℕ → Type
| is_elt_of : LSetRel 2
deriving DecidableEq

-- Instead of defining Relations n for each n,
-- define the entire Relations
namespace Language

/-- Language of Set Theory. -/
def LZFC : Language :=
{
  Functions := fun _ => Empty
  Relations := LSetRel
}

end Language

namespace ZFC

variable {V : Type u} [Language.LZFC.Structure V]

/-- The version of is_elt_of with the type LSet.Relations 2. -/
def is_elt_of_two : Language.LZFC.Relations 2 := LSetRel.is_elt_of

-- Language.BoundedFormula.falsum is the bot.
/-- The formula ⊥ -/
def ϕbot : Language.LZFC.Formula  ℕ:= Language.BoundedFormula.falsum

/-- Make an atomic formula t1 ∈ t2. -/
def ϕelt {n : ℕ} (t₁ t₂ : Language.LZFC.Term (ℕ ⊕ Fin n)) :=
  Language.Relations.boundedFormula₂ is_elt_of_two t₁ t₂

-- I added ' to distinguish the outside and inside ∈
@[inherit_doc] scoped[FirstOrder] infixl : 120 " ∈' " => FirstOrder.ZFC.ϕelt

/-- Make an atomic formula t1 ∉ t2. -/
def ϕnot_elt {n : ℕ} (t₁ t₂ : Language.LZFC.Term (ℕ ⊕ Fin n)) :=
  ∼(Language.Relations.boundedFormula₂ is_elt_of_two t₁ t₂)

@[inherit_doc] scoped[FirstOrder] infixl : 120 " ∉' " => FirstOrder.ZFC.ϕnot_elt

/-- The negation of the equality of two terms as a bounded formula. -/
def int_not_equal {n : ℕ} (t₁ t₂ : Language.LZFC.Term (ℕ ⊕ Fin n)) :=
    ∼(FirstOrder.Language.Term.bdEqual t₁ t₂)

@[inherit_doc] scoped[FirstOrder] infixl: 88 " ≠' " => FirstOrder.ZFC.int_not_equal

/-- Make a free variable in LSet. -/
def fv (n : ℕ) (k : ℕ) : Language.LZFC.Term (ℕ ⊕ Fin n) := Language.Term.var (Sum.inl k)

/-- Make a to-be bounded variable indexed by k, in which free variables are indexed by ℕ. -/
def bv (n : ℕ) (k : Fin n) : Language.LZFC.Term (ℕ ⊕ Fin n) := Language.Term.var (Sum.inr k)

/-- Model of set theory. -/
class ModelSets (V : Type u) extends LZFC.Structure V, Inhabited V where
  /-- The external membership relation interpreting the language's ∈ symbol. -/
  is_elt_of : V → V → Prop
  /-- The external relation matches the language's `RelMap`. -/
  interpret_is_elt_of : ∀ {a b : V}, is_elt_of a b ↔ RelMap is_elt_of_two ![a, b]
  /-- Extensionality: sets with the same elements are equal. -/
  extensionality : ∀ {a b : V}, (∀(z : V), (is_elt_of z a) ↔ is_elt_of z b) → a = b

variable {V : Type u}

/-- The negation of `ModelSets.is_elt_of`. -/
def not_is_elt_of [ModelSets V] (a b : V) : Prop :=
  ¬ (ModelSets.is_elt_of a b)

@[inherit_doc ModelSets.is_elt_of] infix : 120 " ∈ " => ModelSets.is_elt_of
@[inherit_doc not_is_elt_of] infix : 120 " ∉ " => not_is_elt_of

/-- Realize a free varaible. -/
@[simp]
theorem realize_fv [ModelSets V] {n : ℕ} {s : ℕ → V} {xs : Fin n → V} (k : ℕ) :
    Language.Term.realize (Sum.elim s xs) (fv n k) = s k := by
  exact rfl

/-- Realize a bounded variable with the type ℕ. -/
@[simp]
theorem realize_bv [ModelSets V] {n : ℕ} (s : ℕ → V) (xs : Fin n → V) (k : Fin n) :
    Language.Term.realize (Sum.elim s xs) (bv n k) = xs k := by
  rw [bv]
  simp

@[simp]
theorem realize_in [ModelSets V] {n : ℕ} {s : ℕ → V} {xs : Fin n → V}
    {t₁ t₂ : LZFC.Term (ℕ ⊕ Fin n)} :
    (t₁∈'t₂).Realize s xs ↔
      Term.realize (Sum.elim s xs) t₁ ∈ Term.realize (Sum.elim s xs) t₂ := by
  rw [ModelSets.interpret_is_elt_of]
  apply realize_rel₂

@[simp]
theorem realize_nin [ModelSets V] {n : ℕ} {s : ℕ → V} {xs : Fin n → V}
    {t₁ t₂ : LZFC.Term (ℕ ⊕ Fin n)} :
    (t₁∉'t₂).Realize s xs ↔
      Term.realize (Sum.elim s xs) t₁ ∉ Term.realize (Sum.elim s xs) t₂ := by
  apply not_congr realize_in

@[simp]
theorem realize_neq [ModelSets V] {n : ℕ} {s : ℕ → V} {xs : Fin n → V}
    {t₁ t₂ : LZFC.Term (ℕ ⊕ Fin n)} :
    (t₁≠'t₂).Realize s xs ↔
      Term.realize (Sum.elim s xs) t₁ ≠ Term.realize (Sum.elim s xs) t₂ := by
  unfold int_not_equal
  simp

/-- Make a free variable in LSet with n implicit. -/
def fv' {n : ℕ} (k : ℕ) : Language.LZFC.Term (ℕ ⊕ Fin n) := Language.Term.var (Sum.inl k)

/-- Make a to-be bounded variable indexed by (k : Fin n),
  in which free variables are indexed by ℕ with n implicit. -/
def bv' {n : ℕ} (k : Fin n) : Language.LZFC.Term (ℕ ⊕ Fin n) := Language.Term.var (Sum.inr k)

/-- Make a to-be bounded variable indexed by (k : ℕ),
  in which free variables are indexed by ℕ with n implicit. -/
def bv'' {n : ℕ} [NeZero n] (k : ℕ) : Language.LZFC.Term (ℕ ⊕ Fin n) :=
    Language.Term.var (Sum.inr (Fin.ofNat n k))

/-- Realize a free varaible. -/
@[simp]
theorem realize_fv' [ModelSets V] {n : ℕ} {s : ℕ → V} {xs : Fin n → V} (k : ℕ) :
    Language.Term.realize (Sum.elim s xs) (fv' k) = s k := by
  exact rfl

/-- Realize bv' with the type ℕ. -/
@[simp]
theorem realize_bv' [ModelSets V] {n : ℕ} (s : ℕ → V) (xs : Fin n → V) (k : Fin n) :
    Language.Term.realize (Sum.elim s xs) (bv' k) = xs k := by
  unfold bv'
  simp

/-- Realize bv'' with the type ℕ. -/
@[simp]
theorem realize_bv'' [ModelSets V] {n : ℕ} [NeZero n] (s : ℕ → V) (xs : Fin n → V) (k : ℕ) :
    Language.Term.realize (Sum.elim s xs) (bv'' k) = xs (Fin.ofNat n k) := by
  unfold bv''
  simp

end ZFC
end FirstOrder
