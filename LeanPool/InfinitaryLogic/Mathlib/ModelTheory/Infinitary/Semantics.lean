/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import Mathlib.ModelTheory.Semantics
public import LeanPool.InfinitaryLogic.Mathlib.ModelTheory.Infinitary.Syntax
/-!
# Semantics of infinitary first-order formulas

This file defines realization of `L_{∞ω}` formulas in a structure, with simp lemmas for every
constructor and derived connective. Because the branching carrier is a type parameter, each
realization lemma is a single statement generic in the carrier and its universe — there is no
separate `L_{ω₁ω}` semantics, and no universe-specialized lemma set.

## Main definitions

- `FirstOrder.Language.BoundedFormulaInf.Realize`: realization with free-variable and
  bound-variable valuations.
- `FirstOrder.Language.FormulaInf.Realize`, `FirstOrder.Language.SentenceInf.Realize`.

## Main statements

- One `@[simp]` realization lemma per constructor and derived connective, each a single
  statement generic in the carrier and its universe (`realize_iInf`, `realize_alls`, …).
- `BoundedFormula.realize_toInf`: the carrier-generic finitary embedding preserves
  realization.

Realization of the coded connectives and of carrier transport is in
`Infinitary/Reindex.lean`.
-/

@[expose] public section

universe u v u' uι w

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} {ι : Type uι} {α : Type u'} {n : ℕ}

namespace BoundedFormulaInf

/-- Realization of an infinitary bounded formula in a structure, given valuations of the free
and bound variables. One recursion serves every carrier. -/
def Realize {M : Type w} [L.Structure M] :
    ∀ {n}, L.BoundedFormulaInf ι α n → (α → M) → (Fin n → M) → Prop
  | _, .falsum, _, _ => False
  | _, .equal t₁ t₂, v, xs => t₁.realize (Sum.elim v xs) = t₂.realize (Sum.elim v xs)
  | _, .rel R ts, v, xs => Structure.RelMap R fun i ↦ (ts i).realize (Sum.elim v xs)
  | _, .imp φ ψ, v, xs => Realize φ v xs → Realize ψ v xs
  | _, .all φ, v, xs => ∀ y : M, Realize φ v (Fin.snoc xs y)
  | _, .iSup φs, v, xs => ∃ i, Realize (φs i) v xs
  | _, .iInf φs, v, xs => ∀ i, Realize (φs i) v xs

variable {M : Type w} [L.Structure M] {v : α → M} {xs : Fin n → M}

@[simp]
theorem realize_falsum : (falsum : L.BoundedFormulaInf ι α n).Realize v xs ↔ False :=
  Iff.rfl

@[simp]
theorem realize_equal {t₁ t₂ : L.Term (α ⊕ Fin n)} :
    (equal t₁ t₂ : L.BoundedFormulaInf ι α n).Realize v xs ↔
      t₁.realize (Sum.elim v xs) = t₂.realize (Sum.elim v xs) :=
  Iff.rfl

@[simp]
theorem realize_rel {l : ℕ} {R : L.Relations l} {ts : Fin l → L.Term (α ⊕ Fin n)} :
    (rel R ts : L.BoundedFormulaInf ι α n).Realize v xs ↔
      Structure.RelMap R fun i ↦ (ts i).realize (Sum.elim v xs) :=
  Iff.rfl

@[simp]
theorem realize_imp {φ ψ : L.BoundedFormulaInf ι α n} :
    (φ.imp ψ).Realize v xs ↔ φ.Realize v xs → ψ.Realize v xs :=
  Iff.rfl

@[simp]
theorem realize_all {φ : L.BoundedFormulaInf ι α (n + 1)} :
    φ.all.Realize v xs ↔ ∀ y : M, φ.Realize v (Fin.snoc xs y) :=
  Iff.rfl

/-- Realization of an infinitary disjunction: one equation, generic in the carrier and its
universe. -/
@[simp]
theorem realize_iSup {φs : ι → L.BoundedFormulaInf ι α n} :
    (iSup φs).Realize v xs ↔ ∃ i, (φs i).Realize v xs :=
  Iff.rfl

/-- Realization of an infinitary conjunction: one equation, generic in the carrier and its
universe. -/
@[simp]
theorem realize_iInf {φs : ι → L.BoundedFormulaInf ι α n} :
    (iInf φs).Realize v xs ↔ ∀ i, (φs i).Realize v xs :=
  Iff.rfl

@[simp]
theorem realize_not {φ : L.BoundedFormulaInf ι α n} :
    φ.not.Realize v xs ↔ ¬φ.Realize v xs :=
  Iff.rfl

@[simp]
theorem realize_top : (⊤ : L.BoundedFormulaInf ι α n).Realize v xs ↔ True := by
  simp [Top.top, BoundedFormulaInf.verum, BoundedFormulaInf.not, Realize]

@[simp]
theorem realize_bot : (⊥ : L.BoundedFormulaInf ι α n).Realize v xs ↔ False :=
  Iff.rfl

@[simp]
theorem realize_ex {φ : L.BoundedFormulaInf ι α (n + 1)} :
    φ.ex.Realize v xs ↔ ∃ y : M, φ.Realize v (Fin.snoc xs y) := by
  simp only [BoundedFormulaInf.ex, realize_not, realize_all, not_forall, not_not]

end BoundedFormulaInf

/-- Realization of an `L_{∞ω}` formula (no free bound variables). -/
def FormulaInf.Realize {M : Type w} [L.Structure M] (φ : L.FormulaInf ι α) (v : α → M) : Prop :=
  BoundedFormulaInf.Realize φ v default

/-- Realization of an `L_{∞ω}` sentence in a structure. -/
def SentenceInf.Realize (φ : L.SentenceInf ι) (M : Type w) [L.Structure M] : Prop :=
  FormulaInf.Realize (M := M) φ Empty.elim

end Language

end FirstOrder
