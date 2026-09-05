/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Lomega1omega.Semantics
/-!
# Finite quantifier blocks for Lω₁ω formulas

Finite blocks of existential and universal quantifiers over the last `k` bound variables,
with their realization semantics in `Fin.append` form.

## Main Definitions

- `FirstOrder.Language.BoundedFormulaω.existsBlock`: quantify the last `k` bound variables
  existentially, by iterating `ex`.
- `FirstOrder.Language.BoundedFormulaω.forallBlock`: the universal analogue, iterating `all`.

## Main Results

- `realize_existsBlock`: `(existsBlock φ).Realize v xs ↔ ∃ ys : Fin k → M,
  φ.Realize v (Fin.append xs ys)` — the first `n` coordinates remain the ambient bound
  environment and the last `k` coordinates are the block's witnesses.
- `realize_forallBlock`: the universal analogue.

## Implementation Notes

The environment in the realization lemmas is the plain `Fin.append xs ys` (well-typed since
`Fin (n + k)` is the formula's bound-variable index); the successor step is the standard
`Fin.snoc (Fin.append xs ys) y = Fin.append xs (Fin.snoc ys y)` exchange. This is reusable
syntax infrastructure independent of any particular application.
-/

universe u v w u'

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}}
variable {M : Type w} [L.Structure M]
variable {α : Type u'} {n : ℕ}

namespace BoundedFormulaω

/-- Existentially quantify the last `k` bound variables of a formula, by iterating `ex`. -/
def existsBlock : ∀ {k : ℕ}, L.BoundedFormulaω α (n + k) → L.BoundedFormulaω α n
  | 0, φ => φ
  | _ + 1, φ => existsBlock φ.ex

/-- Universally quantify the last `k` bound variables of a formula, by iterating `all`. -/
def forallBlock : ∀ {k : ℕ}, L.BoundedFormulaω α (n + k) → L.BoundedFormulaω α n
  | 0, φ => φ
  | _ + 1, φ => forallBlock φ.all

/-- Appending an empty tuple is the identity. -/
private theorem append_fin_zero {γ : Type*} (xs : Fin n → γ) (ys : Fin 0 → γ) :
    Fin.append xs ys = xs :=
  funext fun i => Fin.append_left xs ys i

/-- `Fin.snoc` distributes into `Fin.append` on the right component. -/
private theorem snoc_append_eq_append_snoc {γ : Type*} {k : ℕ}
    (xs : Fin n → γ) (ys : Fin k → γ) (y : γ) :
    Fin.snoc (Fin.append xs ys) y = Fin.append xs (Fin.snoc ys y) :=
  (Fin.append_snoc xs ys y).symm

variable {v : α → M} {xs : Fin n → M}

/-- Realization of a finite existential block: witnesses for the last `k` bound variables,
in `Fin.append` form. -/
theorem realize_existsBlock :
    ∀ {k : ℕ} (φ : L.BoundedFormulaω α (n + k)),
      (existsBlock φ).Realize v xs ↔ ∃ ys : Fin k → M, φ.Realize v (Fin.append xs ys)
  | 0, φ => by
    change φ.Realize v xs ↔ _
    constructor
    · exact fun h => ⟨Fin.elim0, by rwa [append_fin_zero]⟩
    · rintro ⟨ys, hy⟩
      rwa [append_fin_zero] at hy
  | k + 1, φ => by
    change (existsBlock φ.ex).Realize v xs ↔ _
    rw [realize_existsBlock φ.ex]
    constructor
    · rintro ⟨ys, hy⟩
      rw [realize_ex] at hy
      obtain ⟨y, hy⟩ := hy
      rw [snoc_append_eq_append_snoc] at hy
      exact ⟨Fin.snoc ys y, hy⟩
    · rintro ⟨zs, hz⟩
      refine ⟨Fin.init zs, (realize_ex _).mpr ⟨zs (Fin.last k), ?_⟩⟩
      rwa [snoc_append_eq_append_snoc, Fin.snoc_init_self]

/-- Realization of a finite universal block: all values of the last `k` bound variables,
in `Fin.append` form. -/
theorem realize_forallBlock :
    ∀ {k : ℕ} (φ : L.BoundedFormulaω α (n + k)),
      (forallBlock φ).Realize v xs ↔ ∀ ys : Fin k → M, φ.Realize v (Fin.append xs ys)
  | 0, φ => by
    change φ.Realize v xs ↔ _
    constructor
    · intro h ys
      rwa [append_fin_zero]
    · intro h
      have := h Fin.elim0
      rwa [append_fin_zero] at this
  | k + 1, φ => by
    change (forallBlock φ.all).Realize v xs ↔ _
    rw [realize_forallBlock φ.all]
    constructor
    · intro h zs
      have hz := (realize_all φ).mp (h (Fin.init zs)) (zs (Fin.last k))
      rwa [snoc_append_eq_append_snoc, Fin.snoc_init_self] at hz
    · intro h ys
      rw [realize_all]
      intro y
      rw [snoc_append_eq_append_snoc]
      exact h (Fin.snoc ys y)

end BoundedFormulaω

end Language

end FirstOrder
