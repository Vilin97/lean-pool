/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Methods.EM.Indiscernible
/-!
# Ehrenfeucht–Mostowski templates for Lω₁ω

This file introduces the intermediate object that bridges Lω₁ω-indiscernible
sequences and Ehrenfeucht–Mostowski (EM) stretching: a *template* assigns to
each `n` and each formula `φ : L.BoundedFormulaω Empty n` the truth value of
`φ` on increasing `n`-tuples drawn from an indiscernible sequence. A second
sequence `b : J → N` *realizes* the template if its truth values on increasing
tuples agree with the template's.

## Main definitions

- `Lomega1omegaTemplate L`: a template for an Lω₁ω formula language `L`,
  i.e. an assignment `φ ↦ Prop` for every `φ : L.BoundedFormulaω Empty n`.
- `Lomega1omegaTemplate.RealizesOn T b`: a sequence `b : J → N` realizes the
  template `T` if every formula's truth value on every strictly increasing
  tuple from `J` agrees with `T φ`.
- `IsLomega1omegaIndiscernible.template`: the template induced by an
  indiscernible sequence, defined existentially (so well-defined without any
  extra assumption on the index set).

## Main results

- `IsLomega1omegaIndiscernible.template_truth_iff`: well-definedness — the
  template's value at `φ` agrees with `φ.Realize (a ∘ s)` for any strictly
  increasing tuple `s`. Uses `iff_realize` from `Indiscernible.lean`.
- `IsLomega1omegaIndiscernible.realizesTemplate`: an indiscernible sequence
  realizes its own template.
- `IsLomega1omegaIndiscernible.realizesTemplate_restrict`: restricting the
  index set along an order embedding still realizes the *same* template.
- `IsLomega1omegaIndiscernible.template_reindex`: reindexing along an order
  isomorphism produces a definitionally equal template.

This file does **not** prove anything about EM stretching itself; it only sets
up the template object and its basic invariance properties.
-/

universe u v w

namespace FirstOrder.Language

variable {L : Language.{u, v}}

/-- A template for the language `L` of Lω₁ω formulas: an assignment of a truth
value to every Lω₁ω formula in every arity, with no free variables. Intended to
record the "common truth value on increasing `n`-tuples" of an indiscernible
sequence. -/
@[ext]
structure Lomega1omegaTemplate (L : Language.{u, v}) where
  /-- The truth value assigned to a formula. -/
  truth : ∀ {n : ℕ}, L.BoundedFormulaω Empty n → Prop

namespace Lomega1omegaTemplate

variable {N : Type*} [L.Structure N] {J : Type*} [LinearOrder J]

end Lomega1omegaTemplate

namespace IsLomega1omegaIndiscernible

variable {I : Type w} [LinearOrder I] {M : Type*} [L.Structure M]

end IsLomega1omegaIndiscernible

/-! ### Restricted-indiscernibility API for `templateOfSeq` -/

namespace IsLomega1omegaIndiscernibleOn

variable {I : Type w} [LinearOrder I] {M : Type*} [L.Structure M]

end IsLomega1omegaIndiscernibleOn

end FirstOrder.Language
