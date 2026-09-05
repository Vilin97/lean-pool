/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Methods.EM.Indiscernible
/-!
# Ehrenfeucht–Mostowski templates for Lω₁ω

`Lomega1omegaTemplate L` assigns a truth value to every bounded Lω₁ω formula in every arity.
The downstream EM modules construct templates from indiscernible sequences and develop their
realization properties.
-/

universe u v

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

end FirstOrder.Language
