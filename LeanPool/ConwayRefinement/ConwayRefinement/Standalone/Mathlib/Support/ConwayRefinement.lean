/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import Mathlib.Algebra.Group.Defs

/-!
# Conway's four-factor refinement statement

This file records the logical form of Conway's statement without choosing a construction of the
surreal numbers or the omnific integers. Given a predicate `P` on a type with multiplication, the
statement says that every equation `a * b = c * d` among `P`-elements admits Conway's
four-factor refinement.

Concrete developments may instantiate `P` by Conway's cut definition of the omnific integers or
by membership in a Hahn integer part. This module imports only Mathlib.
-/

public section

namespace ConwayRefinement.Standalone

universe u

variable {R : Type u} [Mul R]

/-- Conway's four-factor refinement schema for a predicate `P`: from `a * b = c * d`, produce
`a = e * f`, `b = g * h`, `c = e * g`, and `d = f * h`, with all eight entries satisfying `P`. -/
def ConwayRefinement (P : R → Prop) : Prop :=
  ∀ a b c d : R,
    P a → P b → P c → P d → a * b = c * d →
    ∃ e f g h : R,
      P e ∧ P f ∧ P g ∧ P h ∧
      a = e * f ∧ b = g * h ∧ c = e * g ∧ d = f * h

/-- The standalone proposition unfolds to the four equations in Conway's refinement conjecture. -/
theorem conwayRefinement_iff (P : R → Prop) : ConwayRefinement P ↔
    ∀ a b c d : R,
      P a → P b → P c → P d → a * b = c * d →
      ∃ e f g h : R,
        P e ∧ P f ∧ P g ∧ P h ∧
        a = e * f ∧ b = g * h ∧ c = e * g ∧ d = f * h := (Iff.rfl)

end ConwayRefinement.Standalone

/-!
## Formal proof

Proof module: `ConwayRefinementProof`.

* `ConwayRefinement` → `ConwayRefinement.refine`
-/
