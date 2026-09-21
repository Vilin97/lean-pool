/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Standalone.Mathlib.Support.ConwayRefinement

/-!
# Public interface for four-factor refinement

This proof sibling supplies the module-safe eliminator for the standalone proposition.
-/

public section

namespace ConwayRefinement.Standalone.ConwayRefinement

universe u

variable {R : Type u} [Mul R] {P : R → Prop}

/-- Apply four-factor refinement to one product equation. -/
theorem refine (hc : ConwayRefinement P)
    {a b c d : R} (ha : P a) (hb : P b) (hc' : P c) (hd : P d)
    (heq : a * b = c * d) :
    ∃ e f g h : R,
      P e ∧ P f ∧ P g ∧ P h ∧
      a = e * f ∧ b = g * h ∧ c = e * g ∧ d = f * h := by
  exact conwayRefinement_iff P |>.mp hc a b c d ha hb hc' hd heq

end ConwayRefinement.Standalone.ConwayRefinement
