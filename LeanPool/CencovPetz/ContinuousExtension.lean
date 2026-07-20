/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import LeanPool.CencovPetz.SimplexTopology


/-!
# `CencovPetz.ContinuousExtension`

Reusable “extend equality from a dense set” lemmas for functions on the finite open simplex.

This is used in the last step of the finite Čencov/Chentsov argument: once an identity is shown
on a dense family of rational/common-denominator points, continuity hypotheses allow extending the
identity to all simplex points.

## Main result

- `CencovPetz.eq_of_eqOn_dense₂`
-/

namespace LeanPool.CencovPetz
open scoped BigOperators

universe u

variable {α : Type u} [Fintype α]

lemma eq_of_eqOn_dense₂ {s : Set (Simplex α)} (hs : Dense s)
    {f g : Simplex α → tangentSpace (α := α) → tangentSpace (α := α) → ℝ}
    (hf : ∀ u v, Continuous fun p : Simplex α => f p u v)
    (hg : ∀ u v, Continuous fun p : Simplex α => g p u v)
    (hfg : ∀ p ∈ s, ∀ u v, f p u v = g p u v) :
    ∀ p u v, f p u v = g p u v := by
  intro p u v
  have hEqOn :
      Set.EqOn (fun p : Simplex α => f p u v) (fun p : Simplex α => g p u v) s := by
    intro p hp
    exact hfg p hp u v
  have hfun :
      (fun p : Simplex α => f p u v) = fun p : Simplex α => g p u v :=
    Continuous.ext_on (X := ℝ) (Y := Simplex α) hs (hf u v) (hg u v) hEqOn
  exact congrArg (fun h => h p) hfun
end LeanPool.CencovPetz
