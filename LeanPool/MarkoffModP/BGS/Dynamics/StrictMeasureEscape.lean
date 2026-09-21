/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import Mathlib.Logic.Relation
import Mathlib.Data.Nat.Order.Lemmas
import Mathlib.Tactic

namespace BGS

universe u


/-- If every state below a target measure admits a relation step that strictly raises the
measure, then finitely many such steps reach the target. -/
theorem exists_reflTransGen_measure_ge
    {X : Type u} (r : X → X → Prop) (measure : X → ℕ) (target : ℕ)
    (step : ∀ x, measure x < target → ∃ y, r x y ∧ measure x < measure y)
    (x : X) :
    ∃ y, Relation.ReflTransGen r x y ∧ target ≤ measure y := by
  by_cases hx : target ≤ measure x
  · exact ⟨x, Relation.ReflTransGen.refl, hx⟩
  · have hxlt : measure x < target := Nat.lt_of_not_ge hx
    obtain ⟨y, hxy, hmeasure⟩ := step x hxlt
    obtain ⟨z, hyz, hz⟩ :=
      exists_reflTransGen_measure_ge r measure target step y
    exact ⟨z, Relation.ReflTransGen.head hxy hyz, hz⟩
termination_by target - measure x
decreasing_by omega

end BGS
