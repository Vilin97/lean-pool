/-
Copyright (c) 2026 Jim Fowler, Dennis Sweeney. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jim Fowler, Dennis Sweeney
-/
module

public import LeanPool.OneManifold.OneMfld.Classification


/-!
# Proved solution

This module imports the full proof development and restates the upstream Challenge
theorem with the identical name and type. The library's `OneMfld.classification`
(in `OneMfld/Classification.lean`) produces the homeomorphism as data, as a
term of `(M ≃ₜ Circle) ⊕ (M ≃ₜ UnitInterval)`; here we only need the
Prop-level disjunction. The Challenge's `{x : ℝ // 0 ≤ x ∧ x ≤ 1}` is
definitionally `↥OneMfld.UnitInterval` (and Mathlib's `↥unitInterval`).
-/

@[expose] public section

namespace OneMfld

theorem homeomorph_circle_or_unitInterval
    (M : Type*) [TopologicalSpace M] [CompactSpace M] [ConnectedSpace M]
    [T2Space M] [ChartedSpace NNReal M] :
    Nonempty (M ≃ₜ Circle) ∨ Nonempty (M ≃ₜ {x : ℝ // 0 ≤ x ∧ x ≤ 1}) := by
  rcases classification (M := M) ‹ChartedSpace NNReal M› with e | e
  · exact Or.inl ⟨e⟩
  · exact Or.inr ⟨e⟩

end OneMfld
