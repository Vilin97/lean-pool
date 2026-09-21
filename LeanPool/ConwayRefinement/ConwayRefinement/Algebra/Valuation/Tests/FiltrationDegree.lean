/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.Valuation.FiltrationDegree

/-!
# API checks for the degree attached to a separated filtration

For a nonzero element, `index` is the largest filtration stage containing it. Thus the element
lies in the stage indexed by its index and not in the next stage.

The value lies in `WithBot (OrderDual ℕ)`: deeper filtration stages give smaller values, as
required for a max-additive degree. Membership in stage `F j` is therefore equivalent to the
corresponding upper bound on the value. The final checks record zero detection, separatedness,
and the weak and strict filtrations recovered from this degree.
-/

public noncomputable section

namespace Tests

universe u

variable {R : Type u} [CommRing R] {F : ℕ → Ideal R}

/-- A nonzero element lies in the filtration stage indexed by its index. -/
theorem mem_filtration_index (hF : IsSeparatedFiltration F) {x : R} (hx : x ≠ 0) :
    x ∈ F (hF.index hx) :=
  (hF.mem_iff_le_index hx _).mpr le_rfl

/-- A nonzero element does not lie in the stage immediately above its index. -/
theorem not_mem_filtration_index_succ (hF : IsSeparatedFiltration F) {x : R}
    (hx : x ≠ 0) :
    x ∉ F (hF.index hx + 1) := by
  rw [hF.mem_iff_le_index hx]
  omega

/-- The value is antitone in the index: deeper filtration means smaller value. -/
theorem value_antitone_of_index_le (hF : IsSeparatedFiltration F) {x y : R}
    (hx : x ≠ 0) (hy : y ≠ 0) (h : hF.index hx ≤ hF.index hy) :
    hF.value y ≤ hF.value x := by
  rw [hF.value_of_ne_zero hx, hF.value_of_ne_zero hy, WithBot.coe_le_coe]
  exact OrderDual.toDual_le_toDual.mpr h

/-- Membership in a filtration stage is equivalent to the corresponding upper bound on the
value. -/
theorem mem_iff_value_le (hF : IsSeparatedFiltration F) (x : R) (j : ℕ) :
    x ∈ F j ↔ hF.value x ≤ ((OrderDual.toDual j : OrderDual ℕ) : WithBot (OrderDual ℕ)) :=
  (hF.value_le_toDual_iff x j).symm

/-- The degree attached to the filtration evaluates to its value function. -/
theorem degree_eq_value (hF : IsSeparatedFiltration F) (x : R) :
    hF.degree x = hF.value x :=
  hF.degree_apply x

/-- An element has value `⊥` exactly when it is zero. -/
theorem value_eq_bot_iff_eq_zero (hF : IsSeparatedFiltration F) (x : R) :
    hF.value x = ⊥ ↔ x = 0 :=
  hF.value_eq_bot_iff x

/-- The degree attached to a separated filtration is separated. -/
theorem degree_isSeparated' (hF : IsSeparatedFiltration F) :
    (hF.degree).IsSeparated :=
  hF.degree_isSeparated

/-- At dual index `j`, the weak filtration of the degree is `F j` and its strict filtration is
`F (j+1)`. -/
theorem mem_degree_filtration_iff (hF : IsSeparatedFiltration F) (j : ℕ) (x : R) :
    (x ∈ (hF.degree).filtrationLE (OrderDual.toDual j) ↔ x ∈ F j) ∧
      ∀ y : (hF.degree).filtrationLE (OrderDual.toDual j),
        (y ∈ (hF.degree).lowerFiltration (OrderDual.toDual j) ↔ (y : R) ∈ F (j + 1)) :=
  ⟨hF.mem_degree_filtrationLE_iff j x, fun y ↦ hF.mem_degree_lowerFiltration_iff j y⟩

end Tests
