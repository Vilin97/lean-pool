/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Standalone.CombinatorialGames.ConwayRefinement

/-! # Conway Refinement Consequences -/

public noncomputable section

universe u

namespace ConwayRefinement.Standalone.Oz

/-- Membership unfolds to Conway's defining cut equation. -/
theorem isConwayOmnificInteger_iff (x : Surreal.{u}) :
    IsConwayOmnificInteger x ↔
      x = !{{x - 1} | {x + 1}}' (by
        simp only [Set.mem_singleton_iff]
        rintro _ rfl _ rfl
        simp [sub_eq_add_neg]) := (Iff.rfl)

/-- The proposition unfolds to the displayed four-factor refinement. -/
theorem conwayConjecture_iff : ConwayConjecture.{u} ↔
    ∀ a b c d : Surreal.{u},
      IsConwayOmnificInteger a → IsConwayOmnificInteger b →
      IsConwayOmnificInteger c → IsConwayOmnificInteger d → a * b = c * d →
      ∃ e f g h : Surreal.{u},
        IsConwayOmnificInteger e ∧ IsConwayOmnificInteger f ∧
        IsConwayOmnificInteger g ∧ IsConwayOmnificInteger h ∧
        a = e * f ∧ b = g * h ∧ c = e * g ∧ d = f * h :=
  (Iff.rfl)

end ConwayRefinement.Standalone.Oz
