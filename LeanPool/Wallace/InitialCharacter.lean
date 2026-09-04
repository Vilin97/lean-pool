/-
Copyright (c) 2026 Juliane Trianon Fraga and Vinicius de Oliveira Rodrigues. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juliane Trianon Fraga, Vinicius de Oliveira Rodrigues
-/

import LeanPool.Wallace.UniformKronecker

/-!
# A character with a prescribed half-turn value

The local fusion starts from a character taking a chosen nonzero element to the half-turn of the
circle.  Torsion-freeness makes this one-point prescription compatible with every integer
relation, and divisibility of the circle extends it to the ambient group.
-/

namespace Wallace

noncomputable section

universe u

/-- Every nonzero element of a torsion-free Abelian group can be sent exactly to `1/2` in the
unit additive circle. -/
theorem exists_character_apply_eq_half
    {G : Type u} [AddCommGroup G] [IsAddTorsionFree G]
    {x : G} (hx : x ≠ 0) :
    ∃ χ : G →+ UnitAddCircle, χ x = ((1 / 2 : ℝ) : UnitAddCircle) := by
  let z : Fin 1 → G := fun _ ↦ x
  let t : Fin 1 → UnitAddCircle := fun _ ↦ ((1 / 2 : ℝ) : UnitAddCircle)
  have hrel : RespectsRelations z t := by
    rw [respectsRelations_iff]
    intro a ha
    have ha0 : a 0 = 0 := by
      have : a 0 • x = 0 := by simpa [z] using ha
      exact (IsAddTorsionFree.zsmul_eq_zero_iff_left hx).mp this
    simp [t, ha0]
  obtain ⟨χ, hχ⟩ := exists_character_of_respectsRelations z t hrel
  exact ⟨χ, by simpa [z, t] using hχ 0⟩

end

end Wallace
