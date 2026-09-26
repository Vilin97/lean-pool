/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.Deligne.Doubling
public import LeanPool.RegtsSevenster.RS.Definitions

/-!
# Scalars on the unit of the doubling

The unit of the doubling is the unit in even degree and the zero
object in odd degree, so its endomorphisms are those of the unit
downstairs: the scalar-unit hypothesis passes to the doubling.
-/

@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory Limits

universe v u

variable {A : Type u}

/-- **The scalar-unit hypothesis passes to the doubling.** -/
theorem hasScalarUnit_doubled
    [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [CategoryTheory.Linear ℂ A] [MonoidalPreadditive A]
    [HasBinaryBiproducts A] [HasZeroObject A]
    (hu : HasScalarUnit A) :
    HasScalarUnit (Doubled A) := by
  constructor
  · intro c c' h
    have he := congrArg Doubled.evenHom h
    rw [Doubled.evenHom_smul, Doubled.evenHom_smul,
      Doubled.evenHom_id] at he
    exact hu.1 he
  · intro f
    obtain ⟨c, hc⟩ := hu.2 (Doubled.evenHom f)
    refine ⟨c, ?_⟩
    apply Doubled.hom_ext
    · rw [Doubled.evenHom_smul, Doubled.evenHom_id]
      exact hc
    · exact (isZero_zero A).eq_of_src _ _

end RS
