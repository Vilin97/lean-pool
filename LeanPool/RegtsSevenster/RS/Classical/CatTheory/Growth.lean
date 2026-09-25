/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.CatTheory.LengthBound

/-!
# Moderate growth of tensor powers

The two ways of asking that the tensor powers of every object grow
at most exponentially: by the dimension of their endomorphism
algebras (`ModerateEndGrowth`, here), and by their composition
length (`ModerateLengthGrowth`, defined in `RS/Definitions.lean`).
In a semisimple category with finite-dimensional Hom-spaces the
first implies the second, because length is bounded by the
endomorphism dimension.

Length is the measure Deligne's theorem states its growth
hypothesis in; the endomorphism dimension is the measure the
envelope's rank bound supplies directly.
-/

@[expose] public section

namespace RS

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe v u

variable (A : Type u)

/-- Every object has moderate tensor-power growth, measured by
endomorphism dimensions. -/
def ModerateEndGrowth [Category.{v} A] [MonoidalCategory A]
    [Preadditive A] [Linear ℂ A] : Prop :=
  ∀ Y : A, ∃ C c : ℕ, ∀ N : ℕ,
    Module.finrank ℂ (tensorPow A Y N ⟶ tensorPow A Y N) ≤
      C * c ^ N

-- The preadditive and abelian structures are supplied
-- independently, as they are for the envelope; `lengthLE_finrank_end`
-- reconciles them.
/-- **Endomorphism growth bounds length growth** in a semisimple
category with finite-dimensional Hom-spaces: the length of an object
is at most the dimension of its endomorphism algebra, so an
exponential bound on the latter is one on the former. -/
theorem moderateLengthGrowth_of_endGrowth [Category.{v} A] [MonoidalCategory A]
    [Preadditive A]
    [Linear ℂ A] [HasFiniteBiproducts A] (hab : Abelian A)
    (hss : IsSemisimple A)
    (hfd : HasFinDimHom A) (hgrow : ModerateEndGrowth A) :
    ModerateLengthGrowth A := by
  intro Y
  obtain ⟨C, c, hC⟩ := hgrow Y
  exact ⟨C, c, fun N =>
    (lengthLE_finrank_end hab hss hfd (tensorPow A Y N)).mono (hC N)⟩

end RS
