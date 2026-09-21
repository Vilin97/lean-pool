/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Definitions

/-!
# Conditions on a ℂ-linear category

The ambient conditions a tensor category is asked to satisfy:
finite-dimensional Hom-spaces and semisimplicity in the form that
every object is a finite biproduct of simple objects.  The third,
scalar endomorphisms of the tensor unit (`HasScalarUnit`), is
defined in `RS/Definitions.lean`.
-/

namespace RS

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe v u

variable (A : Type u)

/-- Every Hom-space is finite dimensional over ℂ. -/
def HasFinDimHom [Category.{v} A]
    [Preadditive A] [Linear ℂ A] : Prop :=
  ∀ X Y : A, FiniteDimensional ℂ (X ⟶ Y)

/-- Every object is a finite biproduct of simple objects. -/
def IsSemisimple [Category.{v} A]
    [Preadditive A] [HasFiniteBiproducts A] : Prop :=
  ∀ X : A, ∃ (n : ℕ) (S : Fin n → A),
    (∀ i, Simple (S i)) ∧ Nonempty (X ≅ ⨁ S)

end RS
