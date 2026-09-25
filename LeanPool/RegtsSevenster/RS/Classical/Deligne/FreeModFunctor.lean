/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.Deligne.FibreFunctor
public import LeanPool.RegtsSevenster.RS.Classical.Deligne.GammaModuleFunctor

/-!
# The free-module functor, and the factorisation of `ω`

Base change to an algebra is a functor to the module objects over
that algebra, and Deligne's `ω` of 2.11 is that functor followed by
realization.  Recording the factorisation lets the two halves be
treated separately: the free-module functor carries the monoidal
comparison of the ambient category, and realization carries the
comparison of (2.11.1).
-/

@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory Limits

universe v u

section Free

variable {D : Type u}

/-- Base change of a morphism is the identity on the identity. -/
theorem freeModMap_id [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    (V : D) :
    freeModMap A (𝟙 V) = 𝟙 (freeMod A V) := by
  apply Mod.Hom.ext
  exact MonoidalCategory.whiskerLeft_id A V

/-- Base change of a morphism respects composition. -/
theorem freeModMap_comp [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    {V W X : D} (f : V ⟶ W) (g : W ⟶ X) :
    freeModMap A (f ≫ g) = freeModMap A f ≫ freeModMap A g := by
  apply Mod.Hom.ext
  exact MonoidalCategory.whiskerLeft_comp A f g

/-- **Base change to an algebra, as a functor.** -/
noncomputable def freeModFunctor
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A] : D ⥤ Mod D A where
  obj V := freeMod A V
  map f := freeModMap A f
  map_id := freeModMap_id A
  map_comp := freeModMap_comp A

@[simp] theorem freeModFunctor_obj
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    (V : D) :
    (freeModFunctor A).obj V = freeMod A V := rfl

@[simp] theorem freeModFunctor_map
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    {V W : D} (f : V ⟶ W) :
    (freeModFunctor A).map f = freeModMap A f := rfl

end Free

end RS
