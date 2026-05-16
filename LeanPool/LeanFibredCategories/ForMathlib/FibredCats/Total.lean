/-
Copyright (c) 2026 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Functor.Basic
import LeanPool.LeanFibredCategories.ForMathlib.FibredCats.Basic
import LeanPool.LeanFibredCategories.ForMathlib.FibredCats.CartesianLift

/-!
# Total Category

This file defines the total category `∫ P` of a functor `P : E ⥤ C` as the
type `Fiber.Total P.obj`, equipped with the morphisms that lift to `P`.
-/

namespace CategoryTheory
open Category Opposite Functor

variable {C E : Type*} [Category C] [Category E]

/-- The total category of a functor `P : E ⥤ C`. -/
abbrev TotalCat {C E : Type*} [Category C] [Category E] (P : E ⥤ C) := Fiber.Total P.obj

@[inherit_doc] prefix:75 " ∫ " => TotalCat

/-- A morphism in the total category consists of a morphism in the base and
a morphism on the fibers, related by the lift compatibility equation. -/
@[ext]
structure TotalCatHom {P : E ⥤ C} (X Y : ∫ P) where
  /-- The morphism in the base category. -/
  base : X.base ⟶ Y.base
  /-- The morphism in the domain of `P`. -/
  fiber : X.fiber.1 ⟶ Y.fiber.1
  /-- The lift compatibility equation. -/
  eq : (P.map fiber) ≫ eqToHom (Y.fiber.over) = eqToHom (X.fiber.over) ≫ base

namespace TotalCat

/-- The based-lift associated to a morphism of the total category. -/
def BasedLiftOf {P : E ⥤ C} {X Y : ∫ P} (g : TotalCatHom X Y) :
    X.fiber ⟶[g.base] Y.fiber where
  hom := g.fiber
  over := g.eq

@[simp]
lemma over_base {P : E ⥤ C} {X Y : ∫ P} (g : TotalCatHom X Y) :
    P.map g.fiber = eqToHom (X.fiber.over) ≫ g.base ≫ (eqToHom (Y.fiber.over).symm) := by
  simp [← Category.assoc _ _ _, ← g.eq]

instance instCatOfTotal (P : E ⥤ C) : Category (∫ P) where
  Hom X Y := TotalCatHom X Y
  id X := ⟨𝟙 X.base, 𝟙 X.fiber.1, by simp⟩
  comp := @fun _ _ _ f g => ⟨f.1 ≫ g.1, f.2 ≫ g.2, by
    rw [Functor.map_comp, assoc, over_base g, over_base f]
    slice_lhs 3 4 =>
      rw [eqToHom_trans, eqToHom_refl]
    simp
   ⟩
  id_comp := by intro _ _ _; dsimp; congr 1 <;> simp
  comp_id := by intro _ _ _; dsimp; congr 1 <;> simp
  assoc := by intro _ _ _ _ _ _ _; dsimp; congr 1 <;> simp

end TotalCat

end CategoryTheory
