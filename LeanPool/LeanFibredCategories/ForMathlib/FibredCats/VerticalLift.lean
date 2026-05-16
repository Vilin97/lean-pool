/-
Copyright (c) 2026 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Sigma.Basic
import LeanPool.LeanFibredCategories.ForMathlib.Data.Fiber
import LeanPool.LeanFibredCategories.ForMathlib.FibredCats.CartesianLift

/-!
# Vertical Lifts

We call a lift `v : x ⟶[𝟙 c] y` of the identity morphism a vertical
lift/morphism.
-/


namespace CategoryTheory

open Category Functor Fiber BasedLift

variable {C E : Type*} [Category C] [Category E]

/-- The type of vertical morphisms — pairs `(c, x)` of a base object with an
object in its fiber, considered up to all isomorphisms covering `𝟙 c`. -/
abbrev Vert (P : E ⥤ C) := Σ c, P ⁻¹ c

variable {P : E ⥤ C}

instance instCategoryVert : Category (Vert P) := inferInstance

/-- A based-lift of the identity generates a morphism in `Vert P`. -/
def vertHomOfBasedLift {X Y : Vert P} (h : X.1 = Y.1)
    (f : X.2 ⟶[𝟙 X.1] Y.2.cast h.symm) : (X ⟶ Y) := by
  obtain ⟨c, x⟩ := X
  obtain ⟨c', y⟩ := Y
  have H : c = c' := h
  subst H
  simp only [Fiber.cast] at f
  exact ⟨f.1, by aesop⟩

@[simp]
lemma base_eq_of_vert_hom {X Y : Vert P} (f : X ⟶ Y) : X.1 = Y.1 := by
  cases f
  rfl

/-- The underlying morphism on fibers of a morphism in `Vert P`. -/
@[simp]
def basedLiftOfVertHomAux {X Y : Vert P} (f : X ⟶ Y) : X.2.1 ⟶ Y.2.1 := by
  obtain ⟨f'⟩ := f
  exact f'.1

@[simp]
lemma basedLiftOfVertHomAux_over {X Y : Vert P} {f : X ⟶ Y} :
    have : P.obj Y.2.1 = X.1 := (Fiber.over _).trans (base_eq_of_vert_hom f).symm
    P.map (basedLiftOfVertHomAux f) ≫ eqToHom this = eqToHom (X.2.over) ≫ 𝟙 X.1 := by
  cases f; simp

/-- The based-lift associated to a vertical morphism. -/
def basedLiftOfVertHom {X Y : Vert P} (f : X ⟶ Y) :
    have : X.1 = Y.1 := base_eq_of_vert_hom f
    X.2 ⟶[𝟙 X.1] Y.2.cast this.symm := ⟨basedLiftOfVertHomAux f, by cases f; simp⟩

/-- A morphism in a fiber, regarded as a based-lift of the identity. -/
@[simp]
def basedLiftOfFiberHom {c : C} {x y : P ⁻¹ c} (f : x ⟶ y) : x ⟶[𝟙 c] y :=
  ⟨f.1, by simp⟩

/-- Coercing a based-lift `x ⟶[𝟙 c] y` of the identity morphism `𝟙 c`
to a morphism `x ⟶ y` in the fiber `P ⁻¹ c`. -/
@[simps]
instance instCoeFiberHom {c : C} {x y : P ⁻¹ c} : Coe (x ⟶[𝟙 c] y) (x ⟶ y) where
  coe := fun f ↦ ⟨f.hom, by simp⟩

/-- The bijection between the hom-type of the fiber `P ⁻¹ c` and the based-lifts of
the identity morphism of `c`. -/
@[simps!]
def equivFiberHomBasedLift {c : C} {x y : P ⁻¹ c} : (x ⟶ y) ≃ (x ⟶[𝟙 c] y) where
  toFun := fun g ↦ basedLiftOfFiberHom g
  invFun := fun g ↦ g
  left_inv := by intro g; simp [basedLiftOfFiberHom]
  right_inv := by intro g; rfl

/-- The bijection between morphisms in `Vert P` between fibers of the same base
object and based-lifts of the identity morphism. -/
@[simps!]
def equivVertHomBasedLift {c : C} {x y : P ⁻¹ c} :
    ((⟨c, x⟩ : Vert P) ⟶ ⟨c, y⟩) ≃ (x ⟶[𝟙 c] y) where
  toFun := fun g ↦ basedLiftOfVertHom g
  invFun := fun g ↦ vertHomOfBasedLift rfl g
  left_inv := by intro g; cases g; aesop
  right_inv := by intro g; rfl

end CategoryTheory
