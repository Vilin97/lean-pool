/-
Copyright (c) 2026 Ivan Kobe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ivan Kobe
-/

import Mathlib.CategoryTheory.Category.Basic

namespace CategoryTheory

universe u v

variable {C : Type u} [Category.{v} C]

/-- A commuting square in a category. -/
structure square (A B X Y : C) where
  left : A ⟶ B
  right : X ⟶ Y
  top : A ⟶ X
  bot : B ⟶ Y
  comm : left ≫ bot = top ≫ right := by aesop_cat

/-- A commuting square with specified vertical maps. -/
structure square_completion {A B X Y : C} (left : A ⟶ B) (right : X ⟶ Y) where
  top : A ⟶ X
  bot : B ⟶ Y
  comm : left ≫ bot = top ≫ right := by aesop_cat

infixl:75 " □ " => square_completion

/-- Forget the specified vertical maps of a completed square. -/
@[reducible]
def square_of_square_completion
    {A B X Y : C} {left : A ⟶ B} {right : X ⟶ Y} (completed : left □ right) :
    square A B X Y where
  left := left
  right := right
  top := completed.top
  bot := completed.bot
  comm := completed.comm

/-- A diagonal filler of a completed square. -/
structure diagonal_filler
    {A B X Y : C} {left : A ⟶ B} {right : X ⟶ Y} (completed : left □ right) where
  map : B ⟶ X
  comm_top : left ≫ map = completed.top := by aesop_cat
  comm_bot : map ≫ right = completed.bot := by aesop_cat

/-- A proof that two morphisms are orthogonal. -/
structure orthogonal {A B X Y : C} (left : A ⟶ B) (right : X ⟶ Y) where
  diagonal : (completed : left □ right) → diagonal_filler completed
  diagonal_unique :
    (completed : left □ right) →
      (filler filler' : diagonal_filler completed) → filler.map = filler'.map

/-- Hom-orthogonality, represented by the existence of an orthogonality structure. -/
def hom_orthogonal {A B X Y : C} (left : A ⟶ B) (right : X ⟶ Y) : Prop :=
  Nonempty (orthogonal left right)

/-- Orthogonality implies hom-orthogonality. -/
lemma orthogonal_implies_hom_orthogonal
    {A B X Y : C} (left : A ⟶ B) (right : X ⟶ Y) :
    orthogonal left right → hom_orthogonal left right := by
  exact fun proof => ⟨proof⟩

/-- Hom-orthogonality gives a chosen orthogonality structure. -/
noncomputable
def hom_orthogonal_implies_orthogonal
    {A B X Y : C} {left : A ⟶ B} {right : X ⟶ Y}
    (proof : hom_orthogonal left right) : orthogonal left right :=
  Classical.choice proof

end CategoryTheory
