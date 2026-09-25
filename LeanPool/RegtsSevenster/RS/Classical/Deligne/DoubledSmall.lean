/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.Deligne.Doubling

/-!
# The doubling is the square

The doubling of a category is its product with itself: an object
is a pair and a morphism is a pair.  Essential smallness follows.
-/

@[expose] public section

namespace RS

open CategoryTheory

universe v u

variable {A : Type u}

/-- The doubling, as the product category. -/
def doubledProdFunctor [Category.{v} A] : Doubled A ⥤ (A × A) where
  obj X := (X.even, X.odd)
  map f := (Doubled.evenHom f, Doubled.oddHom f)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The product category, as the doubling. -/
def prodDoubledFunctor [Category.{v} A] : (A × A) ⥤ Doubled A where
  obj X := ⟨X.1, X.2⟩
  map f := ⟨f.1, f.2⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- **The doubling is the square of the category.** -/
def doubledProdEquiv [Category.{v} A] : Doubled A ≌ (A × A) where
  functor := doubledProdFunctor
  inverse := prodDoubledFunctor
  unitIso := Iso.refl _
  counitIso := Iso.refl _
  functor_unitIso_comp _ := Category.comp_id _

end RS
