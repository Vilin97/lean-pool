/-
Copyright (c) 2026 Dominique Lawson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dominique Lawson, Henning Basold, Peter Bruin
-/
import Mathlib.CategoryTheory.EqToHom
import Mathlib.CategoryTheory.Category.Cat

/-
  This file contains auxiliary equalities of objects morphisms in a category.
  These are used in the proof of the Van Kampen Theorem in directed_van_kampen.lean
-/

open CategoryTheory

universe u
variable {C C' : CategoryTheory.Cat.{u, u}}

/-- If we have two compositions a --f₀--> b₀ --g₀--> c and a --f₁--> b₁ --g₁--> c,
where b₀ = b₀, f₀ = f₁ and g₀ = g₁, then f₀ ≫ g₀ = f₁ ≫ g₁
-/
lemma eq_of_morphism {a b₀ b₁ c : C} {f₀ : a ⟶ b₀} {f₁ : a ⟶ b₁} {g₀ : b₀ ⟶ c} {g₁ : b₁ ⟶ c}
  (hb : b₁ = b₀) (hf : f₀ = f₁ ≫ (eqToHom hb)) (hg : g₀ = (eqToHom hb.symm) ≫ g₁) :
    f₀ ≫ g₀ = f₁ ≫ g₁ := by
  subst_vars
  rw [eqToHom_refl, Category.comp_id, Category.id_comp]

/-- If two functors are equal, they map objects to the same image
-/
lemma obj_eq_obj_of_eq {F₁ F₂ : C ⥤ C'} (h : F₁ = F₂) (x : C) : F₁.obj x = F₂.obj x :=
  congrFun (congrArg Prefunctor.obj (congrArg Functor.toPrefunctor h)) x

/-- If two functors are equal, they map morphisms to the same image
-/
lemma map_eq_map_of_eq {F₁ F₂ : C ⥤ C'} (h : F₁ = F₂) {x y : C} (f : x ⟶ y) :
    F₁.map f = (eqToHom (obj_eq_obj_of_eq h x)) ≫ F₂.map f ≫ (eqToHom (obj_eq_obj_of_eq h y).symm)
        := by
  subst_vars
  simp
