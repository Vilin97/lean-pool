/-
Copyright (c) 2026 Dominique Lawson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dominique Lawson, Henning Basold, Peter Bruin
-/
import LeanPool.DirectedTopologyLean4.Constructions
import Mathlib.CategoryTheory.ConcreteCategory.Basic
import Mathlib.CategoryTheory.Elementwise

/-!
# LeanPool.DirectedTopologyLean4.DTop
-/

/-
  This file contains the definition of `dTopCat`, the category of directed spaces.
  The structure of this file is based on the approach for the undirected version in Mathlib:
  https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Topology/Category/TopCat/Basic.lean
-/

open DirectedMap
open CategoryTheory

universe u

/-- The category of directed topological spaces. -/
structure dTopCat where
  /-- The underlying type of a directed topological space. -/
  carrier : Type u
  [str : DirectedSpace carrier]

namespace dTopCat

attribute [instance] dTopCat.str

instance : CoeSort dTopCat (Type u) := ⟨dTopCat.carrier⟩

attribute [coe] dTopCat.carrier

/-- Construct a bundled `dTopCat` from the underlying type and the typeclass. -/
def of (X : Type u) [DirectedSpace X] : dTopCat := ⟨X⟩

@[simp]
lemma coe_of (X : Type u) [DirectedSpace X] : (of X : Type u) = X := rfl

/-- The type of morphisms in `dTopCat`. -/
@[ext]
structure Hom (X Y : dTopCat.{u}) where
  /-- The underlying `DirectedMap`. -/
  hom' : D(X,Y)

instance : Category dTopCat where
  Hom X Y := Hom X Y
  id X := ⟨DirectedMap.id X⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

instance concreteCategory : ConcreteCategory.{u} dTopCat (fun X Y => D(X,Y)) where
  hom := Hom.hom'
  ofHom f := ⟨f⟩

namespace Hom

/-- Turn a morphism in `dTopCat` back into a `DirectedMap`. -/
abbrev hom {X Y : dTopCat.{u}} (f : Hom X Y) : D(X,Y) :=
  ConcreteCategory.hom (C := dTopCat) f

end Hom

/-- Typecheck a `DirectedMap` as a morphism in `dTopCat`. -/
abbrev ofHom {X Y : Type u} [DirectedSpace X] [DirectedSpace Y] (f : D(X,Y)) : of X ⟶ of Y :=
  ConcreteCategory.ofHom (C := dTopCat) f

@[simp]
lemma hom_id {X : dTopCat.{u}} : (𝟙 X : X ⟶ X).hom = DirectedMap.id X := rfl

@[simp]
lemma id_app (X : dTopCat.{u}) (x : ↑X) : (𝟙 X : X ⟶ X) x = x := rfl

@[simp]
lemma hom_comp {X Y Z : dTopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

@[simp]
lemma comp_app {X Y Z : dTopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g : X → Z) x = g (f x) := rfl

@[ext]
lemma hom_ext {X Y : dTopCat} {f g : X ⟶ Y} (hf : f.hom = g.hom) : f = g := Hom.ext hf

@[ext]
lemma ext {X Y : dTopCat} {f g : X ⟶ Y} (w : ∀ x : X, f x = g x) : f = g :=
  ConcreteCategory.hom_ext _ _ w

@[simp]
lemma hom_ofHom {X Y : Type u} [DirectedSpace X] [DirectedSpace Y] (f : D(X,Y)) :
    (ofHom f).hom = f := rfl

@[simp]
lemma ofHom_hom {X Y : dTopCat} (f : X ⟶ Y) : ofHom (Hom.hom f) = f := rfl

@[simp]
lemma ofHom_id {X : Type u} [DirectedSpace X] : ofHom (DirectedMap.id X) = 𝟙 (of X) := rfl

@[simp]
lemma ofHom_comp {X Y Z : Type u} [DirectedSpace X] [DirectedSpace Y] [DirectedSpace Z]
    (f : D(X,Y)) (g : D(Y,Z)) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g := rfl

instance subspaceCoe {X : dTopCat} : CoeTC (Set X) dTopCat := ⟨fun s => dTopCat.of s⟩

/-- The inclusion of a directed subspace into its ambient space. -/
def DirectedSubtypeHom {X : dTopCat} (Y : Set X) : (dTopCat.of Y) ⟶ X :=
  ofHom (DirectedSubtypeInclusion (fun s => s ∈ Y))

/-- The inclusion between two directed subspaces, given a subset relation. -/
def DirectedSubsetHom {X : dTopCat} {Y₀ Y₁ : Set X} (h : Y₀ ⊆ Y₁) : (dTopCat.of Y₀) ⟶ Y₁ :=
  ofHom (DirectedSubsetInclusion h)

end dTopCat
