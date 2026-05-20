/-
Copyright (c) 2026 Siddhartha Gadgil, Anand Rao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Siddhartha Gadgil, Anand Rao
-/

import LeanPool.Polylean.Complexes.Structures.Quiver

namespace LeanPool.Polylean

/-- The definition of a `CategoryStruct`, a barebones structure for a category containing none of the axioms (following `mathlib`). -/
class CategoryStruct (Obj : Sort _) extends Quiver Obj where
  /-- The identity morphism at an object. -/
  id : (X : Obj) → (X ⟶ X)
  /-- Composition of composable morphisms. -/
  comp : {X Y Z : Obj} → (X ⟶ Y) → (Y ⟶ Z) → (X ⟶ Z)

attribute [reducible] CategoryStruct.id
attribute [reducible] CategoryStruct.comp

/-- Identity morphism notation. -/
notation "𝟙" => CategoryStruct.id -- type as `\b1`
/-- Morphism composition notation. -/
infixr:80 " ≫ " => CategoryStruct.comp -- type as `\gg`
/-- Reverse-order morphism composition notation. -/
infixl:80 " ⊚ " => λ f g => CategoryStruct.comp g f

/-- The definition of a Category. -/
class Category (Obj : Sort _) extends CategoryStruct Obj where
  id_comp : {X Y : Obj} → (f : X ⟶ Y) → 𝟙 X ≫ f = f
  comp_id : {X Y : Obj} → (f : X ⟶ Y) → f ≫ 𝟙 Y = f
  comp_assoc : {W X Y Z : Obj} → (f : W ⟶ X) → (g : X ⟶ Y) → (h : Y ⟶ Z) →
    (f ≫ g) ≫ h = f ≫ (g ≫ h)

attribute [simp] Category.id_comp
attribute [simp] Category.comp_id
attribute [simp] Category.comp_assoc

namespace Category

/-- A functor is a morphism of categories. -/
structure Functor {C D : Sort _} (𝓒 : Category C) (𝓓 : Category D)
    extends Quiver.PreFunctor 𝓒.toQuiver 𝓓.toQuiver where
  map_id : (X : C) → map (𝟙 X) = 𝟙 (obj X)
  map_comp : {X Y Z : C} → (f : X ⟶ Y) → (g : Y ⟶ Z) →
      map (f ≫ g) = map f ≫ map g

namespace Functor

/-- Functor notation between categories. -/
infixr:26 " ⥤ " => Functor -- type as `\func`

attribute [simp] map_id
attribute [simp] map_comp

/-- The identity functor. -/
@[simp] protected def id (C : Sort _) [𝓒 : Category C] : 𝓒 ⥤ 𝓒 :=
-- TODO Use `..` notation : { .. , mapId := λ _ => rfl, mapComp := λ _ _ => rfl }
 { obj := id, map := id, map_id := λ _ => rfl, map_comp := λ _ _ => rfl }

/-- Composition of functors. -/
def comp {C D E : Sort _} {𝓒 : Category C} {𝓓 : Category D} {𝓔 : Category E}
    (F : 𝓒 ⥤ 𝓓) (G : 𝓓 ⥤ 𝓔) : 𝓒 ⥤ 𝓔 :=
-- TODO Use `..` notation
  { obj := G.obj ∘ F.obj, map := G.map ∘ F.map, map_id := by intro; simp, map_comp := by intros; simp }

/-- Functor composition notation. -/
infix:80 " ⋙ " => comp


/-- The object map of a composed functor is the composite object map. -/
@[simp] theorem comp_obj : (Φ.obj ∘ Ψ.obj) = (Ψ ⋙ Φ).obj := rfl

/-- Pointwise form of `Category.Functor.comp_obj`. -/
@[simp] theorem comp_obj' : ∀ x, (Φ.obj (Ψ.obj x)) = (Ψ ⋙ Φ).obj x := λ _ => rfl

end Functor

end Category


namespace Path

variable {C : Sort _} [𝓒 : Category C]

/-- Compose the arrows appearing in a category path. -/
def compose {X Y : C} : @Path C 𝓒.toQuiver X Y → (X ⟶ Y)
  | .nil => 𝟙 _
  | .cons e p => e ≫ p.compose

@[simp] theorem compose_nil {X : C} : (Path.nil' X).compose = 𝟙 X := rfl

/-- Composing an appended path equals composing the two pieces. -/
theorem compose_append {X Y Z : C} : {p : Path X Y} → {q : Path Y Z} → (append p q).compose = p.compose ≫ q.compose
  | .nil, _ => by simp
  | .cons _ _, _ => by
    dsimp [append, compose]
    rw [compose_append, Category.comp_assoc]

end Path

/-- Paths in a quiver form a category under concatenation. -/
instance (priority := low) Quiver.PathCategory {V : Sort _} [Quiver V] : Category V where
  hom := Path
  id := Path.nil'
  comp := Path.append

  id_comp := Path.nil_append
  comp_id := Path.append_nil
  comp_assoc := Path.append_assoc

namespace Quiver

/-- Embedding of a `Quiver` into its category of paths. -/
def toPathCategory {V : Sort _} [Q : Quiver V] : Quiver.PreFunctor Q Q.PathCategory.toQuiver where
  obj := id
  map := Quiver.toPath

end Quiver
end LeanPool.Polylean
