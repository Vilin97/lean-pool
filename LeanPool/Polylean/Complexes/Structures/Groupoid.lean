/-
Copyright (c) 2026 Siddhartha Gadgil, Anand Rao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Siddhartha Gadgil, Anand Rao
-/

import LeanPool.Polylean.Complexes.Structures.Category

/-!
# LeanPool.Polylean.Complexes.Structures.Groupoid

Imported Lean Pool material for `LeanPool.Polylean.Complexes.Structures.Groupoid`.
-/

namespace LeanPool.Polylean

/-- A `Groupoid` is defined as a `Category` in which every morphism has an inverse satisfying certain conditions. -/
class Groupoid (S : Sort _) extends Category S where
  /-- The inverse of a morphism. -/
  inv : {X Y : S} → (X ⟶ Y) → (Y ⟶ X)
  inv_comp_id : {X Y : S} → (g : X ⟶ Y) → (inv g) ≫ g = 𝟙 Y
  comp_inv_id : {X Y : S} → (g : X ⟶ Y) → g ≫ (inv g) = 𝟙 X

namespace Groupoid

open Category

attribute [simp] inv_comp_id
attribute [simp] comp_inv_id

variable {S : Sort _} [G : Groupoid S] {X Y Z : S} (g g' : X ⟶ Y) (h h' : Y ⟶ Z)

/-- Groupoid inverse notation. -/
postfix:max " ⁻¹ " => Groupoid.inv -- type as `\inv`

@[simp] theorem left_inv_cancel : g⁻¹ ≫ (g ≫ h) = h := by
  rw [← comp_assoc]; simp

@[simp] theorem id_inv : (𝟙 X)⁻¹ = 𝟙 X := by
  have := left_inv_cancel (𝟙 X) (𝟙 X)
  rw [comp_id, comp_id] at this; assumption

@[simp] theorem inv_inv : (g⁻¹)⁻¹ = g := by
  have := left_inv_cancel (g⁻¹) g
  rw [inv_comp_id, comp_id] at this; assumption

@[simp] theorem left_cancel_inv (h : X ⟶ Z) : g ≫ (g⁻¹ ≫ h) = h := by
  have := left_inv_cancel g⁻¹ h
  rw [inv_inv] at this; assumption

@[simp] theorem inv_comp : (g ≫ h)⁻¹ = h⁻¹ ≫ g⁻¹ := by
  have := left_cancel_inv (g ≫ h)⁻¹ (h⁻¹ ≫ g⁻¹)
  simp at this; assumption

@[simp] theorem left_cancel : g ≫ h = g ≫ h' ↔ h = h' :=
  ⟨fun hyp => by have := congrArg (g⁻¹ ≫ ·) hyp; simp at this; exact this,
    congrArg _⟩

@[simp] theorem right_cancel : g ≫ h = g' ≫ h ↔ g = g' :=
  ⟨fun hyp => by have := congrArg (· ≫ h⁻¹) hyp; simp at this; exact this,
    congrArg (· ≫ h)⟩

@[simp] theorem left_cancel_id : (g = g ≫ e) ↔ 𝟙 Y = e := by
  have := left_cancel g (𝟙 _) e; simp at this; exact this

@[simp] theorem left_cancel_id' : (g ≫ e = g) ↔ e = 𝟙 Y := by
  have := left_cancel g e (𝟙 Y); simp at this; exact this

@[simp] theorem right_cancel_id : (g = e ≫ g) ↔ 𝟙 X = e := by
  have := right_cancel (𝟙 X) e g; simp at this; exact this

@[simp] theorem right_cancel_id' : (e ≫ g = g) ↔ e = 𝟙 X := by
  have := right_cancel e (𝟙 X) g; simp at this; exact this

end Groupoid


namespace Groupoid

/-- A `Functor` is a morphism of `Groupoid`s. -/
structure Functor {S S' : Sort _} (G : Groupoid S) (G' : Groupoid S')
    extends Category.Functor G.toCategory G'.toCategory

namespace Functor

variable {R S T : Sort _} [F : Groupoid R] [G : Groupoid S] [H : Groupoid T]
variable (Ψ : Groupoid.Functor F G) (Φ : Groupoid.Functor G H)

theorem map_id' {X : S} : Φ.map (𝟙 X) = 𝟙 (Φ.obj X) := by
  have := Φ.map_comp (𝟙 X) (𝟙 X)
  rw [Category.comp_id, right_cancel_id] at this
  exact this.symm

@[simp] theorem map_inv {X Y : S} (g : X ⟶ Y) : Φ.map g⁻¹ = (Φ.map g)⁻¹ := by
  apply (Groupoid.left_cancel (Φ.map g) _ _).mp
  rw [← Φ.map_comp]
  simp

end Functor

end Groupoid
end LeanPool.Polylean
