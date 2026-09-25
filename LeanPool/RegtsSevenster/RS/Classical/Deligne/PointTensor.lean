/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.UnitSimple

/-!
# Points of objects tensor without vanishing

In the setting of Deligne's theorem the tensor unit is simple, so
a nonzero morphism out of it is a monomorphism; whiskering is
exact, so the tensor of two nonzero points is again a
monomorphism, and in particular nonzero.  This is the input that
makes a tensor product of nonzero algebras nonzero.
-/

namespace RS

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe v u

variable {A : Type u}

/-- **A nonzero point is a monomorphism**: the unit is simple. -/
theorem mono_of_point_ne_zero
    [Category.{v} A] [Abelian A] [Linear ℂ A] [MonoidalCategory A]
    [MonoidalPreadditive A] [MonoidalLinear ℂ A] [RigidCategory A]
    (hu : HasScalarUnit A) {X : A}
    {u : 𝟙_ A ⟶ X} (h : u ≠ 0) : Mono u := by
  have := simple_unit_of_hasScalarUnit hu
  exact mono_of_nonzero_from_simple h

/-- **The tensor of two nonzero points is a monomorphism.** -/
theorem mono_tensorHom_point
    [Category.{v} A] [Abelian A] [Linear ℂ A] [MonoidalCategory A]
    [MonoidalPreadditive A] [MonoidalLinear ℂ A] [RigidCategory A]
    (hu : HasScalarUnit A) {X Y : A}
    {u : 𝟙_ A ⟶ X} {v : 𝟙_ A ⟶ Y} (hu0 : u ≠ 0) (hv0 : v ≠ 0) :
    Mono (u ⊗ₘ v) := by
  have : Mono u := mono_of_point_ne_zero hu hu0
  have : Mono v := mono_of_point_ne_zero hu hv0
  have hR : (tensorRight (𝟙_ A)).PreservesMonomorphisms :=
    Functor.preservesMonomorphisms_of_adjunction
      (tensorRightAdjunction (ᘁ(𝟙_ A)) (𝟙_ A))
  have hL : (tensorLeft X).PreservesMonomorphisms :=
    Functor.preservesMonomorphisms_of_adjunction
      (tensorLeftAdjunction X (Xᘁ))
  have hmu : Mono (u ▷ 𝟙_ A) := hR.preserves (f := u)
  have hmv : Mono (X ◁ v) := hL.preserves (f := v)
  rw [MonoidalCategory.tensorHom_def]
  exact mono_comp _ _

/-- **The tensor of two nonzero points is nonzero.** -/
theorem tensorHom_point_ne_zero
    [Category.{v} A] [Abelian A] [Linear ℂ A] [MonoidalCategory A]
    [MonoidalPreadditive A] [MonoidalLinear ℂ A] [RigidCategory A]
    (hu : HasScalarUnit A) {X Y : A}
    {u : 𝟙_ A ⟶ X} {v : 𝟙_ A ⟶ Y} (hu0 : u ≠ 0) (hv0 : v ≠ 0) :
    (u ⊗ₘ v) ≠ 0 := by
  have := mono_tensorHom_point hu hu0 hv0
  intro h0
  have hid : 𝟙 (𝟙_ A ⊗ 𝟙_ A) = 0 := by
    refine (cancel_mono (u ⊗ₘ v)).mp ?_
    rw [Category.id_comp, h0, Limits.zero_comp]
  refine id_unit_ne_zero hu ?_
  have := congrArg
    (fun t => (λ_ (𝟙_ A)).inv ≫ t ≫ (λ_ (𝟙_ A)).hom) hid
  simpa using this

end RS
