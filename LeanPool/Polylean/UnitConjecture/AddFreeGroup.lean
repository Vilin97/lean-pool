/-
Copyright (c) 2026 Siddhartha Gadgil, Anand Rao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Siddhartha Gadgil, Anand Rao
-/

import Mathlib.Algebra.Group.Prod
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Algebra.Ring.Basic
import LeanPool.Polylean.UnitConjecture.EnumDecide

namespace LeanPool.Polylean

/-!

## Free groups

The definition of a free group on a basis, along with a few properties.

Free groups are defined constructively to allow automatic equality checking of
homomorphisms on finitely generated free groups.

## Overview
- `AddFreeGroup` - the main definition.
- `decideHomsEqual` - the crucial result that allows the
  automatic comparison of homomorphisms by checking their values on the basis.
- `ℤFree` - a proof that the additive group of integers is a free group on the one-element type.
- `prodFree` - a proof that the product of free groups is free.
-/

/-- Free (Additive) Groups, implemented as a typeclass.
    A free additive group with a basis `X` is an additive group `F` with an
    inclusion map `ι : X → F`,
    such that any map `f : X → A` from the basis to any Abelian group `A`
    extends *uniquely* to an *additive group homomorphism* `φ : F →+ A`. -/
class AddFreeGroup (F : Type _) [AddCommGroup F] (X : Type _) where
  /-- The inclusion map from the basis to the free group. -/
  ι : X → F
  /-- The homomorphism from the free group induced by a map from the basis. -/
  inducedHom : (A : Type) → [AddCommGroup A] → (X → A) → (F →+ A)
  /-- A proof that the induced homomorphism extends the map from the basis. -/
  induced_extends {A : Type} [AddCommGroup A] : ∀ f : X → A, (inducedHom A f) ∘ ι = f
  /-- A proof that any homomorphism extending a map from the basis must be unique. -/
  unique_extension {A : Type} [AddCommGroup A] (f g : F →+ A) : f ∘ ι = g ∘ ι → f = g


/-- The additive group of integers `ℤ` is the free group on a singleton basis. -/
instance ℤFree : AddFreeGroup ℤ Unit where
  ι := fun _ => 1
  inducedHom := fun A _ f => (zmultiplesHom A).toFun (f ())
  induced_extends := by
    intro A _ f
    funext u; cases u
    simp [one_zsmul]
  unique_extension := by
    intro A abg f g hyp
    let hyp' := congrFun hyp ()
    dsimp at hyp'
    rwa [← zmultiplesHom_symm_apply, ← zmultiplesHom_symm_apply, Equiv.apply_eq_iff_eq] at hyp'


open EnumDecide in
/-- Equality of homomorphisms from a free group on an exhaustively searchable basis is decidable. -/
def decideHomsEqual {F : Type _} [AddCommGroup F] {X : Type _} [DecideForall X]
    [fgp : AddFreeGroup F X]
    {A : Type _} [AddCommGroup A] [DecidableEq A] : DecidableEq (F →+ A) := fun f g =>
  if c : ∀ x : X, f (fgp.ι x) = g (fgp.ι x) then by
    apply Decidable.isTrue
    apply fgp.unique_extension
    funext x
    exact c x
  else by
    apply Decidable.isFalse
    intro contra
    let c' : ∀ (x : X), f (fgp.ι x) = g (fgp.ι x) := by
      intro; apply congrFun (congrArg _ contra)
    contradiction

namespace AddFreeGroup.Product

variable {A B : Type _} [AddCommGroup A] [AddCommGroup B]
variable {X_A X_B : Type _}
variable [FAb_A : AddFreeGroup A X_A] [FAb_B : AddFreeGroup B X_B]

/-- The inclusion map from the direct sum of the bases of two free groups into their product. -/
def ι : (X_A ⊕ X_B) → A × B
  | Sum.inl x_a => (FAb_A.ι x_a, 0)
  | Sum.inr x_b => (0, FAb_B.ι x_b)

/-- The group homomorphism from the product of two free groups induced by a map from the basis. -/
def inducedProdHom (G : Type _) [AddCommGroup G] (f : X_A ⊕ X_B → G) : A × B →+ G :=
    let f_A : X_A → G := f ∘ Sum.inl
    let f_B : X_B → G := f ∘ Sum.inr
    AddMonoidHom.coprod
      (FAb_A.inducedHom G f_A)
      (FAb_B.inducedHom G f_B)

/-- The product of free groups is free. -/
instance prodFree : AddFreeGroup (A × B) (X_A ⊕ X_B) :=
  {
    ι := ι
    inducedHom := inducedProdHom
    induced_extends := by
      intro _ _ f
      funext x
      cases x with
      | inl x =>
          unfold inducedProdHom ι
          dsimp
          rw [map_zero, add_zero]
          exact congrFun (FAb_A.induced_extends (f ∘ Sum.inl)) x
      | inr x =>
          unfold inducedProdHom ι
          dsimp
          rw [map_zero, zero_add]
          exact congrFun (FAb_B.induced_extends (f ∘ Sum.inr)) x
    unique_extension := by
      intro _ _ f g hyp
      ext ⟨a, b⟩
      rw [show (a, b) = (a, 0) + (0, b) by simp, map_add, map_add]
      have A_unique : f.comp (.inl A B) = g.comp (.inl A B) := by
        apply FAb_A.unique_extension; funext x_A; apply congrFun hyp (Sum.inl x_A)
      have B_unique : f.comp (.inr A B) = g.comp (.inr A B) := by
        apply FAb_B.unique_extension; funext x_B; apply congrFun hyp (Sum.inr x_B)
      change f.comp (.inl _ _) a + f.comp (.inr _ _) b =
           g.comp (.inl _ _) a + g.comp (.inr _ _) b
      rw [A_unique, B_unique]
  }

end AddFreeGroup.Product

end LeanPool.Polylean
