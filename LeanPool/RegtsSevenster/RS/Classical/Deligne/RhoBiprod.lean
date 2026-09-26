/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.Deligne.RhoTwist

/-!
# The realization of a biproduct

Morphisms into a finite biproduct are families of morphisms into
the summands, ℂ-linearly.  With the distribution of a tensor over
a biproduct this computes `ρ` on a mixed sum.
-/

@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory Limits

universe v u

variable {D : Type u}

/-- **Morphisms into a biproduct are families of morphisms**, as
ℂ-modules. -/
noncomputable def homBiproductEquiv
    [Category.{v} D] [Preadditive D] [HasFiniteBiproducts D]
    [CategoryTheory.Linear ℂ D]
    {J : Type} [Finite J] (P : D)
    (f : J → D) : (P ⟶ ⨁ f) ≃ₗ[ℂ] ∀ j, (P ⟶ f j) where
  toFun g := fun j => g ≫ biproduct.π f j
  map_add' g h := by
    funext j
    exact Preadditive.add_comp _ _ _ g h _
  map_smul' r g := by
    funext j
    exact Linear.smul_comp _ _ _ r g _
  invFun h := biproduct.lift h
  left_inv g := by
    apply biproduct.hom_ext
    intro j
    rw [biproduct.lift_π]
  right_inv h := by
    funext j
    change biproduct.lift h ≫ biproduct.π f j = h j
    rw [biproduct.lift_π]

end RS
