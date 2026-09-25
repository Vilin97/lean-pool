/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Definitions

/-!
# The scalar unit as a ring isomorphism

The scalar-unit hypothesis says that scaling the identity of the
tensor unit is a bijection from the complex numbers.  It is also a
ring homomorphism, so it is a ring isomorphism, which is the form
in which the ℂ-linear structure of the Ind-completion consumes it.
-/

@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory

universe v u

variable (A : Type u)

/-- Scaling the identity of the tensor unit, as a ring
homomorphism. -/
def scalarUnitRingHom
    [Category.{v} A] [Preadditive A] [CategoryTheory.Linear ℂ A]
    [MonoidalCategory A] : ℂ →+* End (𝟙_ A) where
  toFun c := c • 𝟙 (𝟙_ A)
  map_one' := one_smul _ _
  map_mul' a b := by
    change (a * b) • 𝟙 (𝟙_ A) = (b • 𝟙 (𝟙_ A)) ≫ (a • 𝟙 (𝟙_ A))
    rw [Linear.smul_comp, Linear.comp_smul, Category.comp_id,
      smul_smul, mul_comm]
  map_zero' := zero_smul _ _
  map_add' a b := add_smul _ _ _

variable {A}

/-- **The scalar unit as a ring isomorphism.** -/
noncomputable def scalarUnitEquiv
    [Category.{v} A] [Preadditive A] [CategoryTheory.Linear ℂ A]
    [MonoidalCategory A]
    (h : HasScalarUnit A) :
    ℂ ≃+* End (𝟙_ A) :=
  RingEquiv.ofBijective (scalarUnitRingHom A) h

@[simp] theorem scalarUnitEquiv_apply
    [Category.{v} A] [Preadditive A] [CategoryTheory.Linear ℂ A]
    [MonoidalCategory A]
    (h : HasScalarUnit A) (c : ℂ) :
    scalarUnitEquiv h c = c • 𝟙 (𝟙_ A) := rfl

end RS
