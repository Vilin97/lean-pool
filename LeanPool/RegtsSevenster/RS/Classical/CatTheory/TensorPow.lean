/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.CatTheory.Length

/-!
# Tensor powers of an object

The iterated tensor power `X ^ ⊗ n`, its mixed form and the
condition that a single object tensor-generates are defined in
`RS/Definitions.lean`.  This module carries the defining recursion
equations, the stronger retract form of generation the envelope
satisfies, and the implication from it to Deligne's subquotient
form.
-/

@[expose] public section

namespace RS

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe v u

variable (A : Type u)

/-- The empty tensor power is the unit. -/
theorem tensorPow_zero [Category.{v} A] [MonoidalCategory A]
    (X : A) : tensorPow A X 0 = 𝟙_ A := rfl

/-- `X ^ ⊗ (n + 1)` is `X ^ ⊗ n ⊗ X`.  Together with
`tensorPow_zero` this is the defining recursion. -/
theorem tensorPow_succ [Category.{v} A] [MonoidalCategory A]
    (X : A) (n : ℕ) :
    tensorPow A X (n + 1) = tensorPow A X n ⊗ X := rfl

/-- **Generation by retracts of pure powers**: every object is a
retract of a finite biproduct of tensor powers of `X` alone.  This
is how the envelope generates, and it is stronger than Deligne's
hypothesis in two ways at once — a retract rather than a
subquotient, and no duals among the powers. -/
def RetractGeneratedBy [Category.{v} A] [MonoidalCategory A]
    [Preadditive A] [HasFiniteBiproducts A]
    (X : A) : Prop :=
  ∀ Y : A, ∃ (k : ℕ) (ns : Fin k → ℕ)
    (ι : Y ⟶ ⨁ fun i => tensorPow A X (ns i))
    (π : (⨁ fun i => tensorPow A X (ns i)) ⟶ Y),
    ι ≫ π = 𝟙 Y

/-- A pure tensor power is the mixed power with no dual factors. -/
def tensorPowIsoMixed [Category.{v} A] [MonoidalCategory A]
    [RigidCategory A] (X : A) (n : ℕ) :
    tensorPow A X n ≅ mixedPow A X n 0 :=
  (ρ_ (tensorPow A X n)).symm

/-- **The retract formulation implies Deligne's.**  A splitting
`ι ≫ π = 𝟙` makes `ι` a split mono, hence a mono, and `Y` is a
quotient of itself, so a retract of a biproduct of pure powers is a
subquotient of the corresponding biproduct of mixed powers. -/
theorem tensorGeneratedBy_of_retract [Category.{v} A] [MonoidalCategory A]
    [Preadditive A]
    [HasFiniteBiproducts A] [RigidCategory A] {X : A}
    (h : RetractGeneratedBy A X) : TensorGeneratedBy A X := by
  intro Y
  obtain ⟨k, ns, ι, π, hιπ⟩ := h Y
  refine ⟨k, fun t => (ns t, 0),
    isSubquotientOf_of_retract
      (ι ≫ (biproduct.mapIso fun i => tensorPowIsoMixed A X (ns i)).hom)
      ((biproduct.mapIso fun i => tensorPowIsoMixed A X (ns i)).inv ≫ π)
      ?_⟩
  rw [Category.assoc, Iso.hom_inv_id_assoc, hιπ]

end RS
