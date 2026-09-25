/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteAbelianSubextension
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalNormResidueNaturality
public import Mathlib.FieldTheory.Galois.Abelian
/-!
# Embedded finite abelian subextensions

An embedding of an actual finite abelian extension into the rational
separable closure determines a finite abelian subextension of the fixing
subgroup of the embedded base field. This file also allows that base fixing
subgroup to be replaced by a propositionally equal selected subgroup, as is
needed by concrete class-field realizations.
-/

@[expose] public section

open scoped NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open ClassFormation
open Reciprocity

/-- An actual finite abelian extension embedded in the rational separable
closure, represented as a finite abelian subextension of a selected base
subgroup equal to the fixing subgroup of the embedded base field. -/
noncomputable def numberFieldEmbeddedAbelianSubextension
    (K E : Type)
    [Field K] [NumberField K]
    [Field E] [NumberField E]
    [Algebra K E] [FiniteDimensional K E]
    [IsAbelianGalois K E]
    (j : E →ₐ[ℚ] SeparableClosure ℚ)
    (B : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (hbase : numberFieldEmbeddedBaseSubgroup K E j = B) :
    FiniteAbelianSubextension B := by
  subst B
  exact
    { toFiniteGaloisExtension :=
        numberFieldEmbeddedFiniteGaloisSubextension K E j
      commutative := by
        let e :
            (numberFieldEmbeddedFiniteGaloisSubextension K E j).extensionQuotient ≃*
              Gal(E/K) := by
          exact
            numberFieldEmbeddedExtensionQuotientEquivGaloisGroup
              K E j
        exact
          { is_comm.comm := fun x y => by
              apply e.injective
              simpa only [map_mul] using
                (inferInstance :
                  IsMulCommutative
                    (Gal(E/K))).is_comm.comm
                  (e x) (e y) } }

/-- The top subgroup of the embedded abelian subextension is the fixing
subgroup of the embedded top field. -/
@[simp]
theorem numberFieldEmbeddedAbelianSubextension_field
    (K E : Type)
    [Field K] [NumberField K]
    [Field E] [NumberField E]
    [Algebra K E] [FiniteDimensional K E]
    [IsAbelianGalois K E]
    (j : E →ₐ[ℚ] SeparableClosure ℚ)
    (B : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (hbase : numberFieldEmbeddedBaseSubgroup K E j = B) :
    (numberFieldEmbeddedAbelianSubextension K E j B hbase).field =
      numberFieldEmbeddedTopSubgroup K E j := by
  subst B
  rfl

end GlobalClassFields
end GlobalClassFieldTheory
