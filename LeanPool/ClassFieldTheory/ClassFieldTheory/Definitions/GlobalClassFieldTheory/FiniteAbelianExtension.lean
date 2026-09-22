/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.NumberTheory.NumberField.Basic
/-!
# Finite abelian extensions of number fields

This module packages finite abelian extensions inside Mathlib's chosen
separable closure.  It contains no class-field-theory implementation.
-/

noncomputable section

namespace ClassFieldTheory

universe u

/-- A finite abelian extension of a number field inside Mathlib's chosen
separable closure.  The inherited order is inclusion of intermediate fields. -/
abbrev FiniteAbelianExtension
    (K : Type u) [Field K] :=
  { E : IntermediateField K (SeparableClosure K) //
      FiniteDimensional K E ∧ IsAbelianGalois K E }

namespace FiniteAbelianExtension

instance {K : Type u} [Field K] [NumberField K] :
    CoeSort (FiniteAbelianExtension K) (Type u) where
  coe E := E.1

instance {K : Type u} [Field K] [NumberField K]
    (E : FiniteAbelianExtension K) : Field E :=
  inferInstance

instance {K : Type u} [Field K] [NumberField K]
    (E : FiniteAbelianExtension K) : FiniteDimensional K E :=
  E.2.1

instance {K : Type u} [Field K] [NumberField K]
    (E : FiniteAbelianExtension K) : Algebra K E :=
  inferInstance

instance {K : Type u} [Field K] [NumberField K]
    (E : FiniteAbelianExtension K) : NumberField E :=
  NumberField.of_module_finite K E

instance {K : Type u} [Field K] [NumberField K]
    (E : FiniteAbelianExtension K) : IsAbelianGalois K E :=
  E.2.2

end FiniteAbelianExtension

end ClassFieldTheory
