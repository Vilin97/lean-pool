/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.Algebra.Field.Shrink
public import Mathlib.Algebra.Ring.Shrink
public import Mathlib.Basic.Countable.Small
public import Mathlib.Data.Rat.Encodable
public import Mathlib.LinearAlgebra.Countable
public import Mathlib.NumberTheory.NumberField.Basic
/-!
# Small models of number fields

A number field has finite dimension over the countable field `ℚ`, so its
underlying type has a representative in the lowest universe.  The ring
equivalence to that representative preserves the number-field structure.
-/

@[expose] public section

namespace ClassFieldTheory

universe u

/-- Every number field can be represented by a type in universe zero. -/
theorem numberField_small (F : Type u) [Field F] [NumberField F] :
    Small.{0} F := by
  let : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  infer_instance

/-- The shrunk model of a number field remains a number field. -/
theorem numberField_shrink (F : Type u) [Field F] [NumberField F] :
    letI : Small.{0} F := numberField_small F
    NumberField (Shrink.{0} F) := by
  let : Small.{0} F := numberField_small F
  exact NumberField.of_ringEquiv F (Shrink.{0} F) (Shrink.ringEquiv F).symm

end ClassFieldTheory
