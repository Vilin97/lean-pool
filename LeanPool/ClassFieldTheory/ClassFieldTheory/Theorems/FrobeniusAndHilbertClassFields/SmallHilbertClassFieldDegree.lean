/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.IsSmallHilbertClassField
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.GlobalClassFieldTheory.FiniteAbelianExtension
public import Mathlib.NumberTheory.NumberField.ClassNumber
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.MathlibFrobeniusHilbertComparison
/-!
# Degree of the small Hilbert class field

Any extension satisfying the intrinsic small-Hilbert-class-field property
has degree equal to the ordinary class number of the base field.
-/

@[expose] public section

open scoped NumberField

noncomputable
section

namespace ClassFieldTheory

/-- The small Hilbert class field has degree equal to the class number. -/
theorem smallHilbertClassField_degree_eq_classNumber
    (K : Type) [Field K] [NumberField K]
    (E : FiniteAbelianExtension K) (hE : IsSmallHilbertClassField E) :
    Module.finrank K E = NumberField.classNumber K :=
  GlobalClassFieldComparison.smallHilbertClassField_degree_eq_classNumber_of_isSmall K E hE

end ClassFieldTheory
