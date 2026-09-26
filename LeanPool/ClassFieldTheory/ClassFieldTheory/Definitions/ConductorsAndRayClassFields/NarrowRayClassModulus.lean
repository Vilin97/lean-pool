/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassModulus
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
/-!
# The narrow class-group modulus
-/

@[expose] public section

noncomputable
section



namespace ClassFieldTheory

universe u

open scoped Classical in
/-- The modulus with no finite exponent and positivity at every real place.
Its ray class group is the narrow ideal class group. -/
def narrowRayClassModulus
    (K : Type u) [Field K] [NumberField K] : RayClassModulus K where
  finitePart := 0
  infinitePart := Finset.univ

end ClassFieldTheory
