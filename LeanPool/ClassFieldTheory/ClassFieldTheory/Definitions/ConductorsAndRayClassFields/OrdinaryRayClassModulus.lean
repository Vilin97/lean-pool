/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassModulus
/-!
# The ordinary class-group modulus
-/

@[expose] public section

namespace ClassFieldTheory

universe u

/-- The modulus with no finite exponent and no positivity condition.  Its ray
class group is the ordinary ideal class group. -/
def ordinaryRayClassModulus
    (K : Type u) [Field K] [NumberField K] : RayClassModulus K where
  finitePart := 0
  infinitePart := ∅

/-- The ordinary class-group modulus is below every ray modulus. -/
theorem ordinaryRayClassModulus_le
    (K : Type u) [Field K] [NumberField K]
    (m : RayClassModulus K) :
    ordinaryRayClassModulus K ≤ m := by
  constructor
  · change ∀ v, 0 ≤ m.finitePart v
    exact fun _ => Nat.zero_le _
  · exact Finset.empty_subset _

end ClassFieldTheory
