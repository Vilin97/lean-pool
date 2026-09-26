/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassFieldRealization
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassGroup
/-!
# Degree of a ray class field

For any ray class field realization of `m`, its degree is the cardinality of
the ideal-theoretic ray class group.  The realization is explicit, so this
module does not depend on an implementation-level choice of field.
-/

@[expose] public section

open scoped NumberField

noncomputable
section

namespace ClassFieldTheory

universe u

open scoped Classical in
/-- The ray class field has degree equal to the ray class number. -/
theorem rayClassField_degree
    (K : Type u) [Field K] [NumberField K]
    (m : RayClassModulus K)
    (R : RayClassFieldRealization K m) :
    Module.finrank K R.extension = Nat.card (RayClassGroup m) := by
  calc
    Module.finrank K R.extension =
        Nat.card (R.extension ≃ₐ[K] R.extension) :=
      (IsGalois.card_aut_eq_finrank K R.extension).symm
    _ = Nat.card (RayClassGroup m) :=
      Nat.card_congr R.artinEquiv.symm.toEquiv

end ClassFieldTheory
