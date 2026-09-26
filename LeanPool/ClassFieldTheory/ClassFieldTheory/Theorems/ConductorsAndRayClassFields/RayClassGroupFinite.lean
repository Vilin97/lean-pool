/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassGroup
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.RayClass.Topology
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.PublicRayClassComparison
/-!
# Finiteness of the ideal-theoretic ray class group

The comparison with the idèlic ray class group identifies this group with a
quotient by a finite-index congruence subgroup, so it is finite for every
modulus.
-/

@[expose] public section

namespace ClassFieldTheory

universe u

/-- Every ray class group of a number field is finite. -/
theorem rayClassGroup_finite
    (K : Type u) [Field K] [NumberField K]
    (m : RayClassModulus K) :
    Finite (RayClassGroup m) := by
  let m' := GlobalClassFieldComparison.rayClassModulusToOriginal K m
  let : Finite (RayClass.RayClassGroup m') := inferInstance
  exact Finite.of_equiv (RayClass.RayClassGroup m')
    (GlobalClassFieldComparison.rayClassGroupEquivOriginalIdele K m).symm.toEquiv

end ClassFieldTheory
