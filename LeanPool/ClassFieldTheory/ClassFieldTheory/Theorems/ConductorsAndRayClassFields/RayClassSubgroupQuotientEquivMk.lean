/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassSubgroupQuotientEquiv
/-!
# Evaluation of a ray-class subgroup quotient isomorphism

The quotient isomorphism retains the prescribed Artin normalization.
-/

open scoped NumberField

noncomputable section

namespace ClassFieldTheory

universe u

/-- A ray class maps to its original Artin value under the induced quotient isomorphism. -/
@[simp]
theorem rayClassSubgroupQuotientEquiv_mk
    (K : Type u) [Field K] [NumberField K]
    (m : RayClassModulus K) (H : Subgroup (RayClassGroup m))
    (R : RayClassSubgroupRealization K m H)
    (x : RayClassGroup m) :
    rayClassSubgroupQuotientEquiv K m H R
        (QuotientGroup.mk' H x) = R.artin x := by
  rfl

end ClassFieldTheory
