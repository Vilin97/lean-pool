/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassSubgroupQuotientEquiv
/-!
# Degree of the class field of a ray-class subgroup

The degree of a finite abelian class field is the index of its defining
subgroup in the ray class group.
-/

open scoped NumberField

noncomputable section

namespace ClassFieldTheory

universe u

/-- A ray-class subgroup realization has degree equal to the subgroup index. -/
theorem rayClassSubgroup_degree
    (K : Type u) [Field K] [NumberField K]
    (m : RayClassModulus K) (H : Subgroup (RayClassGroup m))
    (R : RayClassSubgroupRealization K m H) :
    Module.finrank K R.extension = H.index := by
  calc
    Module.finrank K R.extension =
        Nat.card (R.extension ≃ₐ[K] R.extension) :=
      (IsGalois.card_aut_eq_finrank K R.extension).symm
    _ = Nat.card (RayClassGroup m ⧸ H) :=
      Nat.card_congr (rayClassSubgroupQuotientEquiv K m H R).symm.toEquiv
    _ = H.index := H.index_eq_card.symm

end ClassFieldTheory
