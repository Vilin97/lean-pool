/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassSubgroupRealization
import Mathlib.GroupTheory.QuotientGroup.Basic
/-!
# The quotient induced by a ray-class Artin map

The prescribed subgroup is identified with the Artin kernel before applying
the first isomorphism theorem.
-/

open scoped NumberField

noncomputable section

namespace ClassFieldTheory

universe u

/-- The isomorphism induced by the Artin map of a ray-class realization. -/
def rayClassSubgroupQuotientEquiv
    (K : Type u) [Field K] [NumberField K]
    (m : RayClassModulus K) (H : Subgroup (RayClassGroup m))
    (R : RayClassSubgroupRealization K m H) :
    (RayClassGroup m ⧸ H) ≃* (R.extension ≃ₐ[K] R.extension) :=
  (QuotientGroup.quotientMulEquivOfEq R.artin_ker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      R.artin R.artin_surjective)

end ClassFieldTheory
