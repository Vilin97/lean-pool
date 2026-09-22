/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassGroup
import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassSubgroupRealization
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.PublicRayClassComparison
/-!
# Existence of the class field of a ray-class subgroup

Every subgroup of an ideal-theoretic ray class group is the kernel of the
Frobenius-normalized Artin map of a finite abelian extension.  The statement
uses ideal classes; the proof transports the existing idelic reciprocity
construction to that interface.
-/

open scoped NumberField

noncomputable section

namespace ClassFieldTheory

open scoped Classical in
/-- Every ray-class subgroup has a finite abelian class-field realization. -/
theorem rayClassSubgroup_existence
    (K : Type) [Field K] [NumberField K]
    (m : RayClassModulus K) (H : Subgroup (RayClassGroup m)) :
    Nonempty (RayClassSubgroupRealization K m H) := by
  exact GlobalClassFieldComparison.rayClassSubgroup_existence K m H

end ClassFieldTheory
