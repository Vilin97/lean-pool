/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassSubgroupRealization
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Theorems.ConductorsAndRayClassFields.RayClassSubgroupFieldAntitone
/-!
# Uniqueness of a ray-class subgroup field inside the fixed closure

The class field is independent of the Frobenius-normalized realization as an
actual intermediate field, not just up to abstract isomorphism.  This does
not assert uniqueness of the embedding or of the Artin map.
-/

@[expose] public section

namespace ClassFieldTheory

/-- Two realizations for the same modulus and subgroup have the same
intermediate field in the chosen separable closure. -/
theorem rayClassSubgroupRealizations_eq
    (K : Type) [Field K] [NumberField K]
    (m : RayClassModulus K) (H : Subgroup (RayClassGroup m))
    (R₁ R₂ : RayClassSubgroupRealization K m H) :
    R₁.extension.1 = R₂.extension.1 := by
  apply le_antisymm
  · exact rayClassSubgroupField_antitone K m (le_refl H) R₂ R₁
  · exact rayClassSubgroupField_antitone K m (le_refl H) R₁ R₂

end ClassFieldTheory
