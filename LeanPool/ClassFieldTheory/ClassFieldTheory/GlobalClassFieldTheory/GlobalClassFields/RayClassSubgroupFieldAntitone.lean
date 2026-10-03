/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.PublicRayClassComparison
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.RayClassFieldRealization
/-!
# Subgroup order and chosen ray class fields

The selected field of a larger ray-class subgroup is contained in that of
a smaller subgroup, as actual subfields of the fixed separable closure.
-/

@[expose] public section

open scoped NumberField
noncomputable
section

namespace ClassFieldTheory

open scoped Classical in
/-- For one modulus, inclusion of ray-class subgroups reverses inclusion of
their selected class fields inside the fixed separable closure. -/
theorem chosenRayClassSubgroupSubfield_antitone
    (K : Type) [Field K] [NumberField K]
    (m : RayClassModulus K)
    {H J : Subgroup (RayClassGroup m)} (hHJ : H ≤ J) :
    GlobalClassFieldTheory.GlobalClassFields.rayClassSubgroupSubfield
        (K := K) (GlobalClassFieldComparison.rayClassModulusToOriginal K m)
        (J.map (GlobalClassFieldComparison.rayClassGroupEquivOriginalIdele K m).toMonoidHom) ≤
      GlobalClassFieldTheory.GlobalClassFields.rayClassSubgroupSubfield
        (K := K) (GlobalClassFieldComparison.rayClassModulusToOriginal K m)
        (H.map (GlobalClassFieldComparison.rayClassGroupEquivOriginalIdele K m).toMonoidHom) := by
  let m' := GlobalClassFieldComparison.rayClassModulusToOriginal K m
  let e := GlobalClassFieldComparison.rayClassGroupEquivOriginalIdele K m
  have hmap : H.map e.toMonoidHom ≤ J.map e.toMonoidHom :=
    Subgroup.map_mono hHJ
  have hfixed :
      GlobalClassFieldTheory.GlobalClassFields.rayClassSubgroupFixedField
          (K := K) m' (J.map e.toMonoidHom) ≤
        GlobalClassFieldTheory.GlobalClassFields.rayClassSubgroupFixedField
          (K := K) m' (H.map e.toMonoidHom) := by
    exact IntermediateField.fixedField_le (Subgroup.map_mono hmap)
  exact
    IntermediateField.map_mono
      (GlobalClassFieldTheory.GlobalClassFields.rayClassFieldEmbedding K m')
      hfixed

end ClassFieldTheory
