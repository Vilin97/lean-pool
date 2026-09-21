/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassSubgroupRealization
import LeanPool.ClassFieldTheory.ClassFieldTheory.Theorems.ConductorsAndRayClassFields.RayClassSubgroupEmbedding
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.FiniteAbelianClassFieldContainment
/-!
# Independence of the realization of a ray-class subgroup

The field attached to a fixed modulus and subgroup is well-defined up to
`K`-algebra equivalence.  The equivalence is not claimed to be unique.
-/

open scoped NumberField

noncomputable section

namespace ClassFieldTheory

/-- Two Frobenius-normalized class-field realizations for the same modulus
and ray-class subgroup are isomorphic over the base number field. -/
theorem rayClassSubgroupRealizations_equiv
    (K : Type) [Field K] [NumberField K]
    (m : RayClassModulus K) (H : Subgroup (RayClassGroup m))
    (R₁ R₂ : RayClassSubgroupRealization K m H) :
    Nonempty (R₁.extension ≃ₐ[K] R₂.extension) := by
  obtain ⟨f, _⟩ :=
    exists_rayClassSubgroupEmbedding_artinNaturality K m
      (le_refl H) R₂ R₁
  obtain ⟨g, _⟩ :=
    exists_rayClassSubgroupEmbedding_artinNaturality K m
      (le_refl H) R₁ R₂
  have h₁₂ : (_root_.ideleClassNorm K R₁.extension).range ≤
      (_root_.ideleClassNorm K R₂.extension).range :=
    GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_range_le_of_algHom
      (K := K) R₂.extension R₁.extension g
  have h₂₁ : (_root_.ideleClassNorm K R₂.extension).range ≤
      (_root_.ideleClassNorm K R₁.extension).range :=
    GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_range_le_of_algHom
      (K := K) R₁.extension R₂.extension f
  exact
    (GlobalClassFieldTheory.GlobalClassFields.nonempty_algEquiv_iff_ideleClassNorm_range_eq
      (K := K) R₁.extension R₂.extension).2 (le_antisymm h₁₂ h₂₁)

end ClassFieldTheory
