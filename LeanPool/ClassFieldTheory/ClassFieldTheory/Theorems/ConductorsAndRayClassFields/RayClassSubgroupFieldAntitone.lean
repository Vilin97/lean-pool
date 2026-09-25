/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassSubgroupRealization
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Theorems.ConductorsAndRayClassFields.RayClassSubgroupEmbedding
/-!
# Inclusion of ray-class subgroup class fields

The fields are intermediate fields of one fixed separable closure, so the
conclusion is literal inclusion rather than merely an abstract embedding.
-/

@[expose] public section

open scoped NumberField

noncomputable section

namespace ClassFieldTheory

/-- For one modulus, a larger ray-class subgroup gives a smaller class
field inside the fixed separable closure.  This holds for any choices of
Frobenius-normalized realizations. -/
theorem rayClassSubgroupField_antitone
    (K : Type) [Field K] [NumberField K]
    (m : RayClassModulus K)
    {H J : Subgroup (RayClassGroup m)} (hHJ : H ≤ J)
    (RH : RayClassSubgroupRealization K m H)
    (RJ : RayClassSubgroupRealization K m J) :
    RJ.extension.1 ≤ RH.extension.1 := by
  obtain ⟨f, _⟩ :=
    exists_rayClassSubgroupEmbedding_artinNaturality K m hHJ RH RJ
  let σ : RJ.extension →ₐ[K] SeparableClosure K :=
    (IntermediateField.val RH.extension.1).comp f
  have hσ : σ.fieldRange = RJ.extension.1 :=
    AlgHom.fieldRange_of_normal σ
  rw [← hσ]
  intro x hx
  obtain ⟨y, rfl⟩ := AlgHom.mem_fieldRange.mp hx
  exact (f y).property

end ClassFieldTheory
