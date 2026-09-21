/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassFieldRealization
import LeanPool.ClassFieldTheory.ClassFieldTheory.Theorems.ConductorsAndRayClassFields.ExistsRayArtinModulusProjection
/-!
# Ray class fields increase with the modulus

The modulus projection produces an embedding of realizations.  Normality
upgrades that embedding to literal inclusion in the fixed separable closure.
-/

open scoped NumberField

noncomputable section

namespace ClassFieldTheory

/-- For `m ≤ n`, every realization of the ray class field of `m` is a
subfield of every realization of the ray class field of `n` in the fixed
separable closure. -/
theorem rayClassFieldRealization_mono_modulus
    {K : Type} [Field K] [NumberField K]
    {m n : RayClassModulus K} (hmn : m ≤ n)
    (Rm : RayClassFieldRealization K m)
    (Rn : RayClassFieldRealization K n) :
    Rm.extension.1 ≤ Rn.extension.1 := by
  obtain ⟨f, _⟩ := exists_rayArtin_modulusProjection hmn Rm Rn
  let σ : Rm.extension →ₐ[K] SeparableClosure K :=
    (IntermediateField.val Rn.extension.1).comp f
  have hσ : σ.fieldRange = Rm.extension.1 :=
    AlgHom.fieldRange_of_normal σ
  rw [← hσ]
  intro x hx
  obtain ⟨y, rfl⟩ := AlgHom.mem_fieldRange.mp hx
  exact (f y).property

end ClassFieldTheory
