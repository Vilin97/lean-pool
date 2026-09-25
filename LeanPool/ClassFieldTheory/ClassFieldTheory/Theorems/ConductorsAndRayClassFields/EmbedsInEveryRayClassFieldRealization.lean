/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.EmbedsInRayClassField
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Theorems.ConductorsAndRayClassFields.RayClassFieldModulusMonotone
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Theorems.ConductorsAndRayClassFields.RayClassFieldReciprocity
/-!
# Independence of the ray class field realization

The existential definition of `EmbedsInRayClassField` is independent of
which Frobenius-normalized realization is chosen.  It does not assert
uniqueness of the embedding itself.
-/

@[expose] public section

open scoped NumberField

noncomputable
section

namespace ClassFieldTheory

/-- Embedding in some ray class field realization is equivalent to
embedding in every realization for the same modulus. -/
theorem embedsInRayClassField_iff_every_realization
    (K L : Type)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    (m : RayClassModulus K) :
    EmbedsInRayClassField K L m ↔
      ∀ R : RayClassFieldRealization K m,
        Nonempty (L →ₐ[K] R.extension) := by
  constructor
  · rintro ⟨R₀, ⟨f⟩⟩ R
    have hEq : R₀.extension.1 = R.extension.1 :=
      le_antisymm
        (rayClassFieldRealization_mono_modulus le_rfl R₀ R)
        (rayClassFieldRealization_mono_modulus le_rfl R R₀)
    exact ⟨(IntermediateField.equivOfEq hEq).toAlgHom.comp f⟩
  · intro h
    obtain ⟨R⟩ := rayClassField_reciprocity K m
    exact ⟨R, h R⟩

end ClassFieldTheory
