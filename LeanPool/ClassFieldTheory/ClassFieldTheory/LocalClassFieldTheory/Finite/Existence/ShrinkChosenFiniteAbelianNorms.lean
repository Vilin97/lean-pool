/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.ShrinkChosenFiniteAbelianFields
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.ShrinkFiniteAbelianNorms
/-!
# Actual norm subgroups in the chosen small-base separable closure

The finite-abelian-field order equivalence carries the actual field-norm
subgroup, not merely an abstract subgroup assigned by a classification.
-/

@[expose] public section

noncomputable
section

namespace LocalFieldTheory

universe u

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- The two-step finite-field transport preserves the actual field-norm
subgroup after identifying the multiplicative groups of `K` and `Shrink K`. -/
theorem shrinkChosenFiniteAbelian_normSubgroup_map
    (E : ClassFieldTheory.FiniteAbelianLocalExtension K) :
    letI : Small.{0} K := nonarchimedeanLocalField_small K
    (E.normSubgroup).map
        (Units.mapEquiv (Shrink.ringEquiv K).symm.toMulEquiv).toMonoidHom =
      (shrinkChosenFiniteAbelianField K E).normSubgroup := by
  let : Small.{0} K := nonarchimedeanLocalField_small K
  let : Algebra (Shrink.{0} K) (SeparableClosure K) :=
    shrinkSeparableClosureAlgebra K
  let M := shrinkIntermediateField K E.1
  let c := shrinkSeparableClosureEquiv K
  let : FiniteDimensional (Shrink.{0} K) M :=
    shrinkIntermediateField_finiteDimensional K E
  let : FiniteDimensional (Shrink.{0} K) (M.map c.symm.toAlgHom) :=
    ClassFieldTheory.finiteDimensional_intermediateField_map_algEquiv c.symm M
  change (ClassFieldTheory.fieldNormSubgroup K E.1).map
      (Units.mapEquiv (Shrink.ringEquiv K).symm.toMulEquiv).toMonoidHom =
    ClassFieldTheory.fieldNormSubgroup (Shrink.{0} K)
      (M.map c.symm.toAlgHom)
  calc
    _ = ClassFieldTheory.fieldNormSubgroup (Shrink.{0} K) M :=
      shrinkIntermediateField_normSubgroup_map K E
    _ = ClassFieldTheory.fieldNormSubgroup (Shrink.{0} K)
        (M.map c.symm.toAlgHom) := by
          have h := ClassFieldTheory.fieldNormSubgroup_map_ringEquiv
            (RingEquiv.refl (Shrink.{0} K))
            (IntermediateField.intermediateFieldMap c.symm M).toRingEquiv
            (ClassFieldTheory.intermediateFieldMap_commutes c.symm M)
          have hmapid :
              (Units.mapEquiv
                (RingEquiv.refl (Shrink.{0} K)).toMulEquiv).toMonoidHom =
                MonoidHom.id (Shrink.{0} K)ˣ := by
            ext x
            rfl
          rw [hmapid, Subgroup.map_id] at h
          exact h

end LocalFieldTheory
