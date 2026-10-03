/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.HilbertRamification.DecompositionField
/-!
# Decomposition-field extension comparison

This file starts with clause (i): the restriction of `w` to its decomposition
field has a unique extension back to `L`.  The proof works for finite or
infinite Galois extensions and for archimedean or nonarchimedean valuations.
-/

@[expose] public section

noncomputable
section

universe u v

namespace AlgebraicNumberTheory
namespace Valuations

/-- Restriction of an absolute value on `L` to an intermediate field. -/
def absoluteValueRestrictIntermediateField
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (w : AbsoluteValue L ℝ) (E : IntermediateField K L) : AbsoluteValue E ℝ :=
  w.comp (f := algebraMap E L) (algebraMap E L).injective

@[simp] theorem absoluteValueRestrictIntermediateField_apply
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (w : AbsoluteValue L ℝ) (E : IntermediateField K L) (x : E) :
    absoluteValueRestrictIntermediateField w E x = w (x : L) :=
  rfl

/-- Restricting an extension to an intermediate field that contains the base
preserves nontriviality. -/
theorem absoluteValueRestrictIntermediateField_isNontrivial
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK L) (E : IntermediateField K L) :
    (absoluteValueRestrictIntermediateField w.1 E).IsNontrivial := by
  rcases hvK with ⟨a, ha, hva⟩
  refine ⟨algebraMap K E a, ?_, ?_⟩
  · intro hzero
    apply ha
    apply (algebraMap K E).injective
    simpa using hzero
  change w.1 (algebraMap E L (algebraMap K E a)) ≠ 1
  rw [← IsScalarTower.algebraMap_apply K E L, w.2 a]
  exact hva

/-- Regard `w` as an exact extension of its restriction to an intermediate
field. -/
def absoluteValueExtensionOverRestriction
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (w : AbsoluteValue L ℝ) (E : IntermediateField K L) :
    AbsoluteValueExtension
      (absoluteValueRestrictIntermediateField w E) L :=
  ⟨w, fun _ => rfl⟩

/-- The decomposition-field extension comparison: `w|Z_w` has exactly one
extension to `L`. -/
theorem decompositionField_unique_extension_over_decompositionField
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [IsGalois K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK L)
    (w' : AbsoluteValueExtension
      (absoluteValueRestrictIntermediateField w.1
        (HilbertRamification.absoluteValueDecompositionField K w.1)) L) :
    w' = absoluteValueExtensionOverRestriction w.1
      (HilbertRamification.absoluteValueDecompositionField K w.1) := by
  let Z := HilbertRamification.absoluteValueDecompositionField K w.1
  let wZ := absoluteValueRestrictIntermediateField w.1 Z
  let wLZ : AbsoluteValueExtension wZ L :=
    absoluteValueExtensionOverRestriction w.1 Z
  have hwZ : wZ.IsNontrivial :=
    absoluteValueRestrictIntermediateField_isNontrivial vK hvK w Z
  rcases absoluteValueConjugacy wZ hwZ wLZ w' with ⟨σ, hσ⟩
  let σK : L ≃ₐ[K] L :=
    RamificationTheory.HilbertRamification.ValuationSubring.restrictAutomorphismScalars
      (K := K) (M := Z) σ
  have hfix : σK ∈ Z.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    let z : Z := ⟨x, hx⟩
    simpa [σK, z,
      RamificationTheory.HilbertRamification.ValuationSubring.restrictAutomorphismScalars]
      using σ.commutes z
  have hD : σK ∈ HilbertRamification.absoluteValueDecompositionGroup K w.1 := by
    rw [← HilbertRamification.absoluteValueDecompositionField_fixingSubgroup_eq K w.1]
    exact hfix
  have hstab :
      absoluteValueExtensionConjugate vK w σK = w :=
    (HilbertRamification.mem_absoluteValueDecompositionGroup_iff_extensionConjugate_eq
      vK hvK w σK).mp hD
  apply Subtype.ext
  have hw' := congrArg Subtype.val hσ
  calc
    w'.1 = (absoluteValueExtensionConjugate wZ wLZ σ).1 := hw'
    _ = (absoluteValueExtensionConjugate vK w σK).1 := rfl
    _ = w.1 := congrArg Subtype.val hstab

end Valuations
end AlgebraicNumberTheory
