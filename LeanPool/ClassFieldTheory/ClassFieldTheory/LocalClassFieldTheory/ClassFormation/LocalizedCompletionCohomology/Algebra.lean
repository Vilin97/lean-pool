/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalizedCompletionCohomology.CompMulEquiv
/-!
# Algebra for localized completion cohomology

This file provides named algebra, finite-dimensional, Galois, scalar-tower, and
global-to-local embedding providers for localized completions.
-/

open AlgebraicNumberTheory.Valuations
open HilbertRamification
open LocalClassFieldTheory
open LocalFieldTheory
open CyclicCohomology
open CyclicCohomology.ProfiniteCohomology.Herbrand
open scoped TensorProduct

noncomputable section

namespace LocalClassFieldTheory

universe u v

variable {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L]

/-- The canonical algebra structure on an algebraic localization over the
completed base.  Naming this instance keeps clients from rebuilding the
completion tower at every declaration boundary. -/
@[reducible]
noncomputable def localizedCompletionBaseAlgebra
    (vK : AbsoluteValue K ℝ)
    (w : AbsoluteValueExtension vK L) :
    Algebra vK.Completion (LocalizedCompletion vK w) := by
  letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  letI : SMul K w.1.Completion := hK.toSMul
  letI : Algebra vK.Completion w.1.Completion :=
    AbsoluteValue.completionAlgebra vK w.1 w.2
  exact inferInstance

/-- The named finite-dimensional certificate for an algebraic localization
of a finite global extension. -/
theorem localizedCompletionFiniteDimensional
    [FiniteDimensional K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK L) :
    letI : Algebra vK.Completion (LocalizedCompletion vK w) :=
      localizedCompletionBaseAlgebra vK w
    FiniteDimensional vK.Completion (LocalizedCompletion vK w) := by
  let _ := localizedCompletionBaseAlgebra vK w
  exact localizedCompletionModuleFinite vK hvK w

/-- The named Galois certificate for the algebraic localization of a Galois
extension. -/
theorem localizedCompletionIsGalois
    [IsGalois K L]
    (vK : AbsoluteValue K ℝ)
    (w : AbsoluteValueExtension vK L) :
    letI : Algebra vK.Completion (LocalizedCompletion vK w) :=
      localizedCompletionBaseAlgebra vK w
    IsGalois vK.Completion (LocalizedCompletion vK w) := by
  let _ := localizedCompletionBaseAlgebra vK w
  exact HilbertRamification.algebraicLocalization_isGalois vK w

/-- The algebra structure on the algebraic localization induced by the tower
`K → K_v → L_w`. -/
@[reducible]
noncomputable def localizedCompletionGlobalAlgebra
    (vK : AbsoluteValue K ℝ)
    (w : AbsoluteValueExtension vK L) :
    letI : Algebra vK.Completion (LocalizedCompletion vK w) :=
      localizedCompletionBaseAlgebra vK w
    Algebra K (LocalizedCompletion vK w) := by
  letI : Algebra vK.Completion (LocalizedCompletion vK w) :=
    localizedCompletionBaseAlgebra vK w
  exact
    ((algebraMap vK.Completion
        (LocalizedCompletion vK w)).comp
      (algebraMap K vK.Completion)).toAlgebra

theorem localizedCompletionIsScalarTower
    (vK : AbsoluteValue K ℝ)
    (w : AbsoluteValueExtension vK L) :
    letI : Algebra vK.Completion (LocalizedCompletion vK w) :=
      localizedCompletionBaseAlgebra vK w
    letI := localizedCompletionGlobalAlgebra vK w
    IsScalarTower K vK.Completion
      (LocalizedCompletion vK w) := by
  let _ : Algebra vK.Completion (LocalizedCompletion vK w) :=
    localizedCompletionBaseAlgebra vK w
  let _ := localizedCompletionGlobalAlgebra vK w
  exact IsScalarTower.of_algebraMap_eq' rfl

/-- The canonical global-to-local embedding as a `K`-algebra homomorphism. -/
noncomputable def localizedCompletionToAlgHom
    (vK : AbsoluteValue K ℝ)
    (w : AbsoluteValueExtension vK L) :
    letI : Algebra vK.Completion (LocalizedCompletion vK w) :=
      localizedCompletionBaseAlgebra vK w
    letI := localizedCompletionGlobalAlgebra vK w
    letI := localizedCompletionIsScalarTower vK w
    L →ₐ[K] LocalizedCompletion vK w := by
  letI : Algebra vK.Completion (LocalizedCompletion vK w) :=
    localizedCompletionBaseAlgebra vK w
  letI := localizedCompletionGlobalAlgebra vK w
  letI := localizedCompletionIsScalarTower vK w
  exact
    { __ := AbsoluteValue.toAlgebraicLocalization vK w.1 w.2
      commutes' := fun x ↦ by
        change
          AbsoluteValue.toAlgebraicLocalization
              vK w.1 w.2 (algebraMap K L x) =
            algebraMap vK.Completion
              (LocalizedCompletion vK w)
              (algebraMap K vK.Completion x)
        exact
          AbsoluteValue.toAlgebraicLocalization_algebraMap
            vK w.1 w.2 x }

/-- The algebraic localization is generated over the completed base by the
canonical image of the global extension. -/
theorem localizedCompletion_adjoin_range_eq_top
    (vK : AbsoluteValue K ℝ)
    (w : AbsoluteValueExtension vK L) :
    letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI : Algebra vK.Completion w.1.Completion :=
      AbsoluteValue.completionAlgebra vK w.1 w.2
    letI := localizedCompletionGlobalAlgebra vK w
    letI := localizedCompletionIsScalarTower vK w
    IntermediateField.adjoin vK.Completion
      (Set.range
        (AbsoluteValue.toAlgebraicLocalization vK w.1 w.2)) = ⊤ := by
  let _ := localizedCompletionBaseAlgebra vK w
  let _ := localizedCompletionGlobalAlgebra vK w
  let _ := localizedCompletionIsScalarTower vK w
  exact
    HilbertRamification.decompositionField_localization_adjoin_range_eq_top
      vK w

/-- A global primitive element remains a primitive element after passing to
the chosen algebraic localization over the completed base field. -/
theorem localizedCompletion_adjoin_image_eq_top_of_adjoin_eq_top
    (vK : AbsoluteValue K ℝ)
    (w : AbsoluteValueExtension vK L) (β : L)
    (hβ : IntermediateField.adjoin K {β} = ⊤) :
    letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI : Algebra vK.Completion w.1.Completion :=
      AbsoluteValue.completionAlgebra vK w.1 w.2
    letI := localizedCompletionGlobalAlgebra vK w
    letI := localizedCompletionIsScalarTower vK w
    IntermediateField.adjoin vK.Completion
      {AbsoluteValue.toAlgebraicLocalization vK w.1 w.2 β} = ⊤ := by
  let _ := localizedCompletionBaseAlgebra vK w
  let _ := localizedCompletionGlobalAlgebra vK w
  let _ := localizedCompletionIsScalarTower vK w
  let toF := localizedCompletionToAlgHom vK w
  let βw := AbsoluteValue.toAlgebraicLocalization vK w.1 w.2 β
  have hfieldRange :
      toF.fieldRange = IntermediateField.adjoin K {βw} := by
    rw [AlgHom.fieldRange_eq_map, ← hβ,
      IntermediateField.adjoin_map, Set.image_singleton]
    rfl
  let R : IntermediateField vK.Completion (LocalizedCompletion vK w) :=
    IntermediateField.adjoin vK.Completion {βw}
  have hKAdjoin :
      IntermediateField.adjoin K {βw} ≤ R.restrictScalars K := by
    apply IntermediateField.adjoin_le_iff.mpr
    intro x hx
    have hx' : x = βw := Set.mem_singleton_iff.mp hx
    subst x
    exact IntermediateField.subset_adjoin vK.Completion
      {βw} (Set.mem_singleton βw)
  have hrange :
      Set.range (AbsoluteValue.toAlgebraicLocalization vK w.1 w.2) ⊆ R := by
    rintro _ ⟨x, rfl⟩
    change toF x ∈ R
    have hx : toF x ∈ toF.fieldRange := ⟨x, rfl⟩
    rw [hfieldRange] at hx
    exact hKAdjoin hx
  apply top_unique
  rw [← localizedCompletion_adjoin_range_eq_top vK w]
  exact IntermediateField.adjoin_le_iff.mpr hrange

variable [IsGalois K L]

/-- Every element in the canonical image of the global extension is separable
over the completed base. -/
theorem localizedCompletion_generator_isSeparable
    (vK : AbsoluteValue K ℝ)
    (w : AbsoluteValueExtension vK L) (x : L) :
    letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI : Algebra vK.Completion w.1.Completion :=
      AbsoluteValue.completionAlgebra vK w.1 w.2
    letI := localizedCompletionGlobalAlgebra vK w
    letI := localizedCompletionIsScalarTower vK w
    IsSeparable vK.Completion
      (AbsoluteValue.toAlgebraicLocalization vK w.1 w.2 x) := by
  let _ := localizedCompletionBaseAlgebra vK w
  let _ := localizedCompletionGlobalAlgebra vK w
  let _ := localizedCompletionIsScalarTower vK w
  exact
    HilbertRamification.decompositionField_toLocalization_isSeparable
      vK w x

/-- The completed-base minimal polynomial of every canonical global generator
splits in the algebraic localization. -/
theorem localizedCompletion_generator_minpoly_splits
    (vK : AbsoluteValue K ℝ)
    (w : AbsoluteValueExtension vK L) (x : L) :
    letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI : Algebra vK.Completion w.1.Completion :=
      AbsoluteValue.completionAlgebra vK w.1 w.2
    letI := localizedCompletionGlobalAlgebra vK w
    letI := localizedCompletionIsScalarTower vK w
    ((minpoly vK.Completion
        (AbsoluteValue.toAlgebraicLocalization vK w.1 w.2 x)).map
      (algebraMap vK.Completion
        (LocalizedCompletion vK w))).Splits := by
  let _ := localizedCompletionBaseAlgebra vK w
  let _ := localizedCompletionGlobalAlgebra vK w
  let _ := localizedCompletionIsScalarTower vK w
  exact
    HilbertRamification.decompositionField_toLocalization_minpoly_splits
      vK w x

open scoped IsMulCommutative in
omit [IsGalois K L] in
/-- The algebraic localization of an abelian Galois extension is abelian
Galois over the completed base field. -/
theorem localizedCompletion_isAbelianGalois
    [IsAbelianGalois K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK L) :
    letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI : Algebra vK.Completion w.1.Completion :=
      AbsoluteValue.completionAlgebra vK w.1 w.2
    letI := localizedCompletionGlobalAlgebra vK w
    letI := localizedCompletionIsScalarTower vK w
    IsAbelianGalois vK.Completion
      (LocalizedCompletion vK w) := by
  let _ := localizedCompletionBaseAlgebra vK w
  let _ := localizedCompletionGlobalAlgebra vK w
  let _ := localizedCompletionIsScalarTower vK w
  let _ : IsGalois vK.Completion
      (LocalizedCompletion vK w) :=
    localizedCompletionIsGalois vK w
  let e :
      absoluteValueDecompositionGroup K w.1 ≃*
        (LocalizedCompletion vK w ≃ₐ[vK.Completion]
          LocalizedCompletion vK w) :=
    decompositionGroupEquivAlgebraicLocalizationAut
      vK hvK w
  exact
    { is_comm.comm := fun σ τ => by
        apply e.symm.injective
        rw [map_mul, map_mul]
        apply Subtype.ext
        exact mul_comm _ _ }

/-- The elements of `L` whose images in the algebraic localization come
from the completed base field are exactly the fixed field of the
decomposition group at `w`. -/
theorem localizedCompletion_baseField_comap_eq_fixedField_decompositionGroup
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK L) :
    letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI : Algebra vK.Completion w.1.Completion :=
      AbsoluteValue.completionAlgebra vK w.1 w.2
    letI := localizedCompletionGlobalAlgebra vK w
    letI := localizedCompletionIsScalarTower vK w
    ((algebraMap vK.Completion
        (LocalizedCompletion vK w)).fieldRange).comap
      (AbsoluteValue.toAlgebraicLocalization vK w.1 w.2) =
        (IntermediateField.fixedField
          (absoluteValueDecompositionGroup K w.1)).toSubfield := by
  let _ := localizedCompletionBaseAlgebra vK w
  let _ := localizedCompletionGlobalAlgebra vK w
  let _ := localizedCompletionIsScalarTower vK w
  let _ : IsGalois vK.Completion
      (LocalizedCompletion vK w) :=
    localizedCompletionIsGalois vK w
  ext x
  change
    AbsoluteValue.toAlgebraicLocalization vK w.1 w.2 x ∈
        Set.range
          (algebraMap vK.Completion
            (LocalizedCompletion vK w)) ↔
      x ∈ IntermediateField.fixedField
        (absoluteValueDecompositionGroup K w.1)
  rw [InfiniteGalois.mem_range_algebraMap_iff_fixed,
    IntermediateField.mem_fixedField_iff]
  constructor
  · intro hfixed σ hσ
    let δ : absoluteValueDecompositionGroup K w.1 := ⟨σ, hσ⟩
    apply
      (AbsoluteValue.toAlgebraicLocalization
        vK w.1 w.2).injective
    calc
      AbsoluteValue.toAlgebraicLocalization
          vK w.1 w.2 (σ x) =
        decompositionGroupEquivAlgebraicLocalizationAut
            vK hvK w δ
          (AbsoluteValue.toAlgebraicLocalization
            vK w.1 w.2 x) :=
        (localizationRamificationGroups_decompositionGroupEquiv_toLocalization
          vK hvK w δ x).symm
      _ = AbsoluteValue.toAlgebraicLocalization
            vK w.1 w.2 x :=
        hfixed _
  · intro hZ τ
    let δ : absoluteValueDecompositionGroup K w.1 :=
      (decompositionGroupEquivAlgebraicLocalizationAut
        vK hvK w).symm τ
    have hδ : ((δ : L ≃ₐ[K] L) x) = x :=
      hZ δ δ.property
    calc
      τ (AbsoluteValue.toAlgebraicLocalization
          vK w.1 w.2 x) =
        decompositionGroupEquivAlgebraicLocalizationAut
            vK hvK w δ
          (AbsoluteValue.toAlgebraicLocalization
            vK w.1 w.2 x) := by
        rw [MulEquiv.apply_symm_apply]
      _ = AbsoluteValue.toAlgebraicLocalization
            vK w.1 w.2 ((δ : L ≃ₐ[K] L) x) :=
        localizationRamificationGroups_decompositionGroupEquiv_toLocalization
          vK hvK w δ x
      _ = AbsoluteValue.toAlgebraicLocalization
            vK w.1 w.2 x :=
        congrArg
          (AbsoluteValue.toAlgebraicLocalization
            vK w.1 w.2) hδ


end LocalClassFieldTheory
