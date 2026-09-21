/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalBlocks.Induced
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.Completion.TensorProductDecomposition
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.HilbertRamification.AlgebraicLocalization
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.HilbertRamification.AbsoluteValueConjugacy
import Mathlib.Algebra.Group.Pi.Units
/-!
# The tensor-product realization of a local induced block

This file connects the induced module in `LocalBlock` with the actual local
factor of the scalar-extended adele algebra.  The natural Galois action on
`K_v ⊗[K] L` is conjugation on the second tensor factor. The completion tensor-product theorem
identifies this algebra with the product of the completions above `v`.

The first part records the natural tensor action and the canonical
identifications between completions at conjugate absolute values.  These
identifications are the concrete source of the induced-module covariance in
the induced local-block calculation.
-/

open scoped TensorProduct

noncomputable section

namespace LocalClassFieldTheory

open AlgebraicNumberTheory.Valuations
open HilbertRamification
open CyclicCohomology

universe u v

variable {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    [IsGalois K L]

/-- The local tensor algebra occurring as the factor of
`𝔸_K ⊗[K] L` at `v`. -/
abbrev LocalTensorAlgebra (vK : AbsoluteValue K ℝ) :=
  vK.Completion ⊗[K] L

/-- Galois conjugation on the second factor of the local tensor algebra. -/
noncomputable def localTensorConjugation
    (vK : AbsoluteValue K ℝ) (σ : L ≃ₐ[K] L) :
    LocalTensorAlgebra (L := L) vK ≃ₐ[vK.Completion]
      LocalTensorAlgebra (L := L) vK := by
  let f :
      LocalTensorAlgebra (L := L) vK →ₐ[vK.Completion]
        LocalTensorAlgebra (L := L) vK :=
    Algebra.TensorProduct.map
      (AlgHom.id vK.Completion vK.Completion) σ.toAlgHom
  let g :
      LocalTensorAlgebra (L := L) vK →ₐ[vK.Completion]
        LocalTensorAlgebra (L := L) vK :=
    Algebra.TensorProduct.map
      (AlgHom.id vK.Completion vK.Completion) σ.symm.toAlgHom
  exact AlgEquiv.ofAlgHom f g
    (by ext x; simp [f, g])
    (by ext x; simp [f, g])

omit [FiniteDimensional K L] [IsGalois K L] in
@[simp]
theorem localTensorConjugation_tmul
    (vK : AbsoluteValue K ℝ) (σ : L ≃ₐ[K] L)
    (b : vK.Completion) (x : L) :
    localTensorConjugation vK σ (b ⊗ₜ[K] x) =
      b ⊗ₜ[K] σ x :=
  rfl

omit [FiniteDimensional K L] [IsGalois K L] in
theorem localTensorConjugation_one
    (vK : AbsoluteValue K ℝ)
    (z : LocalTensorAlgebra (L := L) vK) :
    localTensorConjugation vK (1 : L ≃ₐ[K] L) z = z := by
  induction z using TensorProduct.inductionOn with
  | tmul b x => simp
  | add x y hx hy => simp [hx, hy]

omit [FiniteDimensional K L] [IsGalois K L] in
theorem localTensorConjugation_mul
    (vK : AbsoluteValue K ℝ) (σ τ : L ≃ₐ[K] L)
    (z : LocalTensorAlgebra (L := L) vK) :
    localTensorConjugation vK (σ * τ) z =
      localTensorConjugation vK σ
        (localTensorConjugation vK τ z) := by
  induction z using TensorProduct.inductionOn with
  | tmul b x => simp
  | add x y hx hy => simp [hx, hy]

/-- The natural Galois action on the unit group of the local tensor
algebra. -/
@[reducible]
noncomputable def localTensorUnitsAction
    (vK : AbsoluteValue K ℝ) :
    MulDistribMulAction
      (L ≃ₐ[K] L) (LocalTensorAlgebra (L := L) vK)ˣ where
  smul σ z :=
    Units.mapEquiv (localTensorConjugation vK σ).toMulEquiv z
  one_smul z := by
    apply Units.ext
    exact localTensorConjugation_one vK
      (z : LocalTensorAlgebra (L := L) vK)
  mul_smul σ τ z := by
    apply Units.ext
    exact localTensorConjugation_mul vK σ τ
      (z : LocalTensorAlgebra (L := L) vK)
  smul_mul σ x y := by
    apply Units.ext
    exact (localTensorConjugation vK σ).map_mul
      (x : LocalTensorAlgebra (L := L) vK)
      (y : LocalTensorAlgebra (L := L) vK)
  smul_one σ := by
    apply Units.ext
    exact (localTensorConjugation vK σ).map_one

omit [FiniteDimensional K L] [IsGalois K L] in
@[simp]
theorem localTensorUnitsAction_smul_coe
    (vK : AbsoluteValue K ℝ) (σ : L ≃ₐ[K] L)
    (z : (LocalTensorAlgebra (L := L) vK)ˣ) :
    letI := localTensorUnitsAction (K := K) (L := L) vK
    ((σ • z : (LocalTensorAlgebra (L := L) vK)ˣ) :
        LocalTensorAlgebra (L := L) vK) =
      localTensorConjugation vK σ
        (z : LocalTensorAlgebra (L := L) vK) :=
  rfl

/-- The isometric ring equivalence from the normed copy attached to
`w ∘ σ` to the normed copy attached to `w`. -/
noncomputable def conjugateWithAbsRingEquiv
    (w : AbsoluteValue L ℝ) (σ : L ≃ₐ[K] L) :
    WithAbs (absoluteValueConjugate w σ) ≃+* WithAbs w :=
  WithAbs.congr
    (absoluteValueConjugate w σ) w σ.toRingEquiv

omit [FiniteDimensional K L] [IsGalois K L] in
theorem conjugateWithAbsRingEquiv_isometry
    (w : AbsoluteValue L ℝ) (σ : L ≃ₐ[K] L) :
    Isometry (conjugateWithAbsRingEquiv w σ) := by
  apply AddMonoidHomClass.isometry_of_norm
  intro x
  rw [WithAbs.norm_eq_apply_ofAbs, WithAbs.norm_eq_apply_ofAbs]
  rfl

omit [FiniteDimensional K L] [IsGalois K L] in
theorem conjugateWithAbsRingEquiv_symm_isometry
    (w : AbsoluteValue L ℝ) (σ : L ≃ₐ[K] L) :
    Isometry (conjugateWithAbsRingEquiv w σ).symm := by
  apply AddMonoidHomClass.isometry_of_norm
  intro x
  rw [WithAbs.norm_eq_apply_ofAbs, WithAbs.norm_eq_apply_ofAbs]
  change w (σ (σ⁻¹ x.ofAbs)) = w x.ofAbs
  exact congrArg w (σ.apply_symm_apply x.ofAbs)

/-- The canonical equivalence between the completions at `w ∘ σ` and
`w`, induced by `σ : L → L`. -/
noncomputable def conjugateCompletionRingEquiv
    (w : AbsoluteValue L ℝ) (σ : L ≃ₐ[K] L) :
    (absoluteValueConjugate w σ).Completion ≃+*
      w.Completion :=
  UniformSpace.Completion.mapRingEquiv
    (conjugateWithAbsRingEquiv w σ)
    (conjugateWithAbsRingEquiv_isometry w σ).continuous
    (conjugateWithAbsRingEquiv_symm_isometry w σ).continuous

omit [FiniteDimensional K L] [IsGalois K L] in
@[simp]
theorem conjugateCompletionRingEquiv_toCompletion
    (w : AbsoluteValue L ℝ) (σ : L ≃ₐ[K] L) (x : L) :
    conjugateCompletionRingEquiv w σ
        (AbsoluteValue.toCompletion
          (absoluteValueConjugate w σ) x) =
      AbsoluteValue.toCompletion w (σ x) := by
  change
    UniformSpace.Completion.mapRingEquiv
        (conjugateWithAbsRingEquiv w σ)
        (conjugateWithAbsRingEquiv_isometry w σ).continuous
        (conjugateWithAbsRingEquiv_symm_isometry w σ).continuous
      (((WithAbs.equiv
        (absoluteValueConjugate w σ)).symm x :
          WithAbs (absoluteValueConjugate w σ)) :
        (absoluteValueConjugate w σ).Completion) = _
  rw [UniformSpace.Completion.mapRingEquiv_apply,
    UniformSpace.Completion.map_coe
      (conjugateWithAbsRingEquiv_isometry w σ).uniformContinuous]
  rfl

omit [FiniteDimensional K L] [IsGalois K L] in
/-- Conjugation fixes the embedded completed base field. -/
theorem conjugateCompletionRingEquiv_completionMap
    (vK : AbsoluteValue K ℝ)
    (w : AbsoluteValueExtension vK L)
    (σ : L ≃ₐ[K] L) (b : vK.Completion) :
    conjugateCompletionRingEquiv w.1 σ
        (AbsoluteValue.completionMap vK
          (absoluteValueConjugate w.1 σ)
          (absoluteValueConjugate_extends vK w σ) b) =
      AbsoluteValue.completionMap vK w.1 w.2 b := by
  refine UniformSpace.Completion.ext'
    (UniformSpace.Completion.continuous_map.comp
      (AbsoluteValue.completionMap_isometry
        vK
        (absoluteValueConjugate w.1 σ)
        (absoluteValueConjugate_extends vK w σ)).continuous)
    (AbsoluteValue.completionMap_isometry
      vK w.1 w.2).continuous ?_ b
  intro x
  have hx : (x : vK.Completion) =
      algebraMap K vK.Completion (WithAbs.equiv vK x) := by
    rw [← AbsoluteValue.toCompletion_eq_algebraMap]
    simp
  rw [hx]
  simp only [Function.comp_apply]
  rw [AbsoluteValue.completionMap_coe,
    AbsoluteValue.completionMap_coe]
  change
    conjugateCompletionRingEquiv w.1 σ
        (AbsoluteValue.toCompletion
          (absoluteValueConjugate w.1 σ)
          (algebraMap K L (WithAbs.equiv vK x))) =
      AbsoluteValue.toCompletion w.1
        (algebraMap K L (WithAbs.equiv vK x))
  rw [conjugateCompletionRingEquiv_toCompletion, σ.commutes]

omit [FiniteDimensional K L] [IsGalois K L] in
theorem conjugateCompletionRingEquiv_algebraMap
    (vK : AbsoluteValue K ℝ)
    (w : AbsoluteValueExtension vK L)
    (σ : L ≃ₐ[K] L) (b : vK.Completion) :
    letI :
        Algebra vK.Completion
          (absoluteValueConjugate w.1 σ).Completion :=
      AbsoluteValue.completionAlgebra vK
        (absoluteValueConjugate w.1 σ)
        (absoluteValueConjugate_extends vK w σ)
    letI : Algebra vK.Completion w.1.Completion :=
      AbsoluteValue.completionAlgebra vK w.1 w.2
    conjugateCompletionRingEquiv w.1 σ
        (algebraMap vK.Completion
          (absoluteValueConjugate w.1 σ).Completion b) =
      algebraMap vK.Completion w.1.Completion b :=
  conjugateCompletionRingEquiv_completionMap vK w σ b

/-- The conjugate-completion equivalence with its source indexed by the
corresponding element of `AbsoluteValueExtension`.  This wrapper keeps
dependent product components definitionally aligned. -/
noncomputable def conjugateExtensionCompletionRingEquiv
    (vK : AbsoluteValue K ℝ)
    (w : AbsoluteValueExtension vK L)
    (σ : L ≃ₐ[K] L) :
    (absoluteValueExtensionConjugate vK w σ).1.Completion ≃+*
      w.1.Completion := by
  change
    (absoluteValueConjugate w.1 σ).Completion ≃+*
      w.1.Completion
  exact conjugateCompletionRingEquiv w.1 σ

omit [FiniteDimensional K L] [IsGalois K L] in
@[simp]
theorem conjugateExtensionCompletionRingEquiv_toCompletion
    (vK : AbsoluteValue K ℝ)
    (w : AbsoluteValueExtension vK L)
    (σ : L ≃ₐ[K] L) (x : L) :
    conjugateExtensionCompletionRingEquiv vK w σ
        (AbsoluteValue.toCompletion
          (absoluteValueExtensionConjugate vK w σ).1 x) =
      AbsoluteValue.toCompletion w.1 (σ x) := by
  change
    conjugateCompletionRingEquiv w.1 σ
        (AbsoluteValue.toCompletion
          (absoluteValueConjugate w.1 σ) x) =
      AbsoluteValue.toCompletion w.1 (σ x)
  exact conjugateCompletionRingEquiv_toCompletion w.1 σ x

omit [FiniteDimensional K L] [IsGalois K L] in
theorem conjugateExtensionCompletionRingEquiv_algebraMap
    (vK : AbsoluteValue K ℝ)
    (w : AbsoluteValueExtension vK L)
    (σ : L ≃ₐ[K] L) (b : vK.Completion) :
    letI :
        Algebra vK.Completion
          (absoluteValueExtensionConjugate vK w σ).1.Completion :=
      AbsoluteValue.completionAlgebra vK
        (absoluteValueExtensionConjugate vK w σ).1
        (absoluteValueExtensionConjugate vK w σ).2
    letI : Algebra vK.Completion w.1.Completion :=
      AbsoluteValue.completionAlgebra vK w.1 w.2
    conjugateExtensionCompletionRingEquiv vK w σ
        (algebraMap vK.Completion
          (absoluteValueExtensionConjugate vK w σ).1.Completion b) =
      algebraMap vK.Completion w.1.Completion b := by
  let _ :
      Algebra vK.Completion
        (absoluteValueConjugate w.1 σ).Completion :=
    AbsoluteValue.completionAlgebra vK
      (absoluteValueConjugate w.1 σ)
      (absoluteValueConjugate_extends vK w σ)
  let _ : Algebra vK.Completion w.1.Completion :=
    AbsoluteValue.completionAlgebra vK w.1 w.2
  change
    conjugateCompletionRingEquiv w.1 σ
        (algebraMap vK.Completion
          (absoluteValueConjugate w.1 σ).Completion b) =
      algebraMap vK.Completion w.1.Completion b
  exact conjugateCompletionRingEquiv_algebraMap vK w σ b

/-- Evaluation of the local tensor algebra in the chosen completion,
with codomain written in the algebraic-localization model used by
`LocalPlaceBlock`. -/
noncomputable def localTensorEvaluation
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK L) :
    letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI := AbsoluteValue.completionAlgebra vK w.1 w.2
    LocalTensorAlgebra (L := L) vK →ₐ[vK.Completion]
      LocalizedCompletion vK w := by
  letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  letI : SMul K w.1.Completion := hK.toSMul
  letI := AbsoluteValue.completionAlgebra vK w.1 w.2
  exact
    (localizedCompletionEquivCompletion vK hvK w).symm.toAlgHom.comp
      (absoluteValueExtension_localizationTensorHom vK w)

omit [IsGalois K L] in
@[simp]
theorem localTensorEvaluation_tmul
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK L)
    (b : vK.Completion) (x : L) :
    letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI := AbsoluteValue.completionAlgebra vK w.1 w.2
    localTensorEvaluation vK hvK w (b ⊗ₜ[K] x) =
      algebraMap vK.Completion (LocalizedCompletion vK w) b *
        AbsoluteValue.toAlgebraicLocalization
          vK w.1 w.2 x := by
  let hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  let _ : SMul K w.1.Completion := hK.toSMul
  let _ := AbsoluteValue.completionAlgebra vK w.1 w.2
  apply (localizedCompletionEquivCompletion vK hvK w).injective
  rw [map_mul]
  simp only [localTensorEvaluation, AlgHom.coe_comp, Function.comp_apply,
    absoluteValueExtension_localizationTensorHom_tmul]
  rfl

/-- Evaluation at the chosen extension is covariant for left
multiplication by the decomposition group.  This is the defining
covariance relation of the induced module, obtained directly from
the localization Galois-group equivalence. -/
theorem localTensorEvaluation_conjugation_decomposition
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK L)
    (h : absoluteValueDecompositionGroup K w.1)
    (g : L ≃ₐ[K] L)
    (z : LocalTensorAlgebra (L := L) vK) :
    letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI := AbsoluteValue.completionAlgebra vK w.1 w.2
    localTensorEvaluation vK hvK w
        (localTensorConjugation vK (h.1 * g) z) =
      decompositionGroupEquivAlgebraicLocalizationAut
        vK hvK w h
        (localTensorEvaluation vK hvK w
          (localTensorConjugation vK g z)) := by
  let hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  let _ : SMul K w.1.Completion := hK.toSMul
  let _ := AbsoluteValue.completionAlgebra vK w.1 w.2
  induction z using TensorProduct.inductionOn with
  | add x y hx hy =>
      simpa only [map_add] using congrArg₂ (· + ·) hx hy
  | tmul b x =>
      rw [localTensorConjugation_tmul,
        localTensorConjugation_tmul,
        localTensorEvaluation_tmul,
        localTensorEvaluation_tmul,
        map_mul,
        (decompositionGroupEquivAlgebraicLocalizationAut
          vK hvK w h).commutes,
        localizationRamificationGroups_decompositionGroupEquiv_toLocalization]
      rfl

/-- The canonical orbit-evaluation map from local tensor units to the
induced local block.  Its covariance is exactly
`localTensorEvaluation_conjugation_decomposition`. -/
noncomputable def localTensorOrbitHom
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK L) :
    letI :=
      decompositionGroupLocalUnitsAction vK hvK w
    letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI := AbsoluteValue.completionAlgebra vK w.1 w.2
    (LocalTensorAlgebra (L := L) vK)ˣ →*
      LocalPlaceBlock vK hvK w := by
  letI :=
    decompositionGroupLocalUnitsAction vK hvK w
  letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  letI : SMul K w.1.Completion := hK.toSMul
  letI := AbsoluteValue.completionAlgebra vK w.1 w.2
  exact
    { toFun := fun z =>
        ⟨fun g =>
          Units.map
            (localTensorEvaluation vK hvK w).toMonoidHom
            (Units.map
              (localTensorConjugation vK g).toMonoidHom z),
          by
            intro h g
            apply Units.ext
            change
              localTensorEvaluation vK hvK w
                    (localTensorConjugation vK (h.1 * g)
                      (z : LocalTensorAlgebra (L := L) vK)) =
                decompositionGroupEquivAlgebraicLocalizationAut
                  vK hvK w h
                  (localTensorEvaluation vK hvK w
                    (localTensorConjugation vK g
                      (z : LocalTensorAlgebra (L := L) vK)))
            exact
              localTensorEvaluation_conjugation_decomposition
                vK hvK w h g z⟩
      map_one' := by
        apply Subtype.ext
        funext g
        apply Units.ext
        simp
      map_mul' := by
        intro x y
        apply Subtype.ext
        funext g
        apply Units.ext
        simp }

/-- Orbit evaluation intertwines natural conjugation on the tensor
factor with right translation on the induced module. -/
theorem localTensorOrbitHom_smul
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK L)
    (τ : L ≃ₐ[K] L)
    (z : (LocalTensorAlgebra (L := L) vK)ˣ) :
    letI :=
      decompositionGroupLocalUnitsAction vK hvK w
    letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI := AbsoluteValue.completionAlgebra vK w.1 w.2
    letI := localTensorUnitsAction (K := K) (L := L) vK
    localTensorOrbitHom vK hvK w (τ • z) =
      τ • localTensorOrbitHom vK hvK w z := by
  let _ :=
    decompositionGroupLocalUnitsAction vK hvK w
  let hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  let _ : SMul K w.1.Completion := hK.toSMul
  let _ := AbsoluteValue.completionAlgebra vK w.1 w.2
  let _ := localTensorUnitsAction (K := K) (L := L) vK
  apply Subtype.ext
  funext g
  apply Units.ext
  change
    localTensorEvaluation vK hvK w
        (localTensorConjugation vK g
          (localTensorConjugation vK τ
            (z : LocalTensorAlgebra (L := L) vK))) =
      localTensorEvaluation vK hvK w
        (localTensorConjugation vK (g * τ)
          (z : LocalTensorAlgebra (L := L) vK))
  rw [localTensorConjugation_mul]

/-- After transporting the completion at `w ∘ g` back to the chosen
completion at `w`, the corresponding component of the tensor-product decomposition is
evaluation of the `g`-conjugate tensor. -/
theorem conjugateExtensionCompletionRingEquiv_completionTensorDecomposition_left
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK L)
    (g : L ≃ₐ[K] L)
    (z : LocalTensorAlgebra (L := L) vK) :
    letI : ∀ w' : AbsoluteValueExtension vK L,
        Algebra vK.Completion w'.1.Completion :=
      fun w' ↦ AbsoluteValue.completionAlgebra vK w'.1 w'.2
    conjugateExtensionCompletionRingEquiv vK w g
        (completionTensorDecomposition_left (K := K) (L := L) vK hvK z
          (absoluteValueExtensionConjugate vK w g)) =
      absoluteValueExtension_localizationTensorHom vK w
        (localTensorConjugation vK g z) := by
  let _ : ∀ w' : AbsoluteValueExtension vK L,
      Algebra vK.Completion w'.1.Completion :=
    fun w' ↦ AbsoluteValue.completionAlgebra vK w'.1 w'.2
  induction z using TensorProduct.inductionOn with
  | add x y hx hy =>
      simpa only [map_add, Pi.add_apply] using
        congrArg₂ (· + ·) hx hy
  | tmul b x =>
      rw [completionTensorDecomposition_left_tmul_apply,
        map_mul,
        conjugateExtensionCompletionRingEquiv_algebraMap]
      change
        algebraMap vK.Completion w.1.Completion b *
            conjugateExtensionCompletionRingEquiv vK w g
              (AbsoluteValue.toCompletion
                (absoluteValueExtensionConjugate vK w g).1 x) =
          absoluteValueExtension_localizationTensorHom vK w
            (localTensorConjugation vK g (b ⊗ₜ[K] x))
      rw [conjugateExtensionCompletionRingEquiv_toCompletion,
        localTensorConjugation_tmul,
        absoluteValueExtension_localizationTensorHom_tmul]
      change
        algebraMap vK.Completion w.1.Completion b *
            AbsoluteValue.toCompletion w.1 (g x) =
          algebraMap vK.Completion w.1.Completion b *
            AbsoluteValue.toCompletion w.1 (g x)
      rfl

section RightCosetCoordinates

universe uG uB

variable {G : Type uG} {B : Type uB}
    [Group G] [CommGroup B]
    (H : Subgroup G) [MulDistribMulAction H B]

/-- Right cosets `H \ G`, appropriate for the convention
`f (h * g) = h • f g` used by `InducedModule`. -/
abbrev InducedRightCosets :=
  Quotient (QuotientGroup.rightRel H)

/-- The element carrying the chosen representative of the right coset of
`g` to `g`. -/
noncomputable def rightCosetCoefficient (g : G) : H := by
  let q : InducedRightCosets H := Quotient.mk'' g
  refine ⟨g * (Quotient.out q)⁻¹, ?_⟩
  exact QuotientGroup.rightRel_apply.mp
    (Quotient.exact' (Quotient.out_eq' q))

@[simp]
theorem rightCosetCoefficient_mul_out (g : G) :
    (rightCosetCoefficient H g : G) *
        Quotient.out (Quotient.mk'' g :
          InducedRightCosets H) = g := by
  simp [rightCosetCoefficient]

theorem rightCoset_mk_mul_left
    (h : H) (g : G) :
    (Quotient.mk'' (h.1 * g) : InducedRightCosets H) =
      Quotient.mk'' g := by
  apply Quotient.sound'
  rw [QuotientGroup.rightRel_apply]
  simpa only [mul_inv_rev, mul_assoc, mul_inv_cancel_left,
    one_mul] using H.inv_mem h.2

theorem rightCosetCoefficient_mul_left
    (h : H) (g : G) :
    rightCosetCoefficient H (h.1 * g) =
      h * rightCosetCoefficient H g := by
  apply Subtype.ext
  simp only [rightCosetCoefficient, Subgroup.coe_mul]
  rw [rightCoset_mk_mul_left H h g]
  simp only [mul_assoc]

/-- Restriction to one representative of each right coset identifies an
induced module with a product indexed by `H \ G`.  No commutativity or
cyclicity assumption on `G` is used. -/
noncomputable def inducedRightCosetCoordinates :
    InducedModule (B := B) H ≃*
      (InducedRightCosets H → B) where
  toFun f q := f.1 (Quotient.out q)
  invFun b := ⟨fun g =>
      rightCosetCoefficient H g •
        b (Quotient.mk'' g), by
    intro h g
    change
      rightCosetCoefficient H (h.1 * g) •
          b (Quotient.mk'' (h.1 * g)) =
        h •
          (rightCosetCoefficient H g •
            b (Quotient.mk'' g))
    rw [rightCosetCoefficient_mul_left H h g,
      rightCoset_mk_mul_left H h g, mul_smul]⟩
  left_inv f := by
    apply Subtype.ext
    funext g
    change
      rightCosetCoefficient H g •
          f.1 (Quotient.out
            (Quotient.mk'' g : InducedRightCosets H)) =
        f.1 g
    calc
      rightCosetCoefficient H g •
          f.1 (Quotient.out
            (Quotient.mk'' g : InducedRightCosets H)) =
          f.1 ((rightCosetCoefficient H g : G) *
            Quotient.out
              (Quotient.mk'' g : InducedRightCosets H)) :=
        (f.2 (rightCosetCoefficient H g)
          (Quotient.out
            (Quotient.mk'' g : InducedRightCosets H))).symm
      _ = f.1 g := congrArg f.1
        (rightCosetCoefficient_mul_out H g)
  right_inv b := by
    funext q
    change
      rightCosetCoefficient H (Quotient.out q) •
          b (Quotient.mk'' (Quotient.out q)) =
        b q
    have hq :
        (Quotient.mk'' (Quotient.out q) :
          InducedRightCosets H) = q :=
      Quotient.out_eq' q
    rw [hq]
    have hc :
        rightCosetCoefficient H (Quotient.out q) = 1 := by
      apply Subtype.ext
      simp [rightCosetCoefficient, hq]
    rw [hc, one_smul]
  map_mul' f g := by
    funext q
    rfl

@[simp]
theorem inducedRightCosetCoordinates_apply
    (f : InducedModule (B := B) H)
    (q : InducedRightCosets H) :
    inducedRightCosetCoordinates H f q =
      f.1 (Quotient.out q) :=
  rfl

end RightCosetCoordinates

section ExtensionOrbit

variable (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK L)

local notation "G" => L ≃ₐ[K] L

/-- The chosen representative of a right coset sends `w` to a well-defined
extension above `v`. -/
noncomputable def rightCosetExtension
    (q : InducedRightCosets
      (absoluteValueDecompositionGroup K w.1)) :
    AbsoluteValueExtension vK L :=
  absoluteValueExtensionConjugate vK w (Quotient.out q)

omit [FiniteDimensional K L] [IsGalois K L] in
include hvK in
theorem rightCosetExtension_eq_of_mk
    (g : G) :
    rightCosetExtension vK w
        (Quotient.mk'' g : InducedRightCosets
          (absoluteValueDecompositionGroup K w.1)) =
      absoluteValueExtensionConjugate vK w g := by
  let q : InducedRightCosets
      (absoluteValueDecompositionGroup K w.1) := Quotient.mk'' g
  let h : absoluteValueDecompositionGroup K w.1 :=
    rightCosetCoefficient (absoluteValueDecompositionGroup K w.1) g
  have hfix :
      absoluteValueExtensionConjugate vK w h.1 = w :=
    (mem_absoluteValueDecompositionGroup_iff_extensionConjugate_eq
      vK hvK w h.1).mp h.2
  have hg :
      h.1 * Quotient.out q = g :=
    rightCosetCoefficient_mul_out
      (absoluteValueDecompositionGroup K w.1) g
  apply Subtype.ext
  ext x
  change w.1 (Quotient.out q x) = w.1 (g x)
  rw [← hg]
  change w.1 (Quotient.out q x) =
    w.1 (h.1 (Quotient.out q x))
  have hp :
      w.1 (h.1 (Quotient.out q x)) =
        w.1 (Quotient.out q x) := by
    have hp' := congrArg
      (fun z : AbsoluteValueExtension vK L =>
        z.1 (Quotient.out q x)) hfix
    change
      w.1 (h.1 (Quotient.out q x)) =
        w.1 (Quotient.out q x) at hp'
    exact hp'
  exact hp.symm

/-- Transitivity of extensions, sharpened to the orbit equivalence
`H \ G ≃ {w' | w' ∣ v}`. -/
noncomputable def rightCosetExtensionEquiv :
    InducedRightCosets (absoluteValueDecompositionGroup K w.1) ≃
      AbsoluteValueExtension vK L := by
  apply Equiv.ofBijective (rightCosetExtension vK w)
  constructor
  · intro q r hqr
    have hmem :
        Quotient.out r * (Quotient.out q)⁻¹ ∈
          absoluteValueDecompositionGroup K w.1 := by
      rw [mem_absoluteValueDecompositionGroup_iff_extensionConjugate_eq
        vK hvK w]
      apply Subtype.ext
      ext x
      change
        w.1 (Quotient.out r ((Quotient.out q)⁻¹ x)) =
          w.1 x
      have hp :
          w.1 (Quotient.out q ((Quotient.out q)⁻¹ x)) =
            w.1 (Quotient.out r ((Quotient.out q)⁻¹ x)) := by
        have hp' := congrArg
          (fun z : AbsoluteValueExtension vK L =>
            z.1 ((Quotient.out q)⁻¹ x)) hqr
        change
          w.1 (Quotient.out q ((Quotient.out q)⁻¹ x)) =
            w.1 (Quotient.out r ((Quotient.out q)⁻¹ x))
          at hp'
        exact hp'
      simpa using hp.symm
    have hout :
        (Quotient.mk'' (Quotient.out q) :
          InducedRightCosets
            (absoluteValueDecompositionGroup K w.1)) =
          Quotient.mk'' (Quotient.out r) := by
      apply Quotient.sound'
      exact QuotientGroup.rightRel_apply.mpr hmem
    calc
      q = Quotient.mk'' (Quotient.out q) :=
        (Quotient.out_eq' q).symm
      _ = Quotient.mk'' (Quotient.out r) := hout
      _ = r := Quotient.out_eq' r
  · intro w'
    obtain ⟨g, hg⟩ := absoluteValueConjugacy vK hvK w w'
    refine ⟨Quotient.mk'' g, ?_⟩
    exact (rightCosetExtension_eq_of_mk vK hvK w g).trans hg.symm

omit [FiniteDimensional K L] in
@[simp]
theorem rightCosetExtensionEquiv_apply
    (q : InducedRightCosets
      (absoluteValueDecompositionGroup K w.1)) :
    rightCosetExtensionEquiv vK hvK w q =
      absoluteValueExtensionConjugate
        vK w (Quotient.out q) :=
  rfl

end ExtensionOrbit

section ProductEquivalences

variable (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK L)

/-- Reindex the product of all completion unit groups by the right cosets
of the decomposition group. -/
noncomputable def completionProductReindexRightCosets :
    (∀ w' : AbsoluteValueExtension vK L, w'.1.Completionˣ) ≃*
      (∀ q : InducedRightCosets
          (absoluteValueDecompositionGroup K w.1),
        ((rightCosetExtensionEquiv vK hvK w q).1.Completion)ˣ) := by
  let e :=
    Equiv.piCongrLeft'
      (fun w' : AbsoluteValueExtension vK L =>
        w'.1.Completionˣ)
      (rightCosetExtensionEquiv vK hvK w).symm
  exact
    { e with
      map_mul' := by
        intro x y
        funext q
        rfl }

/-- For a right coset, conjugation by its chosen representative identifies
the corresponding completion with the fixed completion at `w`. -/
noncomputable def rightCosetCompletionUnitsEquiv
    (q : InducedRightCosets
      (absoluteValueDecompositionGroup K w.1)) :
    ((rightCosetExtensionEquiv vK hvK w q).1.Completion)ˣ ≃*
      w.1.Completionˣ := by
  exact Units.mapEquiv
    (conjugateExtensionCompletionRingEquiv
      vK w (Quotient.out q)).toMulEquiv

omit [FiniteDimensional K L] in
@[simp]
theorem rightCosetCompletionUnitsEquiv_apply_coe
    (q : InducedRightCosets
      (absoluteValueDecompositionGroup K w.1))
    (z :
      ((rightCosetExtensionEquiv vK hvK w q).1.Completion)ˣ) :
    ((rightCosetCompletionUnitsEquiv vK hvK w q z :
        w.1.Completionˣ) : w.1.Completion) =
      conjugateExtensionCompletionRingEquiv
        vK w (Quotient.out q)
        (z :
          (rightCosetExtensionEquiv vK hvK w q).1.Completion) :=
  rfl

/-- The product supplied by the completion tensor-product decomposition, rewritten as one copy of the
chosen local multiplicative group for every right coset. -/
noncomputable def completionProductUnitsEquivRightCosets :
    letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI := AbsoluteValue.completionAlgebra vK w.1 w.2
    (∀ w' : AbsoluteValueExtension vK L, w'.1.Completionˣ) ≃*
      (InducedRightCosets
          (absoluteValueDecompositionGroup K w.1) →
        (LocalizedCompletion vK w)ˣ) := by
  letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  letI : SMul K w.1.Completion := hK.toSMul
  letI := AbsoluteValue.completionAlgebra vK w.1 w.2
  exact
    (completionProductReindexRightCosets vK hvK w).trans
      ((MulEquiv.piCongrRight fun q : InducedRightCosets
          (absoluteValueDecompositionGroup K w.1) =>
        rightCosetCompletionUnitsEquiv vK hvK w q).trans
        (MulEquiv.piCongrRight fun _ : InducedRightCosets
            (absoluteValueDecompositionGroup K w.1) =>
          (Units.mapEquiv
            (localizedCompletionEquivCompletion
              vK hvK w).toMulEquiv).symm))

@[simp]
theorem completionProductUnitsEquivRightCosets_apply_coe
    (p : ∀ w' : AbsoluteValueExtension vK L,
      w'.1.Completionˣ)
    (q : InducedRightCosets
      (absoluteValueDecompositionGroup K w.1)) :
    letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI := AbsoluteValue.completionAlgebra vK w.1 w.2
    ((completionProductUnitsEquivRightCosets vK hvK w p q :
        (LocalizedCompletion vK w)ˣ) :
      LocalizedCompletion vK w) =
      (localizedCompletionEquivCompletion vK hvK w).symm
        (conjugateExtensionCompletionRingEquiv
          vK w (Quotient.out q)
          ((p (rightCosetExtensionEquiv vK hvK w q) :
              (rightCosetExtensionEquiv vK hvK w q).1.Completionˣ) :
            (rightCosetExtensionEquiv vK hvK w q).1.Completion)) := by
  rfl

/-- The product of completions above `v` is the induced block from the
decomposition group.  This form is valid for an arbitrary finite Galois
extension; the decomposition group need not be normal. -/
noncomputable def completionProductUnitsEquivLocalPlaceBlock :
    letI :=
      decompositionGroupLocalUnitsAction vK hvK w
    letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI := AbsoluteValue.completionAlgebra vK w.1 w.2
    (∀ w' : AbsoluteValueExtension vK L, w'.1.Completionˣ) ≃*
      LocalPlaceBlock vK hvK w := by
  letI :=
    decompositionGroupLocalUnitsAction vK hvK w
  letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  letI : SMul K w.1.Completion := hK.toSMul
  letI := AbsoluteValue.completionAlgebra vK w.1 w.2
  exact
    (completionProductUnitsEquivRightCosets vK hvK w).trans
      (inducedRightCosetCoordinates
        (absoluteValueDecompositionGroup K w.1)).symm

/-- Concrete tensor realization of the induced local block: the actual local unit group
`(K_v ⊗[K] L)ˣ` is multiplicatively equivalent to the induced block from
the decomposition group at a chosen extension `w`. -/
noncomputable def localTensorUnitsEquivLocalPlaceBlock :
    letI :=
      decompositionGroupLocalUnitsAction vK hvK w
    letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI := AbsoluteValue.completionAlgebra vK w.1 w.2
    letI : ∀ w' : AbsoluteValueExtension vK L,
        Algebra vK.Completion w'.1.Completion :=
      fun w' ↦ AbsoluteValue.completionAlgebra vK w'.1 w'.2
    (LocalTensorAlgebra (L := L) vK)ˣ ≃*
      LocalPlaceBlock vK hvK w := by
  letI :=
    decompositionGroupLocalUnitsAction vK hvK w
  letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  letI : SMul K w.1.Completion := hK.toSMul
  letI := AbsoluteValue.completionAlgebra vK w.1 w.2
  letI : ∀ w' : AbsoluteValueExtension vK L,
      Algebra vK.Completion w'.1.Completion :=
    fun w' ↦ AbsoluteValue.completionAlgebra vK w'.1 w'.2
  exact
    (localTensorUnitsEquivCompletionProduct vK hvK).trans
      (completionProductUnitsEquivLocalPlaceBlock vK hvK w)

/-- On the chosen representative of a right coset, the concrete
The tensor-product equivalence is the canonical orbit-evaluation map. -/
theorem localTensorUnitsEquivLocalPlaceBlock_apply_out_coe
    (z : (LocalTensorAlgebra (L := L) vK)ˣ)
    (q : InducedRightCosets
      (absoluteValueDecompositionGroup K w.1)) :
    letI :=
      decompositionGroupLocalUnitsAction vK hvK w
    letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI := AbsoluteValue.completionAlgebra vK w.1 w.2
    letI : ∀ w' : AbsoluteValueExtension vK L,
        Algebra vK.Completion w'.1.Completion :=
      fun w' ↦ AbsoluteValue.completionAlgebra vK w'.1 w'.2
    (((localTensorUnitsEquivLocalPlaceBlock vK hvK w z).1
        (Quotient.out q) :
          (LocalizedCompletion vK w)ˣ) :
      LocalizedCompletion vK w) =
      localTensorEvaluation vK hvK w
        (localTensorConjugation vK (Quotient.out q)
          (z : LocalTensorAlgebra (L := L) vK)) := by
  let _ :=
    decompositionGroupLocalUnitsAction vK hvK w
  let hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  let _ : SMul K w.1.Completion := hK.toSMul
  let _ := AbsoluteValue.completionAlgebra vK w.1 w.2
  let _ : ∀ w' : AbsoluteValueExtension vK L,
      Algebra vK.Completion w'.1.Completion :=
    fun w' ↦ AbsoluteValue.completionAlgebra vK w'.1 w'.2
  have hcoord :
      inducedRightCosetCoordinates
          (absoluteValueDecompositionGroup K w.1)
          (localTensorUnitsEquivLocalPlaceBlock vK hvK w z) q =
        completionProductUnitsEquivRightCosets vK hvK w
          (localTensorUnitsEquivCompletionProduct vK hvK z) q := by
    change
      inducedRightCosetCoordinates
          (absoluteValueDecompositionGroup K w.1)
          ((inducedRightCosetCoordinates
            (absoluteValueDecompositionGroup K w.1)).symm
            (completionProductUnitsEquivRightCosets vK hvK w
              (localTensorUnitsEquivCompletionProduct vK hvK z))) q =
        completionProductUnitsEquivRightCosets vK hvK w
          (localTensorUnitsEquivCompletionProduct vK hvK z) q
    rw [MulEquiv.apply_symm_apply]
  have hval := congrArg
    (fun u : (LocalizedCompletion vK w)ˣ =>
      (u : LocalizedCompletion vK w)) hcoord
  change
    (((localTensorUnitsEquivLocalPlaceBlock vK hvK w z).1
        (Quotient.out q) :
          (LocalizedCompletion vK w)ˣ) :
      LocalizedCompletion vK w) =
      ((completionProductUnitsEquivRightCosets vK hvK w
          (localTensorUnitsEquivCompletionProduct vK hvK z) q :
            (LocalizedCompletion vK w)ˣ) :
        LocalizedCompletion vK w) at hval
  rw [hval,
    completionProductUnitsEquivRightCosets_apply_coe,
    localTensorUnitsEquivCompletionProduct_apply_coe]
  change
    (localizedCompletionEquivCompletion vK hvK w).symm
        (conjugateExtensionCompletionRingEquiv
          vK w (Quotient.out q)
          (completionTensorDecomposition_left (K := K) (L := L) vK hvK
            (z : LocalTensorAlgebra (L := L) vK)
            (absoluteValueExtensionConjugate
              vK w (Quotient.out q)))) =
      localTensorEvaluation vK hvK w
        (localTensorConjugation vK (Quotient.out q)
          (z : LocalTensorAlgebra (L := L) vK))
  rw [conjugateExtensionCompletionRingEquiv_completionTensorDecomposition_left]
  rfl

/-- The multiplicative equivalence obtained from the tensor-product decomposition is
literally the canonical orbit-evaluation homomorphism. -/
theorem localTensorUnitsEquivLocalPlaceBlock_eq_orbitHom_apply
    (z : (LocalTensorAlgebra (L := L) vK)ˣ) :
    letI :=
      decompositionGroupLocalUnitsAction vK hvK w
    letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI := AbsoluteValue.completionAlgebra vK w.1 w.2
    letI : ∀ w' : AbsoluteValueExtension vK L,
        Algebra vK.Completion w'.1.Completion :=
      fun w' ↦ AbsoluteValue.completionAlgebra vK w'.1 w'.2
    localTensorUnitsEquivLocalPlaceBlock vK hvK w z =
      localTensorOrbitHom vK hvK w z := by
  let _ :=
    decompositionGroupLocalUnitsAction vK hvK w
  let hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  let _ : SMul K w.1.Completion := hK.toSMul
  let _ := AbsoluteValue.completionAlgebra vK w.1 w.2
  let _ : ∀ w' : AbsoluteValueExtension vK L,
      Algebra vK.Completion w'.1.Completion :=
    fun w' ↦ AbsoluteValue.completionAlgebra vK w'.1 w'.2
  apply
    (inducedRightCosetCoordinates
      (absoluteValueDecompositionGroup K w.1)).injective
  funext q
  apply Units.ext
  change
    (((localTensorUnitsEquivLocalPlaceBlock vK hvK w z).1
        (Quotient.out q) :
          (LocalizedCompletion vK w)ˣ) :
      LocalizedCompletion vK w) =
      localTensorEvaluation vK hvK w
        (localTensorConjugation vK (Quotient.out q)
          (z : LocalTensorAlgebra (L := L) vK))
  exact
    localTensorUnitsEquivLocalPlaceBlock_apply_out_coe
      vK hvK w z q

/-- Equivariant concrete form: the actual tensor local factor
and the induced local block are equivalent compatibly with the full
Galois action. -/
theorem localTensorUnitsEquivLocalPlaceBlock_smul
    (τ : L ≃ₐ[K] L)
    (z : (LocalTensorAlgebra (L := L) vK)ˣ) :
    letI :=
      decompositionGroupLocalUnitsAction vK hvK w
    letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI := AbsoluteValue.completionAlgebra vK w.1 w.2
    letI : ∀ w' : AbsoluteValueExtension vK L,
        Algebra vK.Completion w'.1.Completion :=
      fun w' ↦ AbsoluteValue.completionAlgebra vK w'.1 w'.2
    letI := localTensorUnitsAction (K := K) (L := L) vK
    localTensorUnitsEquivLocalPlaceBlock vK hvK w (τ • z) =
      τ • localTensorUnitsEquivLocalPlaceBlock vK hvK w z := by
  let _ :=
    decompositionGroupLocalUnitsAction vK hvK w
  let hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  let _ : SMul K w.1.Completion := hK.toSMul
  let _ := AbsoluteValue.completionAlgebra vK w.1 w.2
  let _ : ∀ w' : AbsoluteValueExtension vK L,
      Algebra vK.Completion w'.1.Completion :=
    fun w' ↦ AbsoluteValue.completionAlgebra vK w'.1 w'.2
  let _ := localTensorUnitsAction (K := K) (L := L) vK
  rw [localTensorUnitsEquivLocalPlaceBlock_eq_orbitHom_apply,
    localTensorUnitsEquivLocalPlaceBlock_eq_orbitHom_apply]
  exact localTensorOrbitHom_smul vK hvK w τ z

/-- The inverse of the induced local-block equivalence is equivariant as well. -/
theorem localTensorUnitsEquivLocalPlaceBlock_symm_smul
    (τ : L ≃ₐ[K] L)
    (f : LocalPlaceBlock vK hvK w) :
    letI :=
      decompositionGroupLocalUnitsAction vK hvK w
    letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI := AbsoluteValue.completionAlgebra vK w.1 w.2
    letI : ∀ w' : AbsoluteValueExtension vK L,
        Algebra vK.Completion w'.1.Completion :=
      fun w' ↦ AbsoluteValue.completionAlgebra vK w'.1 w'.2
    letI := localTensorUnitsAction (K := K) (L := L) vK
    (localTensorUnitsEquivLocalPlaceBlock vK hvK w).symm
        (τ • f) =
      τ •
        (localTensorUnitsEquivLocalPlaceBlock vK hvK w).symm f := by
  let _ :=
    decompositionGroupLocalUnitsAction vK hvK w
  let hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  let _ : SMul K w.1.Completion := hK.toSMul
  let _ := AbsoluteValue.completionAlgebra vK w.1 w.2
  let _ : ∀ w' : AbsoluteValueExtension vK L,
      Algebra vK.Completion w'.1.Completion :=
    fun w' ↦ AbsoluteValue.completionAlgebra vK w'.1 w'.2
  let _ := localTensorUnitsAction (K := K) (L := L) vK
  apply
    (localTensorUnitsEquivLocalPlaceBlock
      vK hvK w).injective
  rw [MulEquiv.apply_symm_apply,
    localTensorUnitsEquivLocalPlaceBlock_smul,
    MulEquiv.apply_symm_apply]

end ProductEquivalences

end LocalClassFieldTheory
