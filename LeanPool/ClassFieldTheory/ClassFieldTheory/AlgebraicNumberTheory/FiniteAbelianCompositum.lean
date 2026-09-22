/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.FieldTheory.Galois.GaloisClosure
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.SeparableClosureEmbedding
/-!
# Finite abelian composita

This file gives a common realization, in a chosen separable closure, of the
compositum of two finite abelian Galois extensions.  It also records the
canonical factor embeddings and their elementary degree bounds.
-/

noncomputable section

namespace AlgebraicNumberTheory

open scoped IsMulCommutative

universe u v

/-- The chosen copy of a finite Galois extension in the separable closure. -/
def finiteGaloisFieldRange
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [IsGalois K L] :
    IntermediateField K (SeparableClosure K) :=
  AlgHom.fieldRange
    (AlgebraicNumberTheory.separableEmbeddingIntoSeparableClosure K L)

/-- The chosen embedding identifies the extension with its field range. -/
def finiteGaloisFieldRangeEquiv
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    L ≃ₐ[K] finiteGaloisFieldRange K L :=
  AlgEquiv.ofInjectiveField
    (AlgebraicNumberTheory.separableEmbeddingIntoSeparableClosure K L)

/-- The chosen field-range model is finite-dimensional over the base. -/
instance finiteGaloisFieldRange_finiteDimensional
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    FiniteDimensional K (finiteGaloisFieldRange K L) :=
  (finiteGaloisFieldRangeEquiv K L).toLinearEquiv.finiteDimensional

/-- The chosen field-range model is Galois over the base. -/
instance finiteGaloisFieldRange_isGalois
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    IsGalois K (finiteGaloisFieldRange K L) :=
  IsGalois.of_algEquiv (finiteGaloisFieldRangeEquiv K L)

section AbelianCompositum

variable (K : Type u) [Field K]
variable {Omega : Type v} [Field Omega] [Algebra K Omega]

/-- The compositum, inside a common overfield, of two abelian Galois
intermediate fields is again abelian Galois over the base. -/
theorem isAbelianGalois_sup
    (A B : IntermediateField K Omega)
    [FiniteDimensional K A] [FiniteDimensional K B]
    [IsAbelianGalois K A] [IsAbelianGalois K B] :
    IsAbelianGalois K (A ⊔ B : IntermediateField K Omega) := by
  let M : IntermediateField K Omega := A ⊔ B
  let j : M →ₐ[K] Omega := M.val
  let A' : IntermediateField K M := A.comap j
  let B' : IntermediateField K M := B.comap j

  have hjrange : j.fieldRange = M :=
    IntermediateField.fieldRange_val M
  have hAmap : A'.map j = A := by
    apply IntermediateField.map_comap_eq_self
    rw [hjrange]
    exact le_sup_left
  have hBmap : B'.map j = B := by
    apply IntermediateField.map_comap_eq_self
    rw [hjrange]
    exact le_sup_right
  have hsup : A' ⊔ B' = ⊤ := by
    apply IntermediateField.map_injective j
    rw [IntermediateField.map_sup, hAmap, hBmap,
      ← AlgHom.fieldRange_eq_map, hjrange]

  let eA : A' →ₐ[K] A :=
    ((j.comp A'.val).codRestrict A.toSubalgebra fun x ↦ x.2)
  let eB : B' →ₐ[K] B :=
    ((j.comp B'.val).codRestrict B.toSubalgebra fun x ↦ x.2)
  let : IsAbelianGalois K A' := IsAbelianGalois.of_algHom eA
  let : IsAbelianGalois K B' := IsAbelianGalois.of_algHom eB
  let : IsGalois K M := inferInstance

  let rA : (M ≃ₐ[K] M) →* (A' ≃ₐ[K] A') :=
    AlgEquiv.restrictNormalHom A'
  let rB : (M ≃ₐ[K] M) →* (B' ≃ₐ[K] B') :=
    AlgEquiv.restrictNormalHom B'
  let r : (M ≃ₐ[K] M) →* (A' ≃ₐ[K] A') × (B' ≃ₐ[K] B') :=
    rA.prod rB
  have hr : Function.Injective r := by
    rw [injective_iff_map_eq_one]
    intro sigma hsigma
    have hAone : rA sigma = 1 := congrArg Prod.fst hsigma
    have hBone : rB sigma = 1 := congrArg Prod.snd hsigma
    have hmemA : sigma ∈ A'.fixingSubgroup := by
      rw [← IntermediateField.restrictNormalHom_ker]
      exact hAone
    have hmemB : sigma ∈ B'.fixingSubgroup := by
      rw [← IntermediateField.restrictNormalHom_ker]
      exact hBone
    have hmem : sigma ∈ (A' ⊔ B').fixingSubgroup := by
      rw [IntermediateField.fixingSubgroup_sup]
      exact ⟨hmemA, hmemB⟩
    simpa [hsup] using hmem

  exact
    { is_comm.comm := fun sigma tau ↦ by
        apply hr
        rw [map_mul, map_mul]
        apply Prod.ext
        · change rA sigma * rA tau = rA tau * rA sigma
          exact mul_comm (rA sigma) (rA tau)
        · change rB sigma * rB tau = rB tau * rB sigma
          exact mul_comm (rB sigma) (rB tau) }

end AbelianCompositum

section ConcreteAbelianCompositum

variable (K L E : Type)
variable [Field K]
variable [Field L] [Field E] [Algebra K L] [Algebra K E]
variable [FiniteDimensional K L] [FiniteDimensional K E]
variable [IsAbelianGalois K L] [IsAbelianGalois K E]

/-- A concrete common realization of the compositum of two finite abelian
extensions in the chosen separable closure of the base. -/
def finiteAbelianCompositumField :
    IntermediateField K (SeparableClosure K) :=
  finiteGaloisFieldRange K L ⊔ finiteGaloisFieldRange K E

/-- The concrete compositum is finite-dimensional over the base. -/
instance finiteAbelianCompositumField_finiteDimensional :
    FiniteDimensional K (finiteAbelianCompositumField K L E) :=
  IntermediateField.finiteDimensional_sup
    (finiteGaloisFieldRange K L) (finiteGaloisFieldRange K E)

/-- The concrete compositum is abelian Galois over the base. -/
instance finiteAbelianCompositumField_isAbelianGalois :
    IsAbelianGalois K (finiteAbelianCompositumField K L E) := by
  let : IsAbelianGalois K (finiteGaloisFieldRange K L) :=
    IsAbelianGalois.of_algHom
      (finiteGaloisFieldRangeEquiv K L).symm.toAlgHom
  let : IsAbelianGalois K (finiteGaloisFieldRange K E) :=
    IsAbelianGalois.of_algHom
      (finiteGaloisFieldRangeEquiv K E).symm.toAlgHom
  exact isAbelianGalois_sup K
    (finiteGaloisFieldRange K L) (finiteGaloisFieldRange K E)

/-- The given left extension embeds into its concrete compositum. -/
def finiteAbelianCompositumEmbeddingLeft :
    L →ₐ[K] finiteAbelianCompositumField K L E :=
  (IntermediateField.inclusion le_sup_left).comp
    (finiteGaloisFieldRangeEquiv K L).toAlgHom

/-- The given right extension embeds into its concrete compositum. -/
def finiteAbelianCompositumEmbeddingRight :
    E →ₐ[K] finiteAbelianCompositumField K L E :=
  (IntermediateField.inclusion le_sup_right).comp
    (finiteGaloisFieldRangeEquiv K E).toAlgHom

/-- The images of the two canonical embeddings generate their concrete
compositum. -/
theorem finiteAbelianCompositum_embeddingRanges_sup_eq_top :
    (finiteAbelianCompositumEmbeddingLeft K L E).fieldRange ⊔
        (finiteAbelianCompositumEmbeddingRight K L E).fieldRange = ⊤ := by
  let A₀ : IntermediateField K (SeparableClosure K) :=
    finiteGaloisFieldRange K L
  let B₀ : IntermediateField K (SeparableClosure K) :=
    finiteGaloisFieldRange K E
  let M : IntermediateField K (SeparableClosure K) :=
    finiteAbelianCompositumField K L E
  let j : M →ₐ[K] SeparableClosure K := M.val
  have hjrange : j.fieldRange = M :=
    IntermediateField.fieldRange_val M
  have hjleft :
      j.comp (finiteAbelianCompositumEmbeddingLeft K L E) =
        A₀.val.comp (finiteGaloisFieldRangeEquiv K L).toAlgHom := by
    ext x
    rfl
  have hjright :
      j.comp (finiteAbelianCompositumEmbeddingRight K L E) =
        B₀.val.comp (finiteGaloisFieldRangeEquiv K E).toAlgHom := by
    ext x
    rfl
  have heqLeft :
      (finiteGaloisFieldRangeEquiv K L).toAlgHom.fieldRange =
        (⊤ : IntermediateField K A₀) :=
    AlgHom.fieldRange_eq_top.mpr
      (finiteGaloisFieldRangeEquiv K L).surjective
  have heqRight :
      (finiteGaloisFieldRangeEquiv K E).toAlgHom.fieldRange =
        (⊤ : IntermediateField K B₀) :=
    AlgHom.fieldRange_eq_top.mpr
      (finiteGaloisFieldRangeEquiv K E).surjective
  have hleft :
      (finiteAbelianCompositumEmbeddingLeft K L E).fieldRange.map j = A₀ := by
    calc
      (finiteAbelianCompositumEmbeddingLeft K L E).fieldRange.map j =
          (j.comp (finiteAbelianCompositumEmbeddingLeft K L E)).fieldRange :=
        AlgHom.map_fieldRange _ _
      _ = (A₀.val.comp
          (finiteGaloisFieldRangeEquiv K L).toAlgHom).fieldRange :=
        congrArg AlgHom.fieldRange hjleft
      _ = (finiteGaloisFieldRangeEquiv K L).toAlgHom.fieldRange.map A₀.val :=
        (AlgHom.map_fieldRange _ _).symm
      _ = (⊤ : IntermediateField K A₀).map A₀.val := by
        rw [heqLeft]
      _ = A₀.val.fieldRange :=
        (AlgHom.fieldRange_eq_map A₀.val).symm
      _ = A₀ := IntermediateField.fieldRange_val A₀
  have hright :
      (finiteAbelianCompositumEmbeddingRight K L E).fieldRange.map j = B₀ := by
    calc
      (finiteAbelianCompositumEmbeddingRight K L E).fieldRange.map j =
          (j.comp (finiteAbelianCompositumEmbeddingRight K L E)).fieldRange :=
        AlgHom.map_fieldRange _ _
      _ = (B₀.val.comp
          (finiteGaloisFieldRangeEquiv K E).toAlgHom).fieldRange :=
        congrArg AlgHom.fieldRange hjright
      _ = (finiteGaloisFieldRangeEquiv K E).toAlgHom.fieldRange.map B₀.val :=
        (AlgHom.map_fieldRange _ _).symm
      _ = (⊤ : IntermediateField K B₀).map B₀.val := by
        rw [heqRight]
      _ = B₀.val.fieldRange :=
        (AlgHom.fieldRange_eq_map B₀.val).symm
      _ = B₀ := IntermediateField.fieldRange_val B₀
  apply IntermediateField.map_injective j
  calc
    ((finiteAbelianCompositumEmbeddingLeft K L E).fieldRange ⊔
        (finiteAbelianCompositumEmbeddingRight K L E).fieldRange).map j =
        A₀ ⊔ B₀ := by
      rw [IntermediateField.map_sup, hleft, hright]
    _ = M := rfl
    _ = j.fieldRange := hjrange.symm
    _ = (⊤ : IntermediateField K M).map j :=
      AlgHom.fieldRange_eq_map j

/-- The degree of the left factor is bounded by the degree of the
compositum. -/
theorem finiteAbelianCompositum_finrank_left_le :
    Module.finrank K L ≤
      Module.finrank K (finiteAbelianCompositumField K L E) :=
  (finiteAbelianCompositumEmbeddingLeft K L E).toLinearMap
    |>.finrank_le_finrank_of_injective
      (finiteAbelianCompositumEmbeddingLeft K L E).injective

/-- The degree of the right factor is bounded by the degree of the
compositum. -/
theorem finiteAbelianCompositum_finrank_right_le :
    Module.finrank K E ≤
      Module.finrank K (finiteAbelianCompositumField K L E) :=
  (finiteAbelianCompositumEmbeddingRight K L E).toLinearMap
    |>.finrank_le_finrank_of_injective
      (finiteAbelianCompositumEmbeddingRight K L E).injective

end ConcreteAbelianCompositum

end AlgebraicNumberTheory
