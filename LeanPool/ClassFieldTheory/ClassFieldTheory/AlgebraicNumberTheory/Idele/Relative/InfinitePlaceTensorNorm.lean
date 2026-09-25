/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.ArchimedeanNormQuotient
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.NormApproximation.InfinitePlaces
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.LocalComponent
/-!
# The norm image of an archimedean tensor factor

For a finite Galois extension `L / K`, the determinant-norm image on
`K_v ⊗[K] L` is the field-norm subgroup of any completion of `L` above
the infinite place `v`.  This is the archimedean counterpart of the
finite-place tensor-norm comparison.
-/

@[expose] public section

open scoped NumberField TensorProduct NumberField.LiesOver
open NumberField

noncomputable
section

open LocalClassFieldTheory

open LocalFieldTheory

variable {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L]

/-- The determinant-norm image on the actual archimedean tensor factor
is the field-norm subgroup of any completion above the base place. -/
theorem infiniteTensorNormSubgroup_eq_localNormSubgroup
    (v : InfinitePlace K) (w : InfinitePlace L)
    (hw : w.comap (algebraMap K L) = v) :
    let : w.1.LiesOver v.1 :=
      ⟨congrArg (fun q : InfinitePlace K => q.1) hw⟩
    infiniteTensorNormSubgroup (K := K) (L := L) v =
      localNormSubgroup v.Completion w.Completion := by
  let : w.1.LiesOver v.1 :=
    ⟨congrArg (fun q : InfinitePlace K => q.1) hw⟩
  let u :=
    infinitePlaceAbsoluteValueExtension v w hw
  let hL :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K) u.1
  let : SMul K u.1.Completion :=
    hL.toSMul
  let : Algebra v.1.Completion u.1.Completion :=
    AbsoluteValue.completionAlgebra v.1 u.1 u.2
  let : Algebra v.1.Completion w.1.Completion :=
    AbsoluteValue.completionAlgebra v.1 w.1
      (infinitePlaceAbsoluteValueExtension v w hw).2
  let E :=
    AlgebraicNumberTheory.Valuations.LocalizedCompletion v.1 u
  let : Module.Finite v.1.Completion E :=
    AlgebraicNumberTheory.Valuations.localizedCompletionModuleFinite
      v.1 v.isNontrivial u
  let eVField :
      v.Completion ≃+* v.1.Completion :=
    (infinitePlaceCompletionAlgEquiv
      (K := K) v).toRingEquiv
  let eWField :
      w.Completion ≃+* w.1.Completion :=
    (infinitePlaceCompletionAlgEquiv
      (K := L) w).toRingEquiv
  let eVUnits :
      v.Completionˣ ≃* v.1.Completionˣ :=
    Units.mapEquiv eVField.toMulEquiv
  let eTensorUnits :
      (v.Completion ⊗[K] L)ˣ ≃*
        (LocalTensorAlgebra (L := L) v.1)ˣ :=
    infinitePlaceLocalTensorUnitsEquiv
      (K := K) (L := L) v
  have hTensorNorm
      (z : (v.Completion ⊗[K] L)ˣ) :
      eVUnits
          (infiniteTensorDetNorm
            (K := K) (L := L) v z) =
        localTensorDetNorm
          (K := K) (L := L) v.1
          (eTensorUnits z) := by
    apply Units.ext
    change
      eVField
          (Algebra.norm v.Completion
            (z : v.Completion ⊗[K] L)) =
        Algebra.norm v.1.Completion
          (infinitePlaceLocalTensorAlgEquiv
            (K := K) (L := L) v
            (z : v.Completion ⊗[K] L))
    exact
      _root_.map_norm_tensorProduct_baseChange
        (K := K) (L := L)
        (infinitePlaceCompletionAlgEquiv
          (K := K) v).toAlgHom
        (z : v.Completion ⊗[K] L)
  have hTensorTransport :
      infiniteTensorNormSubgroup
          (K := K) (L := L) v =
        (localTensorNormSubgroup
          (K := K) (L := L) v.1).map
            eVUnits.symm.toMonoidHom := by
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      refine
        ⟨localTensorDetNorm
            (K := K) (L := L) v.1
            (eTensorUnits z),
          ⟨eTensorUnits z, rfl⟩, ?_⟩
      apply eVUnits.injective
      change
        eVUnits
            (eVUnits.symm
              (localTensorDetNorm
                (K := K) (L := L) v.1
                (eTensorUnits z))) =
          eVUnits
            (infiniteTensorDetNorm
              (K := K) (L := L) v z)
      rw [eVUnits.apply_symm_apply]
      exact (hTensorNorm z).symm
    · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
      refine ⟨eTensorUnits.symm z, ?_⟩
      apply eVUnits.injective
      change
        eVUnits
            (infiniteTensorDetNorm
              (K := K) (L := L) v
              (eTensorUnits.symm z)) =
          eVUnits
            (eVUnits.symm
              (localTensorDetNorm
                (K := K) (L := L) v.1 z))
      rw [hTensorNorm, eTensorUnits.apply_symm_apply,
        eVUnits.apply_symm_apply]
  let eLocalized :
      E ≃ₐ[v.1.Completion] w.1.Completion :=
    AlgebraicNumberTheory.Valuations.localizedCompletionEquivCompletion
      v.1 v.isNontrivial u
  let eBase :
      v.1.Completion ≃+* v.Completion :=
    eVField.symm
  let eExtension :
      E ≃+* w.Completion :=
    eLocalized.toRingEquiv.trans eWField.symm
  have hCompatible :
      RingHom.comp
          (algebraMap v.Completion w.Completion)
          eBase =
        RingHom.comp eExtension
          (algebraMap v.1.Completion E) := by
    have hWrapperCompletionSymm :=
      ringEquiv_compat_symm
        eVField eWField (by
          simpa [u, infinitePlaceAbsoluteValueExtension,
            eVField, eWField] using
            (infinitePlaceCompletionAlgEquiv_algebraMap
              (K := K) (L := L) v w hw))
    apply RingHom.ext
    intro x
    change
      algebraMap v.Completion w.Completion
          (eVField.symm x) =
        eWField.symm
          (eLocalized
            (algebraMap v.1.Completion E x))
    rw [eLocalized.commutes]
    exact
      DFunLike.congr_fun hWrapperCompletionSymm x
  have hNormTransport :
      (localNormSubgroup
          v.1.Completion E).map
            eVUnits.symm.toMonoidHom =
        localNormSubgroup
          v.Completion w.Completion := by
    ext x
    constructor
    · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
      refine
        ⟨Units.mapEquiv
            eExtension.toMulEquiv z, ?_⟩
      simpa [eBase, eVUnits] using
        (normUnits_map_ringEquiv
          eBase eExtension hCompatible z).symm
    · rintro ⟨z, rfl⟩
      refine
        ⟨normUnits v.1.Completion E
            ((Units.mapEquiv
              eExtension.toMulEquiv).symm z),
          ⟨(Units.mapEquiv
              eExtension.toMulEquiv).symm z, rfl⟩,
          ?_⟩
      have hTransport :=
        normUnits_map_ringEquiv
          eBase eExtension hCompatible
          ((Units.mapEquiv
            eExtension.toMulEquiv).symm z)
      rw [(Units.mapEquiv
        eExtension.toMulEquiv).apply_symm_apply] at hTransport
      simpa [eBase, eVUnits] using hTransport
  rw [hTensorTransport,
    localTensorNormSubgroup_eq_localNormSubgroup
      (K := K) (L := L) v.1 u v.isNontrivial]
  exact hNormTransport
