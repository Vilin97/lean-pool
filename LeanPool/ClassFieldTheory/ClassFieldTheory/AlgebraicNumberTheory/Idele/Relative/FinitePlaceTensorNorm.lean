/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalBlocks.TensorNorm
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.NormApproximation.FinitePlaces
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.LocalComponent
/-!
# Tensor norm images at actual finite places

This file specializes the local tensor norm calculation to a height-one
prime of a number field.  The canonical comparison

`(K, |·|_v)^∧ ≃ K_v`

identifies the determinant norm on
`(K, |·|_v)^∧ ⊗[K] L` with the determinant norm on the concrete tensor
factor `K_v ⊗[K] L` used by relative ideles.  Consequently its image is
the chosen open local norm subgroup from `LocalNormApproximation`.

The finite component of every global relative-idele norm therefore lies
in that subgroup, and its corresponding local quotient class is one.
-/

open scoped NumberField TensorProduct
open NumberField IsDedekindDomain

noncomputable section

open LocalClassFieldTheory


open AlgebraicNumberTheory.Valuations
open LocalFieldTheory

variable {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

/-- The canonical completion comparison as a `K`-algebra
equivalence. -/
noncomputable def finitePlaceCompletionAlgEquiv
    (v : HeightOneSpectrum (𝓞 K)) :
    (NumberField.HeightOneSpectrum.adicAbv K v).Completion ≃ₐ[K]
      v.adicCompletion K where
  __ := finitePlaceCompletionRingEquiv v
  commutes' x := by
    change
      finitePlaceCompletionRingHom v
          (((WithAbs.equiv
            (NumberField.HeightOneSpectrum.adicAbv K v)).symm x :
              WithAbs
                (NumberField.HeightOneSpectrum.adicAbv K v)) :
            (NumberField.HeightOneSpectrum.adicAbv K v).Completion) =
        algebraMap K (v.adicCompletion K) x
    rw [finitePlaceCompletionRingHom_coe]
    rfl

/-- Base change of the first tensor factor gives the concrete tensor
algebra at `v`. -/
noncomputable def finitePlaceLocalTensorAlgEquiv
    (v : HeightOneSpectrum (𝓞 K)) :
    LocalTensorAlgebra (L := L)
        (NumberField.HeightOneSpectrum.adicAbv K v) ≃ₐ[K]
      v.adicCompletion K ⊗[K] L :=
  Algebra.TensorProduct.congr
    (finitePlaceCompletionAlgEquiv v)
    (AlgEquiv.refl : L ≃ₐ[K] L)

/-- The induced equivalence on tensor-algebra unit groups. -/
noncomputable def finitePlaceLocalTensorUnitsEquiv
    (v : HeightOneSpectrum (𝓞 K)) :
    (LocalTensorAlgebra (L := L)
      (NumberField.HeightOneSpectrum.adicAbv K v))ˣ ≃*
      (v.adicCompletion K ⊗[K] L)ˣ :=
  Units.mapEquiv
    (finitePlaceLocalTensorAlgEquiv
      (K := K) (L := L) v).toMulEquiv

omit [NumberField L] [IsGalois K L] in
/-- The completed-base comparison intertwines the two determinant norm
maps. -/
theorem finitePlaceLocalTensorNorm_commutes
    (v : HeightOneSpectrum (𝓞 K))
    (z :
      (LocalTensorAlgebra (L := L)
        (NumberField.HeightOneSpectrum.adicAbv K v))ˣ) :
    finitePlaceCompletionUnitsContinuousMulEquiv v
        (localTensorDetNorm
          (K := K) (L := L)
          (NumberField.HeightOneSpectrum.adicAbv K v) z) =
      _root_.localTensorNorm
        (K := K) (L := L) v
        (finitePlaceLocalTensorUnitsEquiv
          (K := K) (L := L) v z) := by
  apply Units.ext
  exact
    _root_.map_norm_tensorProduct_baseChange
      (K := K) (L := L)
      (finitePlaceCompletionAlgEquiv v).toAlgHom
      (z : LocalTensorAlgebra (L := L)
        (NumberField.HeightOneSpectrum.adicAbv K v))

omit [NumberField L] [IsGalois K L] in
/-- Before choosing a localization, the concrete determinant-norm
image is the transport of the absolute-value tensor norm image. -/
theorem finitePlaceLocalTensorNorm_range_eq_transport
    (v : HeightOneSpectrum (𝓞 K)) :
    (_root_.localTensorNorm
        (K := K) (L := L) v).range =
      (localTensorNormSubgroup
        (K := K) (L := L)
        (NumberField.HeightOneSpectrum.adicAbv K v)).map
          (finitePlaceCompletionUnitsContinuousMulEquiv
            v).toMonoidHom := by
  let T :=
    finitePlaceLocalTensorUnitsEquiv
      (K := K) (L := L) v
  let e :=
    finitePlaceCompletionUnitsContinuousMulEquiv v
  ext x
  constructor
  · rintro ⟨z, hz⟩
    refine
      ⟨localTensorDetNorm
          (K := K) (L := L)
          (NumberField.HeightOneSpectrum.adicAbv K v)
          (T.symm z),
        ⟨T.symm z, rfl⟩, ?_⟩
    calc
      e
          (localTensorDetNorm
            (K := K) (L := L)
            (NumberField.HeightOneSpectrum.adicAbv K v)
            (T.symm z)) =
          _root_.localTensorNorm
            (K := K) (L := L) v
            (T (T.symm z)) :=
        finitePlaceLocalTensorNorm_commutes
          (K := K) (L := L) v (T.symm z)
      _ =
          _root_.localTensorNorm
            (K := K) (L := L) v z := by
        rw [T.apply_symm_apply]
      _ = x := hz
  · rintro ⟨y, ⟨z, hz⟩, hy⟩
    refine ⟨T z, ?_⟩
    calc
      _root_.localTensorNorm
          (K := K) (L := L) v (T z) =
          e
            (localTensorDetNorm
              (K := K) (L := L)
              (NumberField.HeightOneSpectrum.adicAbv K v) z) :=
        (finitePlaceLocalTensorNorm_commutes
          (K := K) (L := L) v z).symm
      _ = e y := congrArg e hz
      _ = x := hy

omit [NumberField L] in
/-- **Actual finite-place tensor norm image.**  The image of the
determinant norm on `K_v ⊗[K] L` is exactly the chosen local field-norm
subgroup in the concrete finite idele coordinate. -/
theorem finitePlaceLocalTensorNorm_range_eq_chosenLocalNormSubgroup
    (v : HeightOneSpectrum (𝓞 K)) :
    (_root_.localTensorNorm
        (K := K) (L := L) v).range =
      chosenFinitePlaceLocalNormSubgroup
        (K := K) (L := L) v := by
  let vK :=
    NumberField.HeightOneSpectrum.adicAbv K v
  let w := chosenFinitePlaceExtension (L := L) v
  let hvK : vK.IsNontrivial :=
    RayClass.adicAbv_isNontrivial v
  let hK :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K) w.1
  let : SMul K w.1.Completion := hK.toSMul
  let : Algebra vK.Completion w.1.Completion :=
    AbsoluteValue.completionAlgebra vK w.1 w.2
  let E := LocalizedCompletion vK w
  let : Module.Finite vK.Completion E :=
    localizedCompletionModuleFinite vK hvK w
  rw [finitePlaceLocalTensorNorm_range_eq_transport
    (K := K) (L := L) v]
  change
    (localTensorNormSubgroup
      (K := K) (L := L) vK).map
        (finitePlaceCompletionUnitsContinuousMulEquiv
          v).toMonoidHom =
      (localNormSubgroup vK.Completion E).map
        (finitePlaceCompletionUnitsContinuousMulEquiv
          v).toMonoidHom
  rw [localTensorNormSubgroup_eq_localNormSubgroup
    (K := K) (L := L) vK w hvK]

omit [NumberField L] in
/-- The quotient projection whose kernel is the finite-place tensor
norm image. -/
noncomputable def finitePlaceTensorNormClass
    (v : HeightOneSpectrum (𝓞 K)) :
    (v.adicCompletion K)ˣ →*
      ChosenFinitePlaceNormQuotient
        (K := K) (L := L) v :=
  QuotientGroup.mk'
    (chosenFinitePlaceLocalNormSubgroup
      (K := K) (L := L) v)

omit [NumberField L] in
/-- A concrete local class is trivial exactly when its representative
is a determinant norm from `K_v ⊗[K] L`. -/
theorem finitePlaceTensorNormClass_eq_one_iff
    (v : HeightOneSpectrum (𝓞 K))
    (x : (v.adicCompletion K)ˣ) :
    finitePlaceTensorNormClass
        (K := K) (L := L) v x = 1 ↔
      ∃ z : (v.adicCompletion K ⊗[K] L)ˣ,
        _root_.localTensorNorm
          (K := K) (L := L) v z = x := by
  change
    QuotientGroup.mk'
        (chosenFinitePlaceLocalNormSubgroup
          (K := K) (L := L) v) x = 1 ↔ _
  constructor
  · intro hx
    have hxmem :
        x ∈ chosenFinitePlaceLocalNormSubgroup
          (K := K) (L := L) v :=
      (QuotientGroup.eq_one_iff
        (N := chosenFinitePlaceLocalNormSubgroup
          (K := K) (L := L) v)
        (x := x)).mp hx
    rw [← finitePlaceLocalTensorNorm_range_eq_chosenLocalNormSubgroup
      (K := K) (L := L) v] at hxmem
    exact hxmem
  · intro hx
    apply
      (QuotientGroup.eq_one_iff
        (N := chosenFinitePlaceLocalNormSubgroup
          (K := K) (L := L) v)
        (x := x)).mpr
    rw [← finitePlaceLocalTensorNorm_range_eq_chosenLocalNormSubgroup
      (K := K) (L := L) v]
    exact hx

omit [NumberField L] in
/-- The kernel of the concrete quotient projection is precisely the
finite-place determinant norm image. -/
theorem finitePlaceTensorNormClass_ker
    (v : HeightOneSpectrum (𝓞 K)) :
    (finitePlaceTensorNormClass
      (K := K) (L := L) v).ker =
      (_root_.localTensorNorm
        (K := K) (L := L) v).range := by
  ext x
  rw [MonoidHom.mem_ker,
    finitePlaceTensorNormClass_eq_one_iff
      (K := K) (L := L) v]
  rfl

omit [NumberField L] in
/-- Every finite component of a global relative-idele norm lies in the
chosen local norm subgroup. -/
theorem relativeIdeleNorm_finiteComponent_mem_chosenLocalNormSubgroup
    (v : HeightOneSpectrum (𝓞 K))
    (a : RelativeIdeleGroup K L) :
    IdeleGroup.finiteComponent v
        (RelativeIdeleGroup.norm K L a) ∈
      chosenFinitePlaceLocalNormSubgroup
        (K := K) (L := L) v := by
  rw [← finitePlaceLocalTensorNorm_range_eq_chosenLocalNormSubgroup
    (K := K) (L := L) v]
  exact
    ⟨RelativeIdeleGroup.finiteComponent
        (K := K) (L := L) v a,
      (RelativeIdeleGroup.finiteComponent_norm
        (K := K) (L := L) v a).symm⟩

omit [NumberField L] in
/-- Hence the local tensor-norm class of every finite component of a
global relative-idele norm is trivial. -/
theorem finitePlaceTensorNormClass_relativeIdeleNorm
    (v : HeightOneSpectrum (𝓞 K))
    (a : RelativeIdeleGroup K L) :
    finitePlaceTensorNormClass
        (K := K) (L := L) v
        (IdeleGroup.finiteComponent v
          (RelativeIdeleGroup.norm K L a)) = 1 := by
  rw [finitePlaceTensorNormClass_eq_one_iff
    (K := K) (L := L) v]
  exact
    ⟨RelativeIdeleGroup.finiteComponent
        (K := K) (L := L) v a,
      (RelativeIdeleGroup.finiteComponent_norm
        (K := K) (L := L) v a).symm⟩
