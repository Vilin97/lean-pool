/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Relative.FinitePlaceTensorNorm
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalBlocks.Tensor
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Adele.RestrictedAction
/-!
# Finite-place tensor factors as induced local blocks

This file is the finite-place counterpart of
`InfinitePlaceTensorBlock`.  It compares the concrete completion
`K_v` used by the idele restricted product with the absolute-value
completion used by the canonical local tensor decomposition, and records equivariance for
conjugation on the second tensor factor.
-/

open scoped NumberField TensorProduct
open NumberField IsDedekindDomain

noncomputable section

open LocalClassFieldTheory


open AlgebraicNumberTheory.Valuations
open HilbertRamification

variable {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

omit [NumberField L] [FiniteDimensional K L] [IsGalois K L] in
/-- Base change from the absolute-value completion to the concrete
adic completion commutes with conjugation on `L`. -/
theorem finitePlaceLocalTensorAlgEquiv_conjugation
    (v : HeightOneSpectrum (𝓞 K))
    (σ : L ≃ₐ[K] L)
    (z :
      LocalTensorAlgebra (L := L)
        (HeightOneSpectrum.adicAbv K v)) :
    finitePlaceLocalTensorAlgEquiv
        (K := K) (L := L) v
        (localTensorConjugation
          (K := K) (L := L)
          (HeightOneSpectrum.adicAbv K v) σ z) =
      scalarTensorConjugation
        (K := K) (L := L)
        (A := v.adicCompletion K) σ
        (finitePlaceLocalTensorAlgEquiv
          (K := K) (L := L) v z) := by
  induction z using TensorProduct.inductionOn with
  | tmul a x => rfl
  | add x y hx hy => simp [hx, hy]

omit [NumberField L] [FiniteDimensional K L] [IsGalois K L] in
/-- The finite-completion comparison on tensor units is equivariant. -/
theorem finitePlaceLocalTensorUnitsEquiv_smul
    (v : HeightOneSpectrum (𝓞 K))
    (σ : L ≃ₐ[K] L)
    (z :
      (LocalTensorAlgebra (L := L)
        (HeightOneSpectrum.adicAbv K v))ˣ) :
    letI :=
      localTensorUnitsAction
        (K := K) (L := L)
        (HeightOneSpectrum.adicAbv K v)
    letI :=
      scalarTensorUnitsAction
        (K := K) (L := L)
        (A := v.adicCompletion K)
    finitePlaceLocalTensorUnitsEquiv
        (K := K) (L := L) v (σ • z) =
      σ • finitePlaceLocalTensorUnitsEquiv
        (K := K) (L := L) v z := by
  let :=
    localTensorUnitsAction
      (K := K) (L := L)
      (HeightOneSpectrum.adicAbv K v)
  let :=
    scalarTensorUnitsAction
      (K := K) (L := L)
      (A := v.adicCompletion K)
  apply Units.ext
  exact finitePlaceLocalTensorAlgEquiv_conjugation
    (K := K) (L := L) v σ
      (z :
        LocalTensorAlgebra (L := L)
          (HeightOneSpectrum.adicAbv K v))

omit [NumberField L] [FiniteDimensional K L] [IsGalois K L] in
/-- Equivariance of the inverse finite-completion comparison. -/
theorem finitePlaceLocalTensorUnitsEquiv_symm_smul
    (v : HeightOneSpectrum (𝓞 K))
    (σ : L ≃ₐ[K] L)
    (z : (v.adicCompletion K ⊗[K] L)ˣ) :
    letI :=
      localTensorUnitsAction
        (K := K) (L := L)
        (HeightOneSpectrum.adicAbv K v)
    letI :=
      scalarTensorUnitsAction
        (K := K) (L := L)
        (A := v.adicCompletion K)
    (finitePlaceLocalTensorUnitsEquiv
        (K := K) (L := L) v).symm (σ • z) =
      σ •
        (finitePlaceLocalTensorUnitsEquiv
          (K := K) (L := L) v).symm z := by
  let :=
    localTensorUnitsAction
      (K := K) (L := L)
      (HeightOneSpectrum.adicAbv K v)
  let :=
    scalarTensorUnitsAction
      (K := K) (L := L)
      (A := v.adicCompletion K)
  apply
    (finitePlaceLocalTensorUnitsEquiv
      (K := K) (L := L) v).injective
  rw [MulEquiv.apply_symm_apply,
    finitePlaceLocalTensorUnitsEquiv_smul,
    MulEquiv.apply_symm_apply]

/-- The local tensor decomposition for the concrete finite component type used by relative
ideles. -/
noncomputable def finitePlaceTensorUnitsEquivLocalPlaceBlock
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K v) L) :
    letI :=
      decompositionGroupLocalUnitsAction
        (HeightOneSpectrum.adicAbv K v)
        (RayClass.adicAbv_isNontrivial v) w
    letI hK :=
      AbsoluteValue.extensionCompletionAlgebra
        (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI :=
      AbsoluteValue.completionAlgebra
        (HeightOneSpectrum.adicAbv K v) w.1 w.2
    letI : ∀ w' : AbsoluteValueExtension
        (HeightOneSpectrum.adicAbv K v) L,
      Algebra
        (HeightOneSpectrum.adicAbv K v).Completion
        w'.1.Completion :=
      fun w' =>
        AbsoluteValue.completionAlgebra
          (HeightOneSpectrum.adicAbv K v)
          w'.1 w'.2
    (v.adicCompletion K ⊗[K] L)ˣ ≃*
      LocalPlaceBlock
        (HeightOneSpectrum.adicAbv K v)
        (RayClass.adicAbv_isNontrivial v) w :=
  (finitePlaceLocalTensorUnitsEquiv
      (K := K) (L := L) v).symm.trans
    (localTensorUnitsEquivLocalPlaceBlock
      (HeightOneSpectrum.adicAbv K v)
      (RayClass.adicAbv_isNontrivial v) w)

section Equivariance

variable
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K v) L)

/-- The decomposition group acts on the units of the localized completion at the chosen finite
place. -/
local instance finitePlaceDecompositionGroupAction :
    MulDistribMulAction
      (absoluteValueDecompositionGroup K w.1)
      (AlgebraicNumberTheory.Valuations.LocalizedCompletion
        (HeightOneSpectrum.adicAbv K v) w)ˣ :=
  decompositionGroupLocalUnitsAction
    (HeightOneSpectrum.adicAbv K v)
    (RayClass.adicAbv_isNontrivial v) w

/-- The completion at the extended finite absolute value is an algebra over the base field. -/
local instance finitePlaceExtensionCompletionAlgebra :
    Algebra K w.1.Completion :=
  AbsoluteValue.extensionCompletionAlgebra (K := K) w.1

/-- The base field acts on the extended finite-place completion through its chosen algebra
structure. -/
local instance finitePlaceExtensionCompletionSMul :
    SMul K w.1.Completion :=
  (finitePlaceExtensionCompletionAlgebra v w).toSMul

/-- The completion at the extended finite place is an algebra over the base-place completion. -/
local instance finitePlaceLocalizedCompletionAlgebra :
    Algebra
      (HeightOneSpectrum.adicAbv K v).Completion
      w.1.Completion :=
  AbsoluteValue.completionAlgebra
    (HeightOneSpectrum.adicAbv K v) w.1 w.2

/-- Every extension of the finite absolute value gives a completion over the base-place
completion. -/
local instance finitePlaceAllCompletionAlgebra
    (w' : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K v) L) :
    Algebra
      (HeightOneSpectrum.adicAbv K v).Completion
      w'.1.Completion :=
  AbsoluteValue.completionAlgebra
    (HeightOneSpectrum.adicAbv K v) w'.1 w'.2

/-- Global Galois automorphisms act on units of the finite-place scalar tensor algebra. -/
local instance finitePlaceScalarTensorUnitsAction :
    MulDistribMulAction
      (L ≃ₐ[K] L)
      (v.adicCompletion K ⊗[K] L)ˣ :=
  scalarTensorUnitsAction
    (K := K) (L := L) (A := v.adicCompletion K)

/-- Global Galois automorphisms act on units of the finite-place local tensor algebra. -/
local instance finitePlaceLocalTensorUnitsAction :
    MulDistribMulAction
      (L ≃ₐ[K] L)
      (LocalTensorAlgebra (L := L)
        (HeightOneSpectrum.adicAbv K v))ˣ :=
  localTensorUnitsAction
    (K := K) (L := L)
    (HeightOneSpectrum.adicAbv K v)

omit [NumberField L] in
/-- The concrete finite-place local tensor decomposition is equivariant for the
full global Galois action. -/
theorem finitePlaceTensorUnitsEquivLocalPlaceBlock_smul
    (σ : L ≃ₐ[K] L)
    (z : (v.adicCompletion K ⊗[K] L)ˣ) :
    finitePlaceTensorUnitsEquivLocalPlaceBlock
        (K := K) (L := L) v w (σ • z) =
      σ •
        finitePlaceTensorUnitsEquivLocalPlaceBlock
          (K := K) (L := L) v w z := by
  have hsource :
      (finitePlaceLocalTensorUnitsEquiv
          (K := K) (L := L) v).symm (σ • z) =
        σ •
          (finitePlaceLocalTensorUnitsEquiv
            (K := K) (L := L) v).symm z :=
    finitePlaceLocalTensorUnitsEquiv_symm_smul
      (K := K) (L := L) v σ z
  calc
    finitePlaceTensorUnitsEquivLocalPlaceBlock
        (K := K) (L := L) v w (σ • z) =
      localTensorUnitsEquivLocalPlaceBlock
        (HeightOneSpectrum.adicAbv K v)
        (RayClass.adicAbv_isNontrivial v) w
        (σ •
          (finitePlaceLocalTensorUnitsEquiv
            (K := K) (L := L) v).symm z) :=
      congrArg
        (localTensorUnitsEquivLocalPlaceBlock
          (HeightOneSpectrum.adicAbv K v)
          (RayClass.adicAbv_isNontrivial v) w)
        hsource
    _ =
      σ •
        finitePlaceTensorUnitsEquivLocalPlaceBlock
          (K := K) (L := L) v w z :=
      localTensorUnitsEquivLocalPlaceBlock_smul
        (HeightOneSpectrum.adicAbv K v)
        (RayClass.adicAbv_isNontrivial v) w σ
        ((finitePlaceLocalTensorUnitsEquiv
          (K := K) (L := L) v).symm z)

end Equivariance
