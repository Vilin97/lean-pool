/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Adele.RestrictedAction
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalBlocks.Tensor
import Mathlib.NumberTheory.NumberField.Completion.LiesOverInstances
/-!
# Archimedean relative-idele factors as induced local blocks

The concrete archimedean completion `w.Completion` used by the adele
library is canonically the completion of the underlying absolute value
`w.1`.  Base change along this equivalence connects the actual
archimedean component of a relative idele to the local tensor block of
the local tensor decomposition, equivariantly for the full Galois action.
-/

open scoped NumberField TensorProduct NumberField.LiesOver
open NumberField

noncomputable section

open LocalClassFieldTheory


open AlgebraicNumberTheory.Valuations
open HilbertRamification

universe u v

variable
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]

/-- The wrapper completion at an infinite place as a `K`-algebra
equivalence with the underlying absolute-value completion. -/
def infinitePlaceCompletionAlgEquiv
    (w : InfinitePlace K) :
    w.Completion ≃ₐ[K] w.1.Completion where
  __ := InfinitePlace.Completion.equiv w
  commutes' _ := rfl

omit [NumberField L] in
/-- The canonical comparisons from concrete infinite-place completions to
absolute-value completions commute with the completion maps in a tower of
number fields. -/
theorem infinitePlaceCompletionAlgEquiv_algebraMap
    (v : InfinitePlace K) (w : InfinitePlace L)
    (hw : w.comap (algebraMap K L) = v) :
    letI : w.1.LiesOver v.1 :=
      ⟨congrArg (fun q : InfinitePlace K => q.1) hw⟩
    let u : AbsoluteValueExtension v.1 L :=
      ⟨w.1, fun x =>
        congrArg (fun q : InfinitePlace K => q.1 x) hw⟩
    letI : Algebra v.1.Completion u.1.Completion :=
      AbsoluteValue.completionAlgebra v.1 u.1 u.2
    RingHom.comp
        (algebraMap v.1.Completion u.1.Completion)
        (infinitePlaceCompletionAlgEquiv v).toRingEquiv =
      RingHom.comp
        (infinitePlaceCompletionAlgEquiv w).toRingEquiv
        (algebraMap v.Completion w.Completion) := by
  let : w.1.LiesOver v.1 :=
    ⟨congrArg (fun q : InfinitePlace K => q.1) hw⟩
  let u : AbsoluteValueExtension v.1 L :=
    ⟨w.1, fun x =>
      congrArg (fun q : InfinitePlace K => q.1 x) hw⟩
  let : Algebra v.1.Completion u.1.Completion :=
    AbsoluteValue.completionAlgebra v.1 u.1 u.2
  ext x
  refine InfinitePlace.Completion.induction_on v x ?_ ?_
  · exact
      isClosed_eq
        ((AbsoluteValue.completionMap_isometry
            v.1 w.1 u.2).continuous.comp
          (InfinitePlace.Completion.continuous_toCompletion v))
        ((InfinitePlace.Completion.continuous_toCompletion w).comp
          NumberField.LiesOver.continuous_completionMap)
  · intro y
    have hy :
        (y : v.1.Completion) =
          algebraMap K v.1.Completion
            (WithAbs.equiv v.1 y) := by
      rw [← AbsoluteValue.toCompletion_eq_algebraMap]
      simp
    change
      AbsoluteValue.completionMap v.1 u.1 u.2
          (y : v.1.Completion) =
        (NumberField.LiesOver.completionMap
          (v := v) (w := w)
          (y : v.Completion)).toCompletion
    rw [NumberField.LiesOver.completionMap_coe]
    rw [hy, AbsoluteValue.completionMap_coe]
    rfl

/-- Base change of the first tensor factor from the concrete
archimedean completion to the absolute-value completion. -/
noncomputable def infinitePlaceLocalTensorAlgEquiv
    (w : InfinitePlace K) :
    w.Completion ⊗[K] L ≃ₐ[K]
      LocalTensorAlgebra (L := L) w.1 :=
  Algebra.TensorProduct.congr
    (infinitePlaceCompletionAlgEquiv w)
    (AlgEquiv.refl : L ≃ₐ[K] L)

omit [NumberField K] [NumberField L] [FiniteDimensional K L] in
/-- The concrete-to-absolute completion comparison acts componentwise
on a pure tensor. -/
@[simp]
theorem infinitePlaceLocalTensorAlgEquiv_tmul
    (w : InfinitePlace K) (a : w.Completion) (x : L) :
    infinitePlaceLocalTensorAlgEquiv
        (K := K) (L := L) w (a ⊗ₜ[K] x) =
      infinitePlaceCompletionAlgEquiv w a ⊗ₜ[K] x := by
  rfl

/-- The induced multiplicative equivalence on local tensor units. -/
noncomputable def infinitePlaceLocalTensorUnitsEquiv
    (w : InfinitePlace K) :
    (w.Completion ⊗[K] L)ˣ ≃*
      (LocalTensorAlgebra (L := L) w.1)ˣ :=
  Units.mapEquiv
    (infinitePlaceLocalTensorAlgEquiv
      (K := K) (L := L) w).toMulEquiv

omit [NumberField K] [NumberField L] [FiniteDimensional K L] in
/-- Completion comparison commutes with conjugation on the second
tensor factor. -/
theorem infinitePlaceLocalTensorAlgEquiv_conjugation
    (w : InfinitePlace K)
    (σ : L ≃ₐ[K] L)
    (z : w.Completion ⊗[K] L) :
    infinitePlaceLocalTensorAlgEquiv
        (K := K) (L := L) w
        (scalarTensorConjugation
          (K := K) (L := L)
          (A := w.Completion) σ z) =
      localTensorConjugation
        (K := K) (L := L) w.1 σ
        (infinitePlaceLocalTensorAlgEquiv
          (K := K) (L := L) w z) := by
  induction z using TensorProduct.inductionOn with
  | tmul a x => rfl
  | add x y hx hy => simp [hx, hy]

omit [NumberField K] [NumberField L] [FiniteDimensional K L] in
/-- The completion comparison on units is equivariant. -/
theorem infinitePlaceLocalTensorUnitsEquiv_smul
    (w : InfinitePlace K)
    (σ : L ≃ₐ[K] L)
    (z : (w.Completion ⊗[K] L)ˣ) :
    letI := scalarTensorUnitsAction
      (K := K) (L := L) (A := w.Completion)
    letI := localTensorUnitsAction
      (K := K) (L := L) w.1
    infinitePlaceLocalTensorUnitsEquiv
        (K := K) (L := L) w (σ • z) =
      σ • infinitePlaceLocalTensorUnitsEquiv
        (K := K) (L := L) w z := by
  let := scalarTensorUnitsAction
    (K := K) (L := L) (A := w.Completion)
  let := localTensorUnitsAction
    (K := K) (L := L) w.1
  apply Units.ext
  exact infinitePlaceLocalTensorAlgEquiv_conjugation
    (K := K) (L := L) w σ
      (z : w.Completion ⊗[K] L)

section Galois

variable [IsGalois K L]

/-- The local tensor decomposition for the actual archimedean component type used by the
relative idele restricted product. -/
noncomputable def
    infinitePlaceTensorUnitsEquivLocalPlaceBlock
    (w : InfinitePlace K)
    (hw : w.1.IsNontrivial)
    (u : AbsoluteValueExtension w.1 L) :
    letI :=
      decompositionGroupLocalUnitsAction w.1 hw u
    letI hK :=
      AbsoluteValue.extensionCompletionAlgebra
        (K := K) u.1
    letI : SMul K u.1.Completion := hK.toSMul
    letI :=
      AbsoluteValue.completionAlgebra
        w.1 u.1 u.2
    letI : ∀ u' : AbsoluteValueExtension w.1 L,
        Algebra w.1.Completion u'.1.Completion :=
      fun u' =>
        AbsoluteValue.completionAlgebra
          w.1 u'.1 u'.2
    (w.Completion ⊗[K] L)ˣ ≃*
      LocalPlaceBlock w.1 hw u := by
  letI :=
    decompositionGroupLocalUnitsAction w.1 hw u
  letI hK :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K) u.1
  letI : SMul K u.1.Completion := hK.toSMul
  letI :=
    AbsoluteValue.completionAlgebra
      w.1 u.1 u.2
  letI : ∀ u' : AbsoluteValueExtension w.1 L,
      Algebra w.1.Completion u'.1.Completion :=
    fun u' =>
      AbsoluteValue.completionAlgebra
        w.1 u'.1 u'.2
  exact
    (infinitePlaceLocalTensorUnitsEquiv
      (K := K) (L := L) w).trans
      (localTensorUnitsEquivLocalPlaceBlock
        w.1 hw u)

section Equivariance

variable
    (w : InfinitePlace K)
    (hw : w.1.IsNontrivial)
    (u : AbsoluteValueExtension w.1 L)

local instance infinitePlaceExtensionCompletionAlgebra :
    Algebra K u.1.Completion :=
  AbsoluteValue.extensionCompletionAlgebra (K := K) u.1

local instance infinitePlaceExtensionCompletionSMul :
    SMul K u.1.Completion :=
  infinitePlaceExtensionCompletionAlgebra w u |>.toSMul

local instance infinitePlaceLocalizedCompletionAlgebra :
    Algebra w.1.Completion u.1.Completion :=
  AbsoluteValue.completionAlgebra w.1 u.1 u.2

local instance infinitePlaceAllCompletionAlgebra
    (u' : AbsoluteValueExtension w.1 L) :
    Algebra w.1.Completion u'.1.Completion :=
  AbsoluteValue.completionAlgebra w.1 u'.1 u'.2

local instance infinitePlaceScalarTensorUnitsAction :
    MulDistribMulAction (L ≃ₐ[K] L) (w.Completion ⊗[K] L)ˣ :=
  scalarTensorUnitsAction (K := K) (L := L) (A := w.Completion)

local instance infinitePlaceLocalTensorUnitsAction :
    MulDistribMulAction
      (L ≃ₐ[K] L)
      (LocalTensorAlgebra (L := L) w.1)ˣ :=
  localTensorUnitsAction (K := K) (L := L) w.1

omit [NumberField K] [NumberField L] in
/-- The actual archimedean local tensor equivalence is equivariant for the
full Galois action. -/
theorem
    infinitePlaceTensorUnitsEquivLocalPlaceBlock_smul
    (σ : L ≃ₐ[K] L)
    (z : (w.Completion ⊗[K] L)ˣ) :
    letI :=
      decompositionGroupLocalUnitsAction w.1 hw u
    infinitePlaceTensorUnitsEquivLocalPlaceBlock
        (K := K) (L := L) w hw u (σ • z) =
      σ •
        infinitePlaceTensorUnitsEquivLocalPlaceBlock
          (K := K) (L := L) w hw u z := by
  let :=
    decompositionGroupLocalUnitsAction w.1 hw u
  have hsource :
      infinitePlaceLocalTensorUnitsEquiv
          (K := K) (L := L) w (σ • z) =
        σ • infinitePlaceLocalTensorUnitsEquiv
          (K := K) (L := L) w z :=
    infinitePlaceLocalTensorUnitsEquiv_smul
      (K := K) (L := L) w σ z
  calc
    infinitePlaceTensorUnitsEquivLocalPlaceBlock
        (K := K) (L := L) w hw u (σ • z) =
      localTensorUnitsEquivLocalPlaceBlock w.1 hw u
        (σ • infinitePlaceLocalTensorUnitsEquiv
          (K := K) (L := L) w z) :=
      congrArg
        (localTensorUnitsEquivLocalPlaceBlock w.1 hw u)
        hsource
    _ =
      σ • infinitePlaceTensorUnitsEquivLocalPlaceBlock
        (K := K) (L := L) w hw u z :=
      localTensorUnitsEquivLocalPlaceBlock_smul
        w.1 hw u σ
        (infinitePlaceLocalTensorUnitsEquiv
          (K := K) (L := L) w z)

end Equivariance

end Galois
