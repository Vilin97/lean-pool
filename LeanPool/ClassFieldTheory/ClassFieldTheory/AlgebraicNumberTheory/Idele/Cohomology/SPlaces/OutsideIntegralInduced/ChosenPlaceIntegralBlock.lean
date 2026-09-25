/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.OutsideIntegralInduced.ChosenPlaceIntegralBlockInducedSmul
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.OutsideIntegralInduced.ChosenPlaceIntegralBlockTensorSmul
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.OutsideIntegralInduced.ChosenPlaceIntegralBlockEquivApply
/-!
# Equivariance facade for the integral induced block

This file combines the independent induced-block and tensor-block equivariance
lemmas into the transport used by the cohomology layer.
-/

@[expose] public section

open scoped NumberField TensorProduct ValuativeRel NNReal
open NumberField IsDedekindDomain

noncomputable section

open AlgebraicNumberTheory.Valuations
open HilbertRamification
open LocalClassFieldTheory
open LocalFieldTheory
open CyclicCohomology.ProfiniteCohomology.Herbrand
open CyclicCohomology

variable
    {K : Type} {L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

section ChosenFinitePlace

omit [NumberField L] in
/-- The integral tensor-to-induced-module equivalence is equivariant for
the full global Galois action. -/
theorem
    relativeLocalTensorDecompositionIntegralUnitSubgroupEquivInducedIntegerUnits_smul
    (w₀ : HeightOneSpectrum (𝓞 K))
    (τ : L ≃ₐ[K] L)
    (x : relativeLocalTensorDecompositionIntegralUnitSubgroup
      (K := K) (L := L) w₀) :
    letI :=
      relativeLocalTensorDecompositionIntegralUnitSubgroupAction
        (K := K) (L := L) w₀
    letI :=
      chosenFinitePlaceInducedIntegerUnitsAction
        (K := K) (L := L) w₀
    relativeLocalTensorDecompositionIntegralUnitSubgroupEquivInducedIntegerUnits
        (K := K) (L := L) w₀ (τ • x) =
      τ •
        (relativeLocalTensorDecompositionIntegralUnitSubgroupEquivInducedIntegerUnits
          (K := K) (L := L) w₀ x) := by
  let :=
    relativeLocalTensorDecompositionIntegralUnitSubgroupAction
      (K := K) (L := L) w₀
  let :=
    chosenFinitePlaceInducedIntegerUnitsAction
      (K := K) (L := L) w₀
  let :=
    chosenFinitePlaceLocalPlaceBlockAction
      (K := K) (L := L) w₀
  apply
    chosenFinitePlaceIntegralInducedBlockToLocalPlaceBlock_injective
      (K := K) (L := L) w₀
  calc
    chosenFinitePlaceIntegralInducedBlockToLocalPlaceBlock
          (K := K) (L := L) w₀
          (relativeLocalTensorDecompositionIntegralUnitSubgroupEquivInducedIntegerUnits
            (K := K) (L := L) w₀
            ((relativeLocalTensorDecompositionIntegralUnitSubgroupAction
              (K := K) (L := L) w₀).smul τ x)) =
        finitePlaceTensorUnitsEquivLocalPlaceBlock
          (K := K) (L := L) w₀
          (chosenFinitePlaceExtension (L := L) w₀)
          (((relativeLocalTensorDecompositionIntegralUnitSubgroupAction
              (K := K) (L := L) w₀).smul τ x :
              relativeLocalTensorDecompositionIntegralUnitSubgroup
                (K := K) (L := L) w₀) :
            (w₀.adicCompletion K ⊗[K] L)ˣ) :=
      chosenFinitePlaceIntegralInducedBlockToLocalPlaceBlock_equiv_apply
        (K := K) (L := L) w₀
        ((relativeLocalTensorDecompositionIntegralUnitSubgroupAction
          (K := K) (L := L) w₀).smul τ x)
    _ =
        (chosenFinitePlaceLocalPlaceBlockAction
          (K := K) (L := L) w₀).smul τ
          (finitePlaceTensorUnitsEquivLocalPlaceBlock
            (K := K) (L := L) w₀
            (chosenFinitePlaceExtension (L := L) w₀)
            (x : (w₀.adicCompletion K ⊗[K] L)ˣ)) :=
      finitePlaceTensorUnitsEquivLocalPlaceBlock_restricted_smul
        (K := K) (L := L) w₀ τ x
    _ =
        (chosenFinitePlaceLocalPlaceBlockAction
          (K := K) (L := L) w₀).smul τ
          (chosenFinitePlaceIntegralInducedBlockToLocalPlaceBlock
            (K := K) (L := L) w₀
            (relativeLocalTensorDecompositionIntegralUnitSubgroupEquivInducedIntegerUnits
              (K := K) (L := L) w₀ x)) :=
      congrArg
        (fun z :
            ChosenFinitePlaceLocalPlaceBlock
              (K := K) (L := L) w₀ =>
          (chosenFinitePlaceLocalPlaceBlockAction
            (K := K) (L := L) w₀).smul τ z)
        (chosenFinitePlaceIntegralInducedBlockToLocalPlaceBlock_equiv_apply
          (K := K) (L := L) w₀ x).symm
    _ =
        chosenFinitePlaceIntegralInducedBlockToLocalPlaceBlock
          (K := K) (L := L) w₀
          ((chosenFinitePlaceInducedIntegerUnitsAction
            (K := K) (L := L) w₀).smul τ
            (relativeLocalTensorDecompositionIntegralUnitSubgroupEquivInducedIntegerUnits
              (K := K) (L := L) w₀ x)) :=
      (chosenFinitePlaceIntegralInducedBlockToLocalPlaceBlock_smul
        (K := K) (L := L) w₀ τ
        (relativeLocalTensorDecompositionIntegralUnitSubgroupEquivInducedIntegerUnits
          (K := K) (L := L) w₀ x)).symm

end ChosenFinitePlace
