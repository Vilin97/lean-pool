/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.OutsideIntegralInduced.ChosenPlaceAction
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Adele.FinitePlaceTensorBlock
/-!
# The chosen integral tensor equivalence

This file constructs the equivalence between the chosen integral tensor block
and the induced module of chosen local integer units.
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

/-- Outside a finite exceptional set, the actual integral tensor-unit
subgroup at a finite place is the induced module of the
integer units at the chosen extension. -/
noncomputable def
    relativeLocalTensorDecompositionIntegralUnitSubgroupEquivInducedIntegerUnits
    (w₀ : HeightOneSpectrum (𝓞 K)) :
    relativeLocalTensorDecompositionIntegralUnitSubgroup
        (K := K) (L := L) w₀ ≃*
      ChosenFinitePlaceInducedIntegerUnits
        (K := K) (L := L) w₀ :=
  by
    letI : MulDistribMulAction
        (absoluteValueDecompositionGroup K
          (chosenFinitePlaceExtension (L := L) w₀).1)
        𝒪[ChosenFinitePlaceLocalizedCompletion
          (K := K) (L := L) w₀]ˣ :=
      chosenFinitePlaceDecompositionGroupIntegerUnitsAction
        (K := K) (L := L) w₀
    exact
      (relativeLocalTensorDecompositionIntegralUnitSubgroupEquivPiUnits
        (K := K) (L := L) w₀).trans
        (completionProductIntegerUnitsEquivInducedModule
          (K := K) (L := L)
          (HeightOneSpectrum.adicAbv K w₀)
          (RayClass.adicAbv_isNontrivial w₀)
          (HeightOneSpectrum.isNonarchimedean_adicAbv K w₀)
          (chosenFinitePlaceExtension (L := L) w₀))
end ChosenFinitePlace
