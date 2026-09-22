/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.OutsideIntegralInduced.LocalInduction.Spine
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.OutsideIntegralInduced.LocalInduction.Action
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.OutsideIntegralInduced.LocalInduction.Equiv
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.OutsideIntegralInduced.LocalInduction.Inclusion
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.Decomposition
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Completion.ChosenLocalization
/-!
# The action at a chosen finite place

This file exposes the decomposition-group action and the direct local
cohomology endpoint used by the integral induced-block construction. Keeping
this localization boundary in a lower leaf prevents downstream transport
proofs from elaborating it together with the tensor-block API.
-/

open scoped NumberField ValuativeRel NNReal
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

/-- The decomposition group at the chosen extension of a finite place. -/
abbrev ChosenFinitePlaceDecompositionGroup
    (w₀ : HeightOneSpectrum (𝓞 K)) :=
  absoluteValueDecompositionGroup K
    (chosenFinitePlaceExtension (L := L) w₀).1

/-- Integer units in the chosen localized completion. -/
abbrev ChosenFinitePlaceLocalizedIntegerUnits
    (w₀ : HeightOneSpectrum (𝓞 K)) :=
  𝒪[ChosenFinitePlaceLocalizedCompletion
    (K := K) (L := L) w₀]ˣ

/-- Field units in the chosen localized completion. -/
abbrev ChosenFinitePlaceLocalizedFieldUnits
    (w₀ : HeightOneSpectrum (𝓞 K)) :=
  (ChosenFinitePlaceLocalizedCompletion
    (K := K) (L := L) w₀)ˣ

/-- The decomposition-group action on the chosen local integer units.

The named action is the boundary at which dependent induced-module
declarations stop expanding the chosen-localization construction. -/
@[implicit_reducible]
noncomputable def
    chosenFinitePlaceDecompositionGroupIntegerUnitsAction
    (w₀ : HeightOneSpectrum (𝓞 K)) :
    MulDistribMulAction
      (ChosenFinitePlaceDecompositionGroup
        (K := K) (L := L) w₀)
      (ChosenFinitePlaceLocalizedIntegerUnits
        (K := K) (L := L) w₀) :=
  decompositionGroupLocalizedIntegerUnitsAction
    (vK := HeightOneSpectrum.adicAbv K w₀)
    (hvK := RayClass.adicAbv_isNontrivial w₀)
    (hvKna :=
      HeightOneSpectrum.isNonarchimedean_adicAbv K w₀)
    (w := chosenFinitePlaceExtension (L := L) w₀)

/-- The decomposition-group action on the chosen local field units. -/
@[implicit_reducible]
noncomputable def chosenFinitePlaceDecompositionGroupLocalUnitsAction
    (w₀ : HeightOneSpectrum (𝓞 K)) :
    MulDistribMulAction
      (ChosenFinitePlaceDecompositionGroup
        (K := K) (L := L) w₀)
      (ChosenFinitePlaceLocalizedFieldUnits
        (K := K) (L := L) w₀) :=
  decompositionGroupLocalUnitsAction
    (HeightOneSpectrum.adicAbv K w₀)
    (RayClass.adicAbv_isNontrivial w₀)
    (chosenFinitePlaceExtension (L := L) w₀)

/-- The induced module of integer units at the chosen finite place. -/
abbrev ChosenFinitePlaceInducedIntegerUnits
    (w₀ : HeightOneSpectrum (𝓞 K)) :=
  @InducedModule
    (G := L ≃ₐ[K] L)
    (B := ChosenFinitePlaceLocalizedIntegerUnits
      (K := K) (L := L) w₀)
    inferInstance
    (ChosenFinitePlaceDecompositionGroup
      (K := K) (L := L) w₀)
    inferInstance
    (chosenFinitePlaceDecompositionGroupIntegerUnitsAction
      (K := K) (L := L) w₀)

/-- The local multiplicative block attached to the chosen finite place. -/
abbrev ChosenFinitePlaceLocalPlaceBlock
    (w₀ : HeightOneSpectrum (𝓞 K)) :=
  LocalPlaceBlock
    (HeightOneSpectrum.adicAbv K w₀)
    (RayClass.adicAbv_isNontrivial w₀)
    (chosenFinitePlaceExtension (L := L) w₀)

/-- The global action on the chosen induced integer-unit block. -/
@[implicit_reducible]
noncomputable def chosenFinitePlaceInducedIntegerUnitsAction
    (w₀ : HeightOneSpectrum (𝓞 K)) :
    MulDistribMulAction (L ≃ₐ[K] L)
      (ChosenFinitePlaceInducedIntegerUnits
        (K := K) (L := L) w₀) := by
  letI : MulDistribMulAction
      (ChosenFinitePlaceDecompositionGroup
        (K := K) (L := L) w₀)
      (ChosenFinitePlaceLocalizedIntegerUnits
        (K := K) (L := L) w₀) :=
    chosenFinitePlaceDecompositionGroupIntegerUnitsAction
      (K := K) (L := L) w₀
  exact inducedMulDistribMulAction
    (ChosenFinitePlaceDecompositionGroup
      (K := K) (L := L) w₀)

/-- The global action on the chosen local multiplicative block. -/
@[implicit_reducible]
noncomputable def chosenFinitePlaceLocalPlaceBlockAction
    (w₀ : HeightOneSpectrum (𝓞 K)) :
    MulDistribMulAction (L ≃ₐ[K] L)
      (ChosenFinitePlaceLocalPlaceBlock
        (K := K) (L := L) w₀) := by
  letI : MulDistribMulAction
      (ChosenFinitePlaceDecompositionGroup
        (K := K) (L := L) w₀)
      (ChosenFinitePlaceLocalizedFieldUnits
        (K := K) (L := L) w₀) :=
    chosenFinitePlaceDecompositionGroupLocalUnitsAction
      (K := K) (L := L) w₀
  exact inducedMulDistribMulAction
    (ChosenFinitePlaceDecompositionGroup
      (K := K) (L := L) w₀)

omit [NumberField L] in
/-- On the actual chosen localization, the decomposition-group action on
integer units is the pullback of the local Galois action along the canonical
decomposition equivalence. Both sides are evaluated with the valued-field
and integral-closure data used by `LocalInduction`. -/
theorem
    chosenFinitePlaceDecompositionGroupIntegerUnitsAction_smul_eq_pullback
    (w₀ : HeightOneSpectrum (𝓞 K)) :
    let vK := HeightOneSpectrum.adicAbv K w₀
    let w := chosenFinitePlaceExtension (L := L) w₀
    let E := ChosenFinitePlaceLocalizedCompletion
      (K := K) (L := L) w₀
    let eLocal :=
      decompositionGroupEquivAlgebraicLocalizationAut
        vK
        (RayClass.adicAbv_isNontrivial w₀)
        w
    letI : MulDistribMulAction
        (Gal(E/vK.Completion)) 𝒪[E]ˣ :=
      galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure
        vK.Completion E
    ∀ (σ : absoluteValueDecompositionGroup K w.1)
      (x : 𝒪[E]ˣ),
      (chosenFinitePlaceDecompositionGroupIntegerUnitsAction
        (K := K) (L := L) w₀).smul σ x =
        (MulDistribMulAction.compHom
          𝒪[E]ˣ eLocal.toMonoidHom).smul σ x := by
  unfold chosenFinitePlaceDecompositionGroupIntegerUnitsAction
  dsimp
  intro σ x
  rfl

omit [NumberField L] in
/-- The actual completion selected over a finite place has trivial low-degree
Herbrand cohomology on its integer units whenever that local extension is
unramified. All valued-local-field and integer-ring structures here are the
canonical instances exported by `ChosenLocalization`. -/
theorem chosenFinitePlaceLocalizedIntegerUnits_unramifiedHerbrand_subsingleton
    (w₀ : HeightOneSpectrum (𝓞 K))
    (g : Gal(
      ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) w₀/ChosenFinitePlaceBaseCompletion (K := K) w₀))
    (hg : ∀ τ : Gal(
      ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) w₀/ChosenFinitePlaceBaseCompletion (K := K) w₀),
      τ ∈ Subgroup.zpowers g)
    (hunram : ChosenFinitePlaceIsUnramified
      (K := K) (L := L) w₀) :
    letI : MulDistribMulAction
        (Gal(
          ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) w₀/ChosenFinitePlaceBaseCompletion (K := K) w₀))
        𝒪[ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) w₀]ˣ :=
      galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure
        (ChosenFinitePlaceBaseCompletion (K := K) w₀)
        (ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) w₀)
    Subsingleton
        (HerbrandH0
          (Gal(
            ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) w₀/ChosenFinitePlaceBaseCompletion (K := K) w₀))
          𝒪[ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) w₀]ˣ) ∧
      Subsingleton
        (HerbrandHMinusOne
          (Gal(
            ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) w₀/ChosenFinitePlaceBaseCompletion (K := K) w₀))
          𝒪[ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) w₀]ˣ g) := by
  let vK := HeightOneSpectrum.adicAbv K w₀
  let E := ChosenFinitePlaceLocalizedCompletion
    (K := K) (L := L) w₀
  let :
      IsNonarchimedeanLocalField.IsUnramifiedValuedExtension
        vK.Completion E := by
    simpa [ChosenFinitePlaceIsUnramified] using hunram
  exact
    unramifiedLocalIntegerUnitsHerbrand_subsingleton
      vK.Completion E g hg

end ChosenFinitePlace
