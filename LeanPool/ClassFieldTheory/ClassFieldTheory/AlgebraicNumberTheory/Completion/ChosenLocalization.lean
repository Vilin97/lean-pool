/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Completion.LocalizedValuation
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.NormApproximation.FinitePlaces
/-!
# The chosen localization at a finite place

This file equips the actual chosen localization of a finite number-field
extension with its canonical valued local-field structures. It also defines
unramifiedness for that actual completed extension.
-/

open scoped NumberField ValuativeRel NNReal
open NumberField IsDedekindDomain

noncomputable section

open AlgebraicNumberTheory.Valuations
open LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

open scoped Classical in
/-- The completion of the base field at the chosen finite place. -/
abbrev ChosenFinitePlaceBaseCompletion
    (w₀ : HeightOneSpectrum (𝓞 K)) :=
  (HeightOneSpectrum.adicAbv K w₀).Completion

open scoped Classical in
noncomputable instance chosenFinitePlaceExtensionCompletionAlgebra
    (w₀ : HeightOneSpectrum (𝓞 K)) :
    Algebra K
      (chosenFinitePlaceExtension (L := L) w₀).1.Completion :=
  AbsoluteValue.extensionCompletionAlgebra
    (K := K) (chosenFinitePlaceExtension (L := L) w₀).1

open scoped Classical in
noncomputable instance chosenFinitePlaceExtensionCompletionSMul
    (w₀ : HeightOneSpectrum (𝓞 K)) :
    SMul K
      (chosenFinitePlaceExtension (L := L) w₀).1.Completion :=
  (chosenFinitePlaceExtensionCompletionAlgebra
    (K := K) (L := L) w₀).toSMul

open scoped Classical in
noncomputable instance chosenFinitePlaceCompletionAlgebra
    (w₀ : HeightOneSpectrum (𝓞 K)) :
    Algebra
      (ChosenFinitePlaceBaseCompletion (K := K) w₀)
      (chosenFinitePlaceExtension (L := L) w₀).1.Completion :=
  AbsoluteValue.completionAlgebra
    (HeightOneSpectrum.adicAbv K w₀)
    (chosenFinitePlaceExtension (L := L) w₀).1
    (chosenFinitePlaceExtension (L := L) w₀).2

open scoped Classical in
noncomputable instance chosenFinitePlaceBaseValued
    (w₀ : HeightOneSpectrum (𝓞 K)) :
    Valued
      (ChosenFinitePlaceBaseCompletion (K := K) w₀) ℝ≥0 :=
  finitePlaceCompletionValued
    (HeightOneSpectrum.adicAbv K w₀)
    (HeightOneSpectrum.isNonarchimedean_adicAbv K w₀)

open scoped Classical in
noncomputable instance chosenFinitePlaceBaseValuativeRel
    (w₀ : HeightOneSpectrum (𝓞 K)) :
    ValuativeRel
      (ChosenFinitePlaceBaseCompletion (K := K) w₀) :=
  finitePlaceCompletionValuativeRel
    (HeightOneSpectrum.adicAbv K w₀)
    (HeightOneSpectrum.isNonarchimedean_adicAbv K w₀)

open scoped Classical in
noncomputable instance chosenFinitePlaceLocalizedValued
    (w₀ : HeightOneSpectrum (𝓞 K)) :
    Valued
      (ChosenFinitePlaceLocalizedCompletion
        (K := K) (L := L) w₀) ℝ≥0 :=
  localizedCompletionFinitePlaceValued
    (HeightOneSpectrum.adicAbv K w₀)
    (chosenFinitePlaceExtension (L := L) w₀)
    (HeightOneSpectrum.isNonarchimedean_adicAbv K w₀)

open scoped Classical in
noncomputable instance chosenFinitePlaceLocalizedValuativeRel
    (w₀ : HeightOneSpectrum (𝓞 K)) :
    ValuativeRel
      (ChosenFinitePlaceLocalizedCompletion
        (K := K) (L := L) w₀) :=
  localizedCompletionFinitePlaceValuativeRel
    (HeightOneSpectrum.adicAbv K w₀)
    (chosenFinitePlaceExtension (L := L) w₀)
    (HeightOneSpectrum.isNonarchimedean_adicAbv K w₀)

open scoped Classical in
noncomputable instance
    chosenFinitePlaceLocalizedValuationHasExtension
    (w₀ : HeightOneSpectrum (𝓞 K)) :
    Valuation.HasExtension
      (ValuativeRel.valuation
        (ChosenFinitePlaceBaseCompletion (K := K) w₀))
      (ValuativeRel.valuation
        (ChosenFinitePlaceLocalizedCompletion
          (K := K) (L := L) w₀)) :=
  localizedCompletionValuationHasExtension
    (HeightOneSpectrum.adicAbv K w₀)
    (chosenFinitePlaceExtension (L := L) w₀)
    (HeightOneSpectrum.isNonarchimedean_adicAbv K w₀)

open scoped Classical in
noncomputable instance chosenFinitePlaceLocalizedIntegerAlgebra
    (w₀ : HeightOneSpectrum (𝓞 K)) :
    Algebra
      𝒪[ChosenFinitePlaceBaseCompletion (K := K) w₀]
      (ChosenFinitePlaceLocalizedCompletion
        (K := K) (L := L) w₀) :=
  Algebra.ofSubsemiring
    𝒪[ChosenFinitePlaceBaseCompletion (K := K) w₀]

open scoped Classical in
noncomputable instance chosenFinitePlaceLocalizedIsIntegralClosure
    (w₀ : HeightOneSpectrum (𝓞 K)) :
    IsIntegralClosure
      𝒪[ChosenFinitePlaceLocalizedCompletion
        (K := K) (L := L) w₀]
      𝒪[ChosenFinitePlaceBaseCompletion (K := K) w₀]
      (ChosenFinitePlaceLocalizedCompletion
        (K := K) (L := L) w₀) :=
  localizedCompletionIsIntegralClosureWithExtension
    (HeightOneSpectrum.adicAbv K w₀)
    (chosenFinitePlaceExtension (L := L) w₀)
    (RayClass.adicAbv_isNontrivial w₀)
    (HeightOneSpectrum.isNonarchimedean_adicAbv K w₀)

open scoped Classical in
noncomputable instance
    chosenFinitePlaceBaseNontriviallyNormedField
    (w₀ : HeightOneSpectrum (𝓞 K)) :
    NontriviallyNormedField
      (ChosenFinitePlaceBaseCompletion (K := K) w₀) :=
  absoluteValueExtensionCompletionNontriviallyNormedField
    (HeightOneSpectrum.adicAbv K w₀)
    (RayClass.adicAbv_isNontrivial w₀)

open scoped Classical in
noncomputable instance chosenFinitePlaceBaseLocallyCompactSpace
    (w₀ : HeightOneSpectrum (𝓞 K)) :
    LocallyCompactSpace
      (ChosenFinitePlaceBaseCompletion (K := K) w₀) :=
  AbsoluteValue.Completion.locallyCompactSpace
    (finitePlaceCompletionBaseMap_isometry w₀)

open scoped Classical in
noncomputable instance chosenFinitePlaceBaseIsUltrametricDist
    (w₀ : HeightOneSpectrum (𝓞 K)) :
    IsUltrametricDist
      (ChosenFinitePlaceBaseCompletion (K := K) w₀) :=
  completionIsUltrametricDist
    (HeightOneSpectrum.adicAbv K w₀)
    (HeightOneSpectrum.isNonarchimedean_adicAbv K w₀)

open scoped Classical in
noncomputable instance
    chosenFinitePlaceBaseValuationIsNontrivial
    (w₀ : HeightOneSpectrum (𝓞 K)) :
    (Valued.v :
      Valuation
        (ChosenFinitePlaceBaseCompletion (K := K) w₀)
        ℝ≥0).IsNontrivial :=
  (inferInstance :
    (NormedField.valuation
      (K := ChosenFinitePlaceBaseCompletion (K := K) w₀)).IsNontrivial)

open scoped Classical in
noncomputable instance chosenFinitePlaceBaseValuationCompatible
    (w₀ : HeightOneSpectrum (𝓞 K)) :
    (Valued.v :
      Valuation
        (ChosenFinitePlaceBaseCompletion (K := K) w₀)
        ℝ≥0).Compatible :=
  Valuation.Compatible.ofValuation _

open scoped Classical in
noncomputable instance
    chosenFinitePlaceBaseValuativeRelIsNontrivial
    (w₀ : HeightOneSpectrum (𝓞 K)) :
    ValuativeRel.IsNontrivial
      (ChosenFinitePlaceBaseCompletion (K := K) w₀) :=
  (ValuativeRel.isNontrivial_iff_isNontrivial
    (Valued.v :
      Valuation
        (ChosenFinitePlaceBaseCompletion (K := K) w₀)
        ℝ≥0)).2 inferInstance

open scoped Classical in
noncomputable instance chosenFinitePlaceBaseIsValuativeTopology
    (w₀ : HeightOneSpectrum (𝓞 K)) :
    IsValuativeTopology
      (ChosenFinitePlaceBaseCompletion (K := K) w₀) :=
  isValuativeTopology_of_valued_ofValuation
    (ChosenFinitePlaceBaseCompletion (K := K) w₀) ℝ≥0

open scoped Classical in
noncomputable instance
    chosenFinitePlaceBaseIsNonarchimedeanLocalField
    (w₀ : HeightOneSpectrum (𝓞 K)) :
    IsNonarchimedeanLocalField
      (ChosenFinitePlaceBaseCompletion (K := K) w₀) :=
  { toIsValuativeTopology := inferInstance
    toLocallyCompactSpace := inferInstance
    toIsNontrivial := inferInstance }

open scoped Classical in
noncomputable instance chosenFinitePlaceCompletionFiniteDimensional
    (w₀ : HeightOneSpectrum (𝓞 K)) :
    FiniteDimensional
      (ChosenFinitePlaceBaseCompletion (K := K) w₀)
      (chosenFinitePlaceExtension (L := L) w₀).1.Completion :=
  completionModuleFinite
    (HeightOneSpectrum.adicAbv K w₀)
    (RayClass.adicAbv_isNontrivial w₀)
    (chosenFinitePlaceExtension (L := L) w₀)

open scoped Classical in
noncomputable instance chosenFinitePlaceCompletionContinuousSMul
    (w₀ : HeightOneSpectrum (𝓞 K)) :
    ContinuousSMul
      (ChosenFinitePlaceBaseCompletion (K := K) w₀)
      (chosenFinitePlaceExtension (L := L) w₀).1.Completion :=
  continuousSMul_of_algebraMap _ _
    (AbsoluteValue.completionMap_isometry
      (HeightOneSpectrum.adicAbv K w₀)
      (chosenFinitePlaceExtension (L := L) w₀).1
      (chosenFinitePlaceExtension (L := L) w₀).2).continuous

open scoped Classical in
noncomputable instance chosenFinitePlaceCompletionLocallyCompactSpace
    (w₀ : HeightOneSpectrum (𝓞 K)) :
    LocallyCompactSpace
      (chosenFinitePlaceExtension (L := L) w₀).1.Completion :=
  LocallyCompactSpace.of_finiteDimensional_of_complete
    (ChosenFinitePlaceBaseCompletion (K := K) w₀)
    (chosenFinitePlaceExtension (L := L) w₀).1.Completion

open scoped Classical in
noncomputable instance chosenFinitePlaceLocalizedFiniteDimensional
    (w₀ : HeightOneSpectrum (𝓞 K)) :
    FiniteDimensional
      (ChosenFinitePlaceBaseCompletion (K := K) w₀)
      (ChosenFinitePlaceLocalizedCompletion
        (K := K) (L := L) w₀) :=
  AlgebraicNumberTheory.Valuations.localizedCompletionModuleFinite
    (HeightOneSpectrum.adicAbv K w₀)
    (RayClass.adicAbv_isNontrivial w₀)
    (chosenFinitePlaceExtension (L := L) w₀)

open scoped Classical in
noncomputable instance chosenFinitePlaceLocalizedIsGalois
    (w₀ : HeightOneSpectrum (𝓞 K)) :
    IsGalois
      (ChosenFinitePlaceBaseCompletion (K := K) w₀)
      (ChosenFinitePlaceLocalizedCompletion
        (K := K) (L := L) w₀) :=
  HilbertRamification.algebraicLocalization_isGalois
    (HeightOneSpectrum.adicAbv K w₀)
    (chosenFinitePlaceExtension (L := L) w₀)

open scoped Classical in
noncomputable instance
    chosenFinitePlaceLocalizedLocallyCompactSpace
    (w₀ : HeightOneSpectrum (𝓞 K)) :
    LocallyCompactSpace
      (ChosenFinitePlaceLocalizedCompletion
        (K := K) (L := L) w₀) := by
  let e :
      ChosenFinitePlaceLocalizedCompletion
          (K := K) (L := L) w₀ ≃ᵢ
        (chosenFinitePlaceExtension (L := L) w₀).1.Completion :=
    { toEquiv :=
        (AlgebraicNumberTheory.Valuations.localizedCompletionEquivCompletion
          (HeightOneSpectrum.adicAbv K w₀)
          (RayClass.adicAbv_isNontrivial w₀)
          (chosenFinitePlaceExtension (L := L) w₀)).toEquiv
      isometry_toFun := Isometry.of_dist_eq fun _ _ => rfl }
  exact (e.toHomeomorph.locallyCompactSpace_iff).2 inferInstance

open scoped Classical in
noncomputable instance chosenFinitePlaceLocalizedIsUltrametricDist
    (w₀ : HeightOneSpectrum (𝓞 K)) :
    IsUltrametricDist
      (ChosenFinitePlaceLocalizedCompletion
        (K := K) (L := L) w₀) :=
  localizedCompletionIsUltrametricDist
    (HeightOneSpectrum.adicAbv K w₀)
    (chosenFinitePlaceExtension (L := L) w₀)
    (HeightOneSpectrum.isNonarchimedean_adicAbv K w₀)

open scoped Classical in
noncomputable instance chosenFinitePlaceLocalizedValuationCompatible
    (w₀ : HeightOneSpectrum (𝓞 K)) :
    (Valued.v :
      Valuation
        (ChosenFinitePlaceLocalizedCompletion
          (K := K) (L := L) w₀)
        ℝ≥0).Compatible :=
  Valuation.Compatible.ofValuation _

open scoped Classical in
noncomputable instance
    chosenFinitePlaceLocalizedValuationIsNontrivial
    (w₀ : HeightOneSpectrum (𝓞 K)) :
    (ValuativeRel.valuation
      (ChosenFinitePlaceLocalizedCompletion
        (K := K) (L := L) w₀)).IsNontrivial :=
  Valuation.IsNontrivial.of_hasExtension
    (ValuativeRel.valuation
      (ChosenFinitePlaceBaseCompletion (K := K) w₀))
    (ValuativeRel.valuation
      (ChosenFinitePlaceLocalizedCompletion
        (K := K) (L := L) w₀))

open scoped Classical in
noncomputable instance
    chosenFinitePlaceLocalizedValuativeRelIsNontrivial
    (w₀ : HeightOneSpectrum (𝓞 K)) :
    ValuativeRel.IsNontrivial
      (ChosenFinitePlaceLocalizedCompletion
        (K := K) (L := L) w₀) :=
  (ValuativeRel.isNontrivial_iff_isNontrivial
    (ValuativeRel.valuation
      (ChosenFinitePlaceLocalizedCompletion
        (K := K) (L := L) w₀))).2 inferInstance

open scoped Classical in
noncomputable instance chosenFinitePlaceLocalizedIsValuativeTopology
    (w₀ : HeightOneSpectrum (𝓞 K)) :
    IsValuativeTopology
      (ChosenFinitePlaceLocalizedCompletion
        (K := K) (L := L) w₀) :=
  isValuativeTopology_of_valued_ofValuation
    (ChosenFinitePlaceLocalizedCompletion
      (K := K) (L := L) w₀) ℝ≥0

open scoped Classical in
noncomputable instance
    chosenFinitePlaceLocalizedIsNonarchimedeanLocalField
    (w₀ : HeightOneSpectrum (𝓞 K)) :
    IsNonarchimedeanLocalField
      (ChosenFinitePlaceLocalizedCompletion
        (K := K) (L := L) w₀) :=
  { toIsValuativeTopology := inferInstance
    toLocallyCompactSpace := inferInstance
    toIsNontrivial := inferInstance }

open scoped Classical in
noncomputable instance chosenFinitePlaceLocalizedIntegerModuleFinite
    (w₀ : HeightOneSpectrum (𝓞 K)) :
    Module.Finite
      𝒪[ChosenFinitePlaceBaseCompletion (K := K) w₀]
      𝒪[ChosenFinitePlaceLocalizedCompletion
        (K := K) (L := L) w₀] := by
  let : Algebra.IsSeparable
      (ChosenFinitePlaceBaseCompletion (K := K) w₀)
      (ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) w₀) :=
    (chosenFinitePlaceLocalizedIsGalois (K := K) (L := L) w₀).to_isSeparable
  exact integerRing_moduleFinite_of_isIntegralClosure
    (ChosenFinitePlaceBaseCompletion (K := K) w₀)
    (ChosenFinitePlaceLocalizedCompletion
      (K := K) (L := L) w₀)

open scoped Classical in
/-- The chosen extension of the completed field is unramified, expressed
using the intrinsic valuation on the algebraic localization.  The canonical local-field
  instances for the chosen completion are exported
from this module, so clients only supply the mathematical unramifiedness
hypothesis. -/
noncomputable def ChosenFinitePlaceIsUnramified
    (w₀ : HeightOneSpectrum (𝓞 K)) : Prop :=
  IsNonarchimedeanLocalField.IsUnramifiedValuedExtension
    (ChosenFinitePlaceBaseCompletion (K := K) w₀)
    (ChosenFinitePlaceLocalizedCompletion
      (K := K) (L := L) w₀)
