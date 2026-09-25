/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.OutsideIntegralInduced.CompletionTransport
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalBlocks.Tensor
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.Valuation
/-!
# Shared completion spine for integral local induction

This file names the coherent algebra, valuation, and integral-closure
structures used by every integral local-induction leaf.
-/

@[expose] public section

open scoped NumberField TensorProduct ValuativeRel NNReal
open NumberField IsDedekindDomain

noncomputable section

open AlgebraicNumberTheory.Valuations
open HilbertRamification
open LocalClassFieldTheory
open LocalFieldTheory

variable
    {K : Type} {L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

namespace LocalInductionInternal

variable (vK : AbsoluteValue K ℝ)
    (w : AbsoluteValueExtension vK L)

/-- The base-field algebra structure on the chosen extension completion. -/
@[reducible]
noncomputable def extensionCompletionAlgebra :
    Algebra K w.1.Completion :=
  AbsoluteValue.extensionCompletionAlgebra (K := K) w.1

/-- The scalar action underlying `extensionCompletionAlgebra`. -/
@[reducible]
noncomputable def extensionCompletionSMul :
    SMul K w.1.Completion :=
  (extensionCompletionAlgebra vK w).toSMul

/-- The completed-base algebra structure on the chosen extension
completion. -/
@[reducible]
noncomputable def completionAlgebra :
    Algebra vK.Completion w.1.Completion :=
  AbsoluteValue.completionAlgebra vK w.1 w.2

/-- The canonical valued structure on the completed base place. -/
@[reducible]
noncomputable def baseValued
    (hvKna : IsNonarchimedean (vK : K → ℝ)) :
    Valued vK.Completion ℝ≥0 :=
  finitePlaceCompletionValued vK hvKna

/-- The canonical valuative relation on the completed base place. -/
@[reducible]
noncomputable def baseValuativeRel
    (hvKna : IsNonarchimedean (vK : K → ℝ)) :
    letI : Valued vK.Completion ℝ≥0 := baseValued vK hvKna
    ValuativeRel vK.Completion :=
  finitePlaceCompletionValuativeRel vK hvKna

/-- The canonical valued structure on the chosen localized completion. -/
@[reducible]
noncomputable def localizedValued
    (hvKna : IsNonarchimedean (vK : K → ℝ)) :
    Valued (LocalizedCompletion vK w) ℝ≥0 :=
  localizedCompletionFinitePlaceValued vK w hvKna

/-- The canonical valuative relation on the chosen localized completion. -/
@[reducible]
noncomputable def localizedValuativeRel
    (hvKna : IsNonarchimedean (vK : K → ℝ)) :
    letI : Valued (LocalizedCompletion vK w) ℝ≥0 :=
      localizedValued vK w hvKna
    ValuativeRel (LocalizedCompletion vK w) :=
  localizedCompletionFinitePlaceValuativeRel vK w hvKna

/-- The canonical algebra of the localized completion over the completed
base valuation ring. -/
@[reducible]
noncomputable def integerAlgebra
    (hvKna : IsNonarchimedean (vK : K → ℝ)) :
    letI := extensionCompletionAlgebra vK w
    letI : SMul K w.1.Completion := extensionCompletionSMul vK w
    letI := completionAlgebra vK w
    letI : Valued vK.Completion ℝ≥0 := baseValued vK hvKna
    letI : ValuativeRel vK.Completion := baseValuativeRel vK hvKna
    letI : Valued (LocalizedCompletion vK w) ℝ≥0 :=
      localizedValued vK w hvKna
    letI : ValuativeRel (LocalizedCompletion vK w) :=
      localizedValuativeRel vK w hvKna
    Algebra 𝒪[vK.Completion] (LocalizedCompletion vK w) := by
  letI := extensionCompletionAlgebra vK w
  letI : SMul K w.1.Completion := extensionCompletionSMul vK w
  letI := completionAlgebra vK w
  letI : Valued vK.Completion ℝ≥0 := baseValued vK hvKna
  letI : ValuativeRel vK.Completion := baseValuativeRel vK hvKna
  letI : Valued (LocalizedCompletion vK w) ℝ≥0 :=
    localizedValued vK w hvKna
  letI : ValuativeRel (LocalizedCompletion vK w) :=
    localizedValuativeRel vK w hvKna
  exact Algebra.ofSubsemiring 𝒪[vK.Completion]

omit [NumberField K] [NumberField L] [FiniteDimensional K L]
    [IsGalois K L] in
/-- The canonical valuation-extension certificate for the integral
local-induction completion pair. -/
theorem valuationHasExtension
    (hvKna : IsNonarchimedean (vK : K → ℝ)) :
    letI := extensionCompletionAlgebra vK w
    letI : SMul K w.1.Completion := extensionCompletionSMul vK w
    letI := completionAlgebra vK w
    letI : Valued vK.Completion ℝ≥0 := baseValued vK hvKna
    letI : ValuativeRel vK.Completion := baseValuativeRel vK hvKna
    letI : Valued (LocalizedCompletion vK w) ℝ≥0 :=
      localizedValued vK w hvKna
    letI : ValuativeRel (LocalizedCompletion vK w) :=
      localizedValuativeRel vK w hvKna
    Valuation.HasExtension
      (ValuativeRel.valuation vK.Completion)
      (ValuativeRel.valuation (LocalizedCompletion vK w)) :=
  localizedCompletionValuationHasExtension vK w hvKna

omit [NumberField K] [NumberField L] [IsGalois K L] in
/-- The canonical integral-closure certificate for the integral
local-induction completion pair. -/
theorem isIntegralClosure
    (hvK : vK.IsNontrivial)
    (hvKna : IsNonarchimedean (vK : K → ℝ)) :
    letI := extensionCompletionAlgebra vK w
    letI : SMul K w.1.Completion := extensionCompletionSMul vK w
    letI := completionAlgebra vK w
    letI : Valued vK.Completion ℝ≥0 := baseValued vK hvKna
    letI : ValuativeRel vK.Completion := baseValuativeRel vK hvKna
    letI : Valued (LocalizedCompletion vK w) ℝ≥0 :=
      localizedValued vK w hvKna
    letI : ValuativeRel (LocalizedCompletion vK w) :=
      localizedValuativeRel vK w hvKna
    letI : Algebra 𝒪[vK.Completion] (LocalizedCompletion vK w) :=
      integerAlgebra vK w hvKna
    letI := valuationHasExtension vK w hvKna
    IsIntegralClosure
      𝒪[LocalizedCompletion vK w]
      𝒪[vK.Completion]
      (LocalizedCompletion vK w) :=
  localizedCompletionIsIntegralClosureWithExtension
    vK w hvK hvKna

end LocalInductionInternal
