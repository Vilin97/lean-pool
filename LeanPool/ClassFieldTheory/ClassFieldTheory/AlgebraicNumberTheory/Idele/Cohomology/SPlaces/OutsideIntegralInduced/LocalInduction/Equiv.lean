/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.OutsideIntegralInduced.LocalInduction.Action
/-!
# Integral local induction equivalence

This leaf identifies the product of completed integer-unit groups with the
induced integer-unit module.
-/

@[expose] public section

open scoped NumberField TensorProduct ValuativeRel NNReal
open NumberField IsDedekindDomain

noncomputable
section

open AlgebraicNumberTheory.Valuations
open HilbertRamification
open LocalClassFieldTheory
open LocalFieldTheory

variable
    {K : Type} {L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

section IntegralInduction

variable (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (hvKna : IsNonarchimedean (vK : K → ℝ))
    (w : AbsoluteValueExtension vK L)

/-- The product of all local integer-unit groups from the canonical local tensor decomposition,
rewritten
as the induced integer-unit module at a chosen extension. -/
noncomputable def completionProductIntegerUnitsEquivInducedModule :
    letI := LocalInductionInternal.extensionCompletionAlgebra vK w
    letI : SMul K w.1.Completion :=
      LocalInductionInternal.extensionCompletionSMul vK w
    letI := LocalInductionInternal.completionAlgebra vK w
    letI : Valued vK.Completion ℝ≥0 :=
      LocalInductionInternal.baseValued vK hvKna
    letI : ValuativeRel vK.Completion :=
      LocalInductionInternal.baseValuativeRel vK hvKna
    letI : Valued (LocalizedCompletion vK w) ℝ≥0 :=
      LocalInductionInternal.localizedValued vK w hvKna
    letI : ValuativeRel (LocalizedCompletion vK w) :=
      LocalInductionInternal.localizedValuativeRel vK w hvKna
    letI := LocalInductionInternal.valuationHasExtension vK w hvKna
    letI := LocalInductionInternal.isIntegralClosure
      vK w hvK hvKna
    letI := decompositionGroupLocalizedIntegerUnitsAction
      (vK := vK) (hvK := hvK) (hvKna := hvKna) (w := w)
    (∀ w' : AbsoluteValueExtension vK L,
      (absoluteValueCompletionIntegers w'.1
        (absoluteValueExtension_isNonarchimedean
          vK hvKna w'))ˣ) ≃*
      CyclicCohomology.InducedModule
        (B := 𝒪[LocalizedCompletion vK w]ˣ)
        (absoluteValueDecompositionGroup K w.1) := by
  letI := LocalInductionInternal.extensionCompletionAlgebra vK w
  letI : SMul K w.1.Completion :=
    LocalInductionInternal.extensionCompletionSMul vK w
  letI := LocalInductionInternal.completionAlgebra vK w
  letI : Valued vK.Completion ℝ≥0 :=
    LocalInductionInternal.baseValued vK hvKna
  letI : ValuativeRel vK.Completion :=
    LocalInductionInternal.baseValuativeRel vK hvKna
  letI : Valued (LocalizedCompletion vK w) ℝ≥0 :=
    LocalInductionInternal.localizedValued vK w hvKna
  letI : ValuativeRel (LocalizedCompletion vK w) :=
    LocalInductionInternal.localizedValuativeRel vK w hvKna
  letI := LocalInductionInternal.valuationHasExtension vK w hvKna
  letI := LocalInductionInternal.isIntegralClosure
    vK w hvK hvKna
  letI := decompositionGroupLocalizedIntegerUnitsAction
    (vK := vK) (hvK := hvK) (hvKna := hvKna) (w := w)
  let reindex :=
    Equiv.piCongrLeft'
      (fun w' : AbsoluteValueExtension vK L =>
        (absoluteValueCompletionIntegers w'.1
          (absoluteValueExtension_isNonarchimedean
            vK hvKna w'))ˣ)
      (rightCosetExtensionEquiv vK hvK w).symm
  let reindexMul :
      (∀ w' : AbsoluteValueExtension vK L,
        (absoluteValueCompletionIntegers w'.1
          (absoluteValueExtension_isNonarchimedean
            vK hvKna w'))ˣ) ≃*
        (∀ q : InducedRightCosets
            (absoluteValueDecompositionGroup K w.1),
          (absoluteValueCompletionIntegers
            (rightCosetExtensionEquiv vK hvK w q).1
            (absoluteValueExtension_isNonarchimedean
              vK hvKna
              (rightCosetExtensionEquiv vK hvK w q)))ˣ) :=
    { reindex with
      map_mul' := by
        intro x y
        funext q
        rfl }
  exact
    reindexMul.trans
      ((MulEquiv.piCongrRight fun q :
          InducedRightCosets (absoluteValueDecompositionGroup K w.1) =>
        Units.mapEquiv
          (rightCosetCompletionIntegersRingEquivLocalized
            vK hvK w hvKna q).toMulEquiv).trans
        (inducedRightCosetCoordinates
          (absoluteValueDecompositionGroup K w.1)).symm)

end IntegralInduction
