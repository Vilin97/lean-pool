/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.OutsideIntegralInduced.LocalInduction.Equiv
/-!
# Inclusion of integral local induced modules

This leaf embeds the induced integer-unit module into the ordinary local
multiplicative induced block and proves injectivity.
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

section IntegralInduction

variable (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (hvKna : IsNonarchimedean (vK : K → ℝ))
    (w : AbsoluteValueExtension vK L)

/-- Pointwise inclusion of integer units embeds the integral induced
block into the ordinary local multiplicative induced block. -/
noncomputable def inducedIntegerUnitsToLocalPlaceBlock :
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
    letI : Algebra 𝒪[vK.Completion] (LocalizedCompletion vK w) :=
      LocalInductionInternal.integerAlgebra vK w hvKna
    letI := LocalInductionInternal.valuationHasExtension vK w hvKna
    letI := LocalInductionInternal.isIntegralClosure
      vK w hvK hvKna
    letI := decompositionGroupLocalizedIntegerUnitsAction
      (vK := vK) (hvK := hvK) (hvKna := hvKna) (w := w)
    CyclicCohomology.InducedModule
          (B := 𝒪[LocalizedCompletion vK w]ˣ)
          (absoluteValueDecompositionGroup K w.1) →*
      LocalPlaceBlock vK hvK w := by
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
  letI : Algebra 𝒪[vK.Completion] (LocalizedCompletion vK w) :=
    LocalInductionInternal.integerAlgebra vK w hvKna
  letI := LocalInductionInternal.valuationHasExtension vK w hvKna
  letI := LocalInductionInternal.isIntegralClosure
    vK w hvK hvKna
  letI := decompositionGroupLocalizedIntegerUnitsAction
    (vK := vK) (hvK := hvK) (hvKna := hvKna) (w := w)
  letI := decompositionGroupLocalUnitsAction vK hvK w
  refine
    { toFun := fun f =>
        ⟨fun g =>
            LocalFieldTheory.IsNonarchimedeanLocalField.integerUnitsToFieldUnits
              (LocalizedCompletion vK w) (f.1 g),
          by
            intro h g
            change
              LocalFieldTheory.IsNonarchimedeanLocalField.integerUnitsToFieldUnits
                    (LocalizedCompletion vK w) (f.1 (h.1 * g)) =
                h •
                  LocalFieldTheory.IsNonarchimedeanLocalField.integerUnitsToFieldUnits
                    (LocalizedCompletion vK w) (f.1 g)
            rw [f.2 h g]
            let : MulDistribMulAction
                (Gal(LocalizedCompletion vK w/vK.Completion))
                𝒪[LocalizedCompletion vK w]ˣ :=
              galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure
                vK.Completion (LocalizedCompletion vK w)
            let : MulDistribMulAction
                (Gal(LocalizedCompletion vK w/vK.Completion))
                (LocalizedCompletion vK w)ˣ :=
              galoisGroupFieldUnitsMulDistribMulAction
                vK.Completion (LocalizedCompletion vK w)
            exact
              integerUnitsToFieldUnits_galoisGroup_equivariant
                vK.Completion (LocalizedCompletion vK w)
                (decompositionGroupEquivAlgebraicLocalizationAut
                  vK hvK w h)
                (f.1 g)⟩
      map_one' := by
        apply Subtype.ext
        funext g
        rfl
      map_mul' := fun f₁ f₂ ↦ by
        apply Subtype.ext
        funext g
        rfl }

omit [NumberField K] [NumberField L] in
/-- The map from induced localized integer units to the corresponding
local-place block is injective. -/
theorem inducedIntegerUnitsToLocalPlaceBlock_injective :
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
    letI : Algebra 𝒪[vK.Completion] (LocalizedCompletion vK w) :=
      LocalInductionInternal.integerAlgebra vK w hvKna
    letI := LocalInductionInternal.valuationHasExtension vK w hvKna
    letI := LocalInductionInternal.isIntegralClosure
      vK w hvK hvKna
    letI := decompositionGroupLocalizedIntegerUnitsAction
      (vK := vK) (hvK := hvK) (hvKna := hvKna) (w := w)
    Function.Injective
      (inducedIntegerUnitsToLocalPlaceBlock
        (K := K) (L := L) vK hvK hvKna w) := by
  let := LocalInductionInternal.extensionCompletionAlgebra vK w
  let : SMul K w.1.Completion :=
    LocalInductionInternal.extensionCompletionSMul vK w
  let := LocalInductionInternal.completionAlgebra vK w
  let : Valued vK.Completion ℝ≥0 :=
    LocalInductionInternal.baseValued vK hvKna
  let : ValuativeRel vK.Completion :=
    LocalInductionInternal.baseValuativeRel vK hvKna
  let : Valued (LocalizedCompletion vK w) ℝ≥0 :=
    LocalInductionInternal.localizedValued vK w hvKna
  let : ValuativeRel (LocalizedCompletion vK w) :=
    LocalInductionInternal.localizedValuativeRel vK w hvKna
  let : Algebra 𝒪[vK.Completion] (LocalizedCompletion vK w) :=
    LocalInductionInternal.integerAlgebra vK w hvKna
  let := LocalInductionInternal.valuationHasExtension vK w hvKna
  let := LocalInductionInternal.isIntegralClosure
    vK w hvK hvKna
  let := decompositionGroupLocalizedIntegerUnitsAction
    (vK := vK) (hvK := hvK) (hvKna := hvKna) (w := w)
  intro f₁ f₂ h
  apply Subtype.ext
  funext g
  apply
    LocalFieldTheory.IsNonarchimedeanLocalField.integerUnitsToFieldUnits_injective
      (LocalizedCompletion vK w)
  exact congrArg
    (fun z : LocalPlaceBlock vK hvK w => z.1 g) h


end IntegralInduction
