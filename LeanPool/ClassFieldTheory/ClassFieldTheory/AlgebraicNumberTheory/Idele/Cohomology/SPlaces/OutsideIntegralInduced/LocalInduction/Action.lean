/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.OutsideIntegralInduced.LocalInduction.Spine
/-!
# Integral local induced modules

This file identifies the product of valuation-ring unit groups over the
extensions of a finite place with the corresponding induced module.
-/

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

/-- The decomposition-group action on the units of the intrinsic integer
ring of the chosen localization. -/
@[reducible]
noncomputable def decompositionGroupLocalizedIntegerUnitsAction :
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
    MulDistribMulAction
      (absoluteValueDecompositionGroup K w.1)
      𝒪[LocalizedCompletion vK w]ˣ := by
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
  letI : MulDistribMulAction
      (Gal(LocalizedCompletion vK w/vK.Completion))
      𝒪[LocalizedCompletion vK w]ˣ :=
    galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure
      vK.Completion (LocalizedCompletion vK w)
  exact
    MulDistribMulAction.compHom
      𝒪[LocalizedCompletion vK w]ˣ
      (decompositionGroupEquivAlgebraicLocalizationAut
        vK hvK w).toMonoidHom


end IntegralInduction
