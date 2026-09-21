/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Completion.LocalizedValuation
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalBlocks.Tensor
/-!
# Transporting integer rings across finite-place cosets

This file transports completion fields and their valuation rings from every
right coset of a decomposition group to the chosen algebraic localization.
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

section CompletionTransport

variable (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK L)

/-- A completion belonging to a right coset, transported first by
Galois conjugation and then into the chosen algebraic localization. -/
noncomputable def rightCosetCompletionRingEquivLocalized
    (q : InducedRightCosets (absoluteValueDecompositionGroup K w.1)) :
    letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI := AbsoluteValue.completionAlgebra vK w.1 w.2
    (rightCosetExtensionEquiv vK hvK w q).1.Completion ≃+*
      LocalizedCompletion vK w := by
  letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  letI : SMul K w.1.Completion := hK.toSMul
  letI := AbsoluteValue.completionAlgebra vK w.1 w.2
  change
    (absoluteValueExtensionConjugate
      vK w (Quotient.out q)).1.Completion ≃+*
      LocalizedCompletion vK w
  exact
    (conjugateExtensionCompletionRingEquiv
      vK w (Quotient.out q)).trans
      (localizedCompletionEquivCompletion vK hvK w).symm.toRingEquiv

omit [NumberField K] [NumberField L] in
/-- The right-coset transport is an isometry for the inherited norms. -/
theorem rightCosetCompletionRingEquivLocalized_norm_eq
    (q : InducedRightCosets (absoluteValueDecompositionGroup K w.1))
    (x : (absoluteValueExtensionConjugate
      vK w (Quotient.out q)).1.Completion) :
    letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI := AbsoluteValue.completionAlgebra vK w.1 w.2
    ‖rightCosetCompletionRingEquivLocalized vK hvK w q x‖ =
      ‖x‖ := by
  let hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  let : SMul K w.1.Completion := hK.toSMul
  let := AbsoluteValue.completionAlgebra vK w.1 w.2
  let z :=
    conjugateExtensionCompletionRingEquiv
      vK w (Quotient.out q) x
  have hcoe :
      (((localizedCompletionEquivCompletion vK hvK w).symm z :
          LocalizedCompletion vK w) : w.1.Completion) = z := by
    have h :=
      localizedCompletionEquivCompletion_coe
        vK hvK w
          ((localizedCompletionEquivCompletion vK hvK w).symm z)
    rw [AlgEquiv.apply_symm_apply] at h
    exact h.symm
  change
    ‖(((localizedCompletionEquivCompletion vK hvK w).symm z :
        LocalizedCompletion vK w) : w.1.Completion)‖ = ‖x‖
  rw [hcoe]
  exact
    conjugateExtensionCompletionRingEquiv_norm_eq
      vK w (Quotient.out q) x

/-- The same transport restricted to the two valuation integer rings. -/
noncomputable def rightCosetCompletionIntegersRingEquivLocalized
    (hvKna : IsNonarchimedean (vK : K → ℝ))
    (q : InducedRightCosets (absoluteValueDecompositionGroup K w.1)) :
    letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI := AbsoluteValue.completionAlgebra vK w.1 w.2
    letI : Valued (LocalizedCompletion vK w) ℝ≥0 :=
      localizedCompletionFinitePlaceValued vK w hvKna
    letI : ValuativeRel (LocalizedCompletion vK w) :=
      localizedCompletionFinitePlaceValuativeRel vK w hvKna
    (absoluteValueCompletionIntegers
      (absoluteValueExtensionConjugate
        vK w (Quotient.out q)).1
      (absoluteValueExtension_isNonarchimedean
        vK hvKna
        (absoluteValueExtensionConjugate
          vK w (Quotient.out q)))) ≃+*
      𝒪[LocalizedCompletion vK w] := by
  letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  letI : SMul K w.1.Completion := hK.toSMul
  letI := AbsoluteValue.completionAlgebra vK w.1 w.2
  letI : Valued (LocalizedCompletion vK w) ℝ≥0 :=
    localizedCompletionFinitePlaceValued vK w hvKna
  letI : ValuativeRel (LocalizedCompletion vK w) :=
    localizedCompletionFinitePlaceValuativeRel vK w hvKna
  let e :
      (absoluteValueExtensionConjugate
        vK w (Quotient.out q)).1.Completion ≃+*
        LocalizedCompletion vK w :=
    rightCosetCompletionRingEquivLocalized vK hvK w q
  refine e.restrict _ _ ?_
  intro x
  rw [mem_absoluteValueCompletionIntegers_iff,
    localizedCompletion_mem_integers_iff_norm_le_one]
  have hnorm :=
    rightCosetCompletionRingEquivLocalized_norm_eq
      vK hvK w q x
  change ‖e x‖ = ‖x‖ at hnorm
  rw [hnorm]

end CompletionTransport
