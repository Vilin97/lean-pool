/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Completion.AdicCompletionComparison
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Completion.ChosenLocalization
import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.PadicField
import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.GaloisIntegerRing
import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ResidueGalois
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.Completion.ExtensionInvariants
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.HilbertRamification.AlgebraicLocalization
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
/-!
# Integer rings in the two finite-place completion models

This file restricts the canonical equivalences between the absolute-value and
adic completion models to their valuation rings.  It also identifies the
residue field of a rational finite-place completion.
-/

open scoped NumberField Classical NNReal ValuativeRel
open NumberField IsDedekindDomain

noncomputable section

open AlgebraicNumberTheory.Valuations
open LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField

/-- Embed global integers into the valuation ring of their finite-place
completion. -/
noncomputable def finitePlaceIntegerToCompletion
    {K : Type} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) :
    (𝓞 K) →+* 𝒪[ChosenFinitePlaceBaseCompletion (K := K) v] :=
  RingHom.codRestrict
    ((algebraMap K (ChosenFinitePlaceBaseCompletion (K := K) v)).comp
      (algebraMap (𝓞 K) K))
    𝒪[ChosenFinitePlaceBaseCompletion (K := K) v] (by
      intro x
      rw [finitePlaceCompletion_mem_integers_iff_norm_le_one]
      change ‖((WithAbs.toAbs (HeightOneSpectrum.adicAbv K v) (x : K) :
        WithAbs (HeightOneSpectrum.adicAbv K v)) :
          ChosenFinitePlaceBaseCompletion (K := K) v)‖ ≤ 1
      rw [UniformSpace.Completion.norm_coe, WithAbs.norm_toAbs_eq]
      rw [HeightOneSpectrum.adicAbv_def]
      apply (WithZeroMulInt.toNNReal_le_one_iff
        (HeightOneSpectrum.one_lt_absNorm_nnreal v)).2
      rw [HeightOneSpectrum.valuation_of_algebraMap]
      exact v.intValuation_le_one x)

@[simp]
theorem finitePlaceIntegerToCompletion_coe
    {K : Type} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K) :
    ((finitePlaceIntegerToCompletion v x :
      𝒪[ChosenFinitePlaceBaseCompletion (K := K) v]) :
        ChosenFinitePlaceBaseCompletion (K := K) v) =
      algebraMap K (ChosenFinitePlaceBaseCompletion (K := K) v) (x : K) :=
  rfl

/-- The comparison with the adic model takes a global element to its
standard finite-place embedding. -/
@[simp]
theorem finitePlaceCompletionRingEquiv_toCompletion
    {K : Type} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) (x : K) :
    finitePlaceCompletionRingEquiv v
        (algebraMap K (ChosenFinitePlaceBaseCompletion (K := K) v) x) =
      FinitePlace.embedding v x := by
  change finitePlaceCompletionRingHom v
    ((WithAbs.toAbs (HeightOneSpectrum.adicAbv K v) x :
      WithAbs (HeightOneSpectrum.adicAbv K v)) :
        ChosenFinitePlaceBaseCompletion (K := K) v) = _
  rw [finitePlaceCompletionRingHom_coe,
    finitePlaceCompletionBaseMap_apply]
  rfl

/-- Localizing the ring of integers at a finite prime preserves its residue
field.  This is the ideal-theoretic end of the finite-completion residue
comparison. -/
noncomputable def finitePlaceIdealResidueEquivLocalization
    {K : Type*} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) :
    (𝓞 K ⧸ v.asIdeal) ≃+*
      IsLocalRing.ResidueField (v.valuationSubringAtPrime K) :=
  IsLocalization.AtPrime.equivQuotMaximalIdeal
    v.asIdeal (v.valuationSubringAtPrime K)

/-- The residue field at a finite prime is canonically the residue field of
its normalized absolute-value completion. -/
noncomputable def finitePlaceIdealResidueEquivCompletion
    {K : Type} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) :
    (𝓞 K ⧸ v.asIdeal) ≃+*
      𝓀[ChosenFinitePlaceBaseCompletion (K := K) v] := by
  let a := HeightOneSpectrum.adicAbv K v
  let ha : LubinTate.Valuations.NonarchimedeanAbsoluteValue a :=
    (AbsoluteValue.isNonarchimedean_iff_bounded_nat a).1
      (HeightOneSpectrum.isNonarchimedean_adicAbv K v)
  let aC := AbsoluteValue.completionAbsoluteValue a
  let haC : LubinTate.Valuations.NonarchimedeanAbsoluteValue aC :=
    (AbsoluteValue.isNonarchimedean_iff_bounded_nat aC).1
      (AbsoluteValue.completionAbsoluteValue_isNonarchimedean a
        (HeightOneSpectrum.isNonarchimedean_adicAbv K v))
  let eBase :
      (v.valuationSubringAtPrime K) ≃+*
        LubinTate.Valuations.exponentialValuationSubring
          (absoluteValueExponentialValuation a ha) :=
    RingEquiv.restrict (RingEquiv.refl K)
      (v.valuationSubringAtPrime K)
      (LubinTate.Valuations.exponentialValuationSubring
        (absoluteValueExponentialValuation a ha)) (by
          intro x
          rw [v.valuationSubringAtPrime_eq_valuationSubring]
          change (v.valuation K) x ≤ 1 ↔
            x ∈ LubinTate.Valuations.exponentialValuationSubring
              (absoluteValueExponentialValuation a ha)
          rw [mem_absoluteValueExponentialSubring_iff]
          rw [HeightOneSpectrum.adicAbv_def]
          exact (WithZeroMulInt.toNNReal_le_one_iff
            (HeightOneSpectrum.one_lt_absNorm_nnreal v)).symm)
  let eCompletion :
      LubinTate.Valuations.exponentialValuationSubring
          (absoluteValueExponentialValuation aC haC) ≃+*
        𝒪[ChosenFinitePlaceBaseCompletion (K := K) v] :=
    RingEquiv.restrict (RingEquiv.refl a.Completion)
      (LubinTate.Valuations.exponentialValuationSubring
        (absoluteValueExponentialValuation aC haC))
      𝒪[ChosenFinitePlaceBaseCompletion (K := K) v] (by
        intro x
        rw [mem_absoluteValueExponentialSubring_iff]
        rw [finitePlaceCompletion_mem_integers_iff_norm_le_one]
        rfl)
  exact (finitePlaceIdealResidueEquivLocalization v).trans
    ((IsLocalRing.ResidueField.mapEquiv eBase).trans
      ((completionResidueEquiv a ha).trans
        (IsLocalRing.ResidueField.mapEquiv eCompletion)))

@[simp]
theorem finitePlaceIdealResidueEquivCompletion_apply_mk
    {K : Type} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K) :
    finitePlaceIdealResidueEquivCompletion v
        (Ideal.Quotient.mk v.asIdeal x) =
      IsLocalRing.residue
        𝒪[ChosenFinitePlaceBaseCompletion (K := K) v]
        (finitePlaceIntegerToCompletion v x) := by
  unfold finitePlaceIdealResidueEquivCompletion
    finitePlaceIdealResidueEquivLocalization
  rfl

/-- The finite completion and its defining prime ideal have residue fields
of the same cardinality. -/
theorem finitePlaceCompletion_residueField_card
    {K : Type} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) :
    Nat.card 𝓀[ChosenFinitePlaceBaseCompletion (K := K) v] =
      Nat.card (𝓞 K ⧸ v.asIdeal) :=
  Nat.card_congr (finitePlaceIdealResidueEquivCompletion v).symm.toEquiv

/-- The canonical equivalence of completion fields identifies their two
valuation rings. -/
theorem finitePlaceCompletionRingEquiv_mem_integers_iff
    {K : Type} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K))
    (x : ChosenFinitePlaceBaseCompletion (K := K) v) :
    finitePlaceCompletionRingEquiv v x ∈
        v.adicCompletionIntegers K ↔
      x ∈ 𝒪[ChosenFinitePlaceBaseCompletion (K := K) v] := by
  symm
  have hnorm :
      ‖finitePlaceCompletionRingEquiv v x‖ = ‖x‖ :=
    (finitePlaceCompletionRingHom_isometry v).norm_map_of_map_zero
      (map_zero (finitePlaceCompletionRingHom v)) x
  rw [finitePlaceCompletion_mem_integers_iff_norm_le_one
    (HeightOneSpectrum.adicAbv K v)
    (HeightOneSpectrum.isNonarchimedean_adicAbv K v) x]
  constructor
  · intro hx
    apply mem_adicCompletionIntegers_of_norm_le_one v
    simpa only [hnorm] using hx
  · intro hx
    have hxnorm :=
      norm_le_one_of_mem_adicCompletionIntegers v hx
    simpa only [hnorm] using hxnorm

/-- The canonical equivalence between the valuation ring of the
absolute-value completion and mathlib's adic completion integers. -/
noncomputable def finitePlaceCompletionIntegerRingEquiv
    {K : Type} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) :
    𝒪[ChosenFinitePlaceBaseCompletion (K := K) v] ≃+*
      v.adicCompletionIntegers K :=
  RingEquiv.restrict
    (finitePlaceCompletionRingEquiv v)
    𝒪[ChosenFinitePlaceBaseCompletion (K := K) v]
    (v.adicCompletionIntegers K).toSubring
      (fun x =>
        (finitePlaceCompletionRingEquiv_mem_integers_iff v x).symm)

/-- The canonical equivalence between the valuation ring of the chosen
localized completion and the concrete adic completion integers at its
centre. -/
noncomputable def chosenFinitePlaceLocalizedIntegerRingEquiv
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (v : HeightOneSpectrum (𝓞 K)) :
    let W :=
      finitePlaceExtensionCentre
        (K := K) (L := L) v
        (chosenFinitePlaceExtension (L := L) v)
    𝒪[ChosenFinitePlaceLocalizedCompletion
        (K := K) (L := L) v] ≃+*
      W.adicCompletionIntegers L := by
  let vK := HeightOneSpectrum.adicAbv K v
  let w := chosenFinitePlaceExtension (L := L) v
  let W :=
    finitePlaceExtensionCentre
      (K := K) (L := L) v w
  let E :=
    ChosenFinitePlaceLocalizedCompletion
      (K := K) (L := L) v
  let eField : E ≃+* W.adicCompletion L :=
    (AlgebraicNumberTheory.Valuations.localizedCompletionEquivCompletion
        vK (RayClass.adicAbv_isNontrivial v) w).toRingEquiv.trans
      (finitePlaceExtensionAdicCompletionRingEquiv
        (K := K) (L := L) v w)
  exact
    RingEquiv.restrict eField 𝒪[E]
      (W.adicCompletionIntegers L).toSubring (by
        intro x
        symm
        change
          eField x ∈ W.adicCompletionIntegers L ↔
            x ∈ 𝒪[E]
        change
          finitePlaceExtensionAdicCompletionRingEquiv
                (K := K) (L := L) v w
                (AlgebraicNumberTheory.Valuations.localizedCompletionEquivCompletion
                  vK (RayClass.adicAbv_isNontrivial v) w x) ∈
              W.adicCompletionIntegers L ↔
            x ∈ 𝒪[E]
        rw [
          finitePlaceExtensionAdicCompletionRingEquiv_mem_integers_iff,
          mem_absoluteValueCompletionIntegers_iff,
          localizedCompletion_mem_integers_iff_norm_le_one
            vK w
            (HeightOneSpectrum.isNonarchimedean_adicAbv K v) x]
        rfl)

/-- The integer rings of the standard completion at the centre and of the
chosen localized completion are canonically equivalent. -/
noncomputable def standardToChosenLocalizedIntegerRingEquiv
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (v : HeightOneSpectrum (𝓞 K)) :
    let W := finitePlaceExtensionCentre
      (K := K) (L := L) v (chosenFinitePlaceExtension (L := L) v)
    𝒪[ChosenFinitePlaceBaseCompletion (K := L) W] ≃+*
      𝒪[ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v] := by
  let W := finitePlaceExtensionCentre
    (K := K) (L := L) v (chosenFinitePlaceExtension (L := L) v)
  exact (finitePlaceCompletionIntegerRingEquiv W).trans
    (chosenFinitePlaceLocalizedIntegerRingEquiv (K := K) (L := L) v).symm

/-- Embed global integers into the integer ring of the chosen localized
completion, through the canonical comparison of completion models. -/
noncomputable def chosenFinitePlaceIntegerToLocalizedCompletion
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (v : HeightOneSpectrum (𝓞 K)) :
    (𝓞 L) →+*
      𝒪[ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v] := by
  let W := finitePlaceExtensionCentre
    (K := K) (L := L) v (chosenFinitePlaceExtension (L := L) v)
  exact (standardToChosenLocalizedIntegerRingEquiv
    (K := K) (L := L) v).toRingHom.comp
      (finitePlaceIntegerToCompletion W)

/-- On global integers the chosen localized integer-ring map is the
standard field embedding into the algebraic localization. -/
@[simp]
theorem chosenFinitePlaceIntegerToLocalizedCompletion_coe
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (v : HeightOneSpectrum (𝓞 K)) (x : 𝓞 L) :
    ((chosenFinitePlaceIntegerToLocalizedCompletion
        (K := K) (L := L) v x :
        𝒪[ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v]) :
        ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v) =
      AbsoluteValue.toAlgebraicLocalization
        (HeightOneSpectrum.adicAbv K v)
        (chosenFinitePlaceExtension (L := L) v).1
        (chosenFinitePlaceExtension (L := L) v).2
        (x : L) := by
  let vK := HeightOneSpectrum.adicAbv K v
  let w := chosenFinitePlaceExtension (L := L) v
  let W := finitePlaceExtensionCentre (K := K) (L := L) v w
  let E := ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v
  let eField : E ≃+* W.adicCompletion L :=
    (AlgebraicNumberTheory.Valuations.localizedCompletionEquivCompletion
        vK (RayClass.adicAbv_isNontrivial v) w).toRingEquiv.trans
      (finitePlaceExtensionAdicCompletionRingEquiv
        (K := K) (L := L) v w)
  have hRight :
      eField (AbsoluteValue.toAlgebraicLocalization
          vK w.1 w.2 (x : L)) =
        FinitePlace.embedding W (x : L) := by
    change
      finitePlaceExtensionAdicCompletionRingEquiv
          (K := K) (L := L) v w
          (AlgebraicNumberTheory.Valuations.localizedCompletionEquivCompletion
            vK (RayClass.adicAbv_isNontrivial v) w
            (AbsoluteValue.toAlgebraicLocalization vK w.1 w.2 (x : L))) =
        FinitePlace.embedding W (x : L)
    rw [AlgebraicNumberTheory.Valuations.localizedCompletionEquivCompletion_coe,
      AbsoluteValue.toAlgebraicLocalization_apply]
    exact finitePlaceExtensionAdicCompletionRingEquiv_toCompletion v w (x : L)
  apply eField.injective
  calc
    eField
        ((chosenFinitePlaceIntegerToLocalizedCompletion
          (K := K) (L := L) v x : 𝒪[E]) : E) =
      finitePlaceCompletionRingEquiv W
        ((finitePlaceIntegerToCompletion W x :
          𝒪[ChosenFinitePlaceBaseCompletion (K := L) W]) :
            ChosenFinitePlaceBaseCompletion (K := L) W) := by
        have hInteger :
            chosenFinitePlaceLocalizedIntegerRingEquiv (K := K) (L := L) v
                (chosenFinitePlaceIntegerToLocalizedCompletion
                  (K := K) (L := L) v x) =
              finitePlaceCompletionIntegerRingEquiv W
                (finitePlaceIntegerToCompletion W x) := by
          change
            (chosenFinitePlaceLocalizedIntegerRingEquiv (K := K) (L := L) v)
                ((chosenFinitePlaceLocalizedIntegerRingEquiv
                  (K := K) (L := L) v).symm
                  ((finitePlaceCompletionIntegerRingEquiv W)
                    (finitePlaceIntegerToCompletion W x))) = _
          exact RingEquiv.apply_symm_apply _ _
        exact congrArg
          (fun y : W.adicCompletionIntegers L =>
            (y : W.adicCompletion L)) hInteger
    _ = FinitePlace.embedding W (x : L) := by
      rw [finitePlaceIntegerToCompletion_coe]
      exact finitePlaceCompletionRingEquiv_toCompletion W (x : L)
    _ = eField (AbsoluteValue.toAlgebraicLocalization vK w.1 w.2 (x : L)) :=
      hRight.symm

/-- Restriction of a decomposition-group automorphism to global integers
commutes with their embedding in the chosen algebraic localization. -/
theorem chosenFinitePlaceIntegerToLocalizedCompletion_equivariant
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (v : HeightOneSpectrum (𝓞 K))
    (σ : HilbertRamification.absoluteValueDecompositionGroup K
      (chosenFinitePlaceExtension (L := L) v).1)
    (x : 𝓞 L) :
    let vK := HeightOneSpectrum.adicAbv K v
    let w := chosenFinitePlaceExtension (L := L) v
    letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI := AbsoluteValue.completionAlgebra vK w.1 w.2
    (HilbertRamification.decompositionGroupEquivAlgebraicLocalizationAut
        vK (RayClass.adicAbv_isNontrivial v) w σ)
        ((chosenFinitePlaceIntegerToLocalizedCompletion
          (K := K) (L := L) v x :
          𝒪[ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v]) :
          ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v) =
      ((chosenFinitePlaceIntegerToLocalizedCompletion
          (K := K) (L := L) v
          (NumberField.RingOfIntegers.mapAlgEquiv (σ : L ≃ₐ[K] L) x) :
          𝒪[ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v]) :
          ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v) := by
  let vK := HeightOneSpectrum.adicAbv K v
  let w := chosenFinitePlaceExtension (L := L) v
  rw [chosenFinitePlaceIntegerToLocalizedCompletion_coe,
    chosenFinitePlaceIntegerToLocalizedCompletion_coe]
  change
    (HilbertRamification.decompositionGroupEquivAlgebraicLocalizationAut
        vK (RayClass.adicAbv_isNontrivial v) w σ)
        (AbsoluteValue.toAlgebraicLocalization vK w.1 w.2 (x : L)) =
      AbsoluteValue.toAlgebraicLocalization vK w.1 w.2
        ((σ : L ≃ₐ[K] L) (x : L))
  exact
    HilbertRamification.localizationRamificationGroups_decompositionGroupEquiv_toLocalization
      vK (RayClass.adicAbv_isNontrivial v) w σ (x : L)

/-- The centre ideal and the chosen localized completion have canonically
equivalent residue fields.  This transfers ideal-theoretic Frobenius
conditions to the local field on which the chosen Artin map acts. -/
noncomputable def chosenFinitePlaceLocalizedResidueEquiv
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (v : HeightOneSpectrum (𝓞 K)) :
    let W := finitePlaceExtensionCentre
      (K := K) (L := L) v (chosenFinitePlaceExtension (L := L) v)
    (𝓞 L ⧸ W.asIdeal) ≃+*
      𝓀[ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v] := by
  let W := finitePlaceExtensionCentre
    (K := K) (L := L) v (chosenFinitePlaceExtension (L := L) v)
  exact (finitePlaceIdealResidueEquivCompletion W).trans
    (IsLocalRing.ResidueField.mapEquiv
      (standardToChosenLocalizedIntegerRingEquiv (K := K) (L := L) v))

@[simp]
theorem chosenFinitePlaceLocalizedResidueEquiv_apply_mk
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (v : HeightOneSpectrum (𝓞 K)) (x : 𝓞 L) :
    let W := finitePlaceExtensionCentre
      (K := K) (L := L) v (chosenFinitePlaceExtension (L := L) v)
    chosenFinitePlaceLocalizedResidueEquiv (K := K) (L := L) v
        (Ideal.Quotient.mk W.asIdeal x) =
      IsLocalRing.residue
        𝒪[ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v]
        (chosenFinitePlaceIntegerToLocalizedCompletion
          (K := K) (L := L) v x) := by
  let W := finitePlaceExtensionCentre
    (K := K) (L := L) v (chosenFinitePlaceExtension (L := L) v)
  let eInteger :
      𝒪[ChosenFinitePlaceBaseCompletion (K := L) W] ≃+*
        𝒪[ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v] :=
    standardToChosenLocalizedIntegerRingEquiv (K := K) (L := L) v
  have hMap :
      eInteger (finitePlaceIntegerToCompletion W x) =
        chosenFinitePlaceIntegerToLocalizedCompletion
          (K := K) (L := L) v x := by
    rfl
  calc
    chosenFinitePlaceLocalizedResidueEquiv (K := K) (L := L) v
        (Ideal.Quotient.mk W.asIdeal x) =
      (IsLocalRing.ResidueField.mapEquiv eInteger)
        (finitePlaceIdealResidueEquivCompletion W
          (Ideal.Quotient.mk W.asIdeal x)) := by
        rfl
    _ = (IsLocalRing.ResidueField.mapEquiv eInteger)
          (IsLocalRing.residue
            𝒪[ChosenFinitePlaceBaseCompletion (K := L) W]
            (finitePlaceIntegerToCompletion W x)) := by
      exact congrArg (IsLocalRing.ResidueField.mapEquiv eInteger)
        (finitePlaceIdealResidueEquivCompletion_apply_mk W x)
    _ = IsLocalRing.residue
          𝒪[ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v]
          (eInteger (finitePlaceIntegerToCompletion W x)) := by
      rfl
    _ = IsLocalRing.residue
          𝒪[ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v]
          (chosenFinitePlaceIntegerToLocalizedCompletion
            (K := K) (L := L) v x) := by
      exact congrArg
        (IsLocalRing.residue
          𝒪[ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v]) hMap

/-- The chosen comparison from the prime-ideal residue field to the localized
completion residue field respects the decomposition-group action. -/
theorem chosenFinitePlaceLocalizedResidueEquiv_equivariant
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (v : HeightOneSpectrum (𝓞 K))
    (σ : HilbertRamification.absoluteValueDecompositionGroup K
      (chosenFinitePlaceExtension (L := L) v).1)
    (x : 𝓞 L) :
    let vK := HeightOneSpectrum.adicAbv K v
    let w := chosenFinitePlaceExtension (L := L) v
    let W := finitePlaceExtensionCentre (K := K) (L := L) v w
    let C := ChosenFinitePlaceBaseCompletion (K := K) v
    let E := ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v
    letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI := AbsoluteValue.completionAlgebra vK w.1 w.2
    chosenFinitePlaceLocalizedResidueEquiv (K := K) (L := L) v
        (Ideal.Quotient.mk W.asIdeal
          (NumberField.RingOfIntegers.mapAlgEquiv (σ : L ≃ₐ[K] L) x)) =
      LocalFieldTheory.galoisGroupResidueAlgEquivOfIsIntegralClosure C E
        ((HilbertRamification.decompositionGroupEquivAlgebraicLocalizationAut
          vK (RayClass.adicAbv_isNontrivial v) w) σ)
        (chosenFinitePlaceLocalizedResidueEquiv (K := K) (L := L) v
          (Ideal.Quotient.mk W.asIdeal x)) := by
  let vK := HeightOneSpectrum.adicAbv K v
  let w := chosenFinitePlaceExtension (L := L) v
  let W := finitePlaceExtensionCentre (K := K) (L := L) v w
  let C := ChosenFinitePlaceBaseCompletion (K := K) v
  let E := ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v
  let f : E ≃ₐ[C] E :=
    (HilbertRamification.decompositionGroupEquivAlgebraicLocalizationAut
      vK (RayClass.adicAbv_isNontrivial v) w) σ
  let y : 𝒪[E] := chosenFinitePlaceIntegerToLocalizedCompletion
    (K := K) (L := L) v x
  have hInt :
      LocalFieldTheory.galoisGroupIntegerRingEquivOfIsIntegralClosure C E f y =
        chosenFinitePlaceIntegerToLocalizedCompletion (K := K) (L := L) v
          (NumberField.RingOfIntegers.mapAlgEquiv (σ : L ≃ₐ[K] L) x) := by
    apply Subtype.ext
    rw [LocalFieldTheory.galoisGroupIntegerRingEquivOfIsIntegralClosure_apply]
    exact chosenFinitePlaceIntegerToLocalizedCompletion_equivariant
      (K := K) (L := L) v σ x
  calc
    chosenFinitePlaceLocalizedResidueEquiv (K := K) (L := L) v
        (Ideal.Quotient.mk W.asIdeal
          (NumberField.RingOfIntegers.mapAlgEquiv (σ : L ≃ₐ[K] L) x)) =
        IsLocalRing.residue 𝒪[E]
          (chosenFinitePlaceIntegerToLocalizedCompletion (K := K) (L := L) v
            (NumberField.RingOfIntegers.mapAlgEquiv (σ : L ≃ₐ[K] L) x)) :=
      chosenFinitePlaceLocalizedResidueEquiv_apply_mk (K := K) (L := L) v _
    _ = IsLocalRing.residue 𝒪[E]
          (LocalFieldTheory.galoisGroupIntegerRingEquivOfIsIntegralClosure C E f y) :=
      congrArg (IsLocalRing.residue 𝒪[E]) hInt.symm
    _ = LocalFieldTheory.galoisGroupResidueAlgEquivOfIsIntegralClosure C E f
          (IsLocalRing.residue 𝒪[E] y) :=
      (LocalFieldTheory.galoisGroupResidueFieldEquivOfIsIntegralClosure_residue
        C E f y).symm
    _ = LocalFieldTheory.galoisGroupResidueAlgEquivOfIsIntegralClosure C E f
          (chosenFinitePlaceLocalizedResidueEquiv (K := K) (L := L) v
            (Ideal.Quotient.mk W.asIdeal x)) := by
      exact congrArg
        (LocalFieldTheory.galoisGroupResidueAlgEquivOfIsIntegralClosure C E f)
        (chosenFinitePlaceLocalizedResidueEquiv_apply_mk
          (K := K) (L := L) v x).symm

/-- The residue cardinality of the chosen localized extension is the norm
of its centre ideal. -/
theorem chosenFinitePlaceLocalized_residueField_card
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (v : HeightOneSpectrum (𝓞 K)) :
    let W := finitePlaceExtensionCentre
      (K := K) (L := L) v (chosenFinitePlaceExtension (L := L) v)
    Nat.card 𝓀[ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v] =
      Nat.card (𝓞 L ⧸ W.asIdeal) := by
  exact Nat.card_congr (chosenFinitePlaceLocalizedResidueEquiv
    (K := K) (L := L) v).symm.toEquiv

/-- The residue field of the absolute-value completion at a rational finite
place has cardinality equal to the natural prime represented by that place. -/
theorem rationalFinitePlaceCompletion_residueField_card
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    Nat.card
        𝓀[ChosenFinitePlaceBaseCompletion (K := ℚ) v] =
      ((Rat.HeightOneSpectrum.primesEquiv
        (R := 𝓞 ℚ) v : Nat.Primes) : ℕ) := by
  let p : Nat.Primes :=
    Rat.HeightOneSpectrum.primesEquiv
      (R := 𝓞 ℚ) v
  let : Fact p.1.Prime := ⟨p.2⟩
  let eIntegers :
      𝒪[ChosenFinitePlaceBaseCompletion (K := ℚ) v] ≃+*
        v.adicCompletionIntegers ℚ :=
    finitePlaceCompletionIntegerRingEquiv v
  let ePadicIntegers :
      v.adicCompletionIntegers ℚ ≃+* ℤ_[p.1] :=
    (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v).toRingEquiv
  let eResidue :
      𝓀[ChosenFinitePlaceBaseCompletion (K := ℚ) v] ≃+*
        ZMod p.1 :=
    (IsLocalRing.ResidueField.mapEquiv
      (eIntegers.trans ePadicIntegers)).trans
        (LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicIntResidueFieldEquivZMod
          p.1)
  change Nat.card
      𝓀[ChosenFinitePlaceBaseCompletion (K := ℚ) v] = p.1
  calc
    Nat.card
          𝓀[ChosenFinitePlaceBaseCompletion (K := ℚ) v] =
        Nat.card (ZMod p.1) :=
      Nat.card_congr eResidue.toEquiv
    _ = p.1 := Nat.card_zmod p.1
