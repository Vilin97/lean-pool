/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Completion.UnramifiedComparison.IdealToCompletion
import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.RamificationIdeal
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients.Basic
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients.Norm
/-!
# From completed to ideal-theoretic unramifiedness

This file recovers ideal-theoretic unramifiedness from the actual chosen
localized completion and propagates it to every place above the base place in
a finite Galois extension.
-/

open scoped NumberField Classical NNReal ValuativeRel
open NumberField IsDedekindDomain

noncomputable section

open AlgebraicNumberTheory.Valuations
open LocalClassFieldTheory
open LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

/-- The actual image of the chosen global integral uniformizer in the
integer ring of the chosen localized completion. -/
noncomputable def chosenFinitePlaceTargetIntegralUniformizer
    (v : HeightOneSpectrum (𝓞 K)) :
    𝒪[ChosenFinitePlaceLocalizedCompletion
      (K := K) (L := L) v] :=
  algebraMap
      𝒪[ChosenFinitePlaceBaseCompletion (K := K) v]
      𝒪[ChosenFinitePlaceLocalizedCompletion
        (K := K) (L := L) v]
    (chosenFinitePlaceCompletionIntegralUniformizer v).completionInteger

omit [NumberField L] in
/-- In an unramified chosen localized completion, the canonical global
integral uniformizer remains a uniformizer after scalar extension. -/
theorem chosenFinitePlace_integralUniformizer_map_isUniformizer
    (v : HeightOneSpectrum (𝓞 K))
    (hunram :
      ChosenFinitePlaceIsUnramified
        (K := K) (L := L) v) :
    (ValuativeRel.valuation
      (ChosenFinitePlaceLocalizedCompletion
        (K := K) (L := L) v)).IsUniformizer
      ((chosenFinitePlaceTargetIntegralUniformizer
          (K := K) (L := L) v :
        𝒪[ChosenFinitePlaceLocalizedCompletion
          (K := K) (L := L) v]) :
        ChosenFinitePlaceLocalizedCompletion
          (K := K) (L := L) v) := by
  let vK := HeightOneSpectrum.adicAbv K v
  let E :=
    ChosenFinitePlaceLocalizedCompletion
      (K := K) (L := L) v
  let :
      IsNonarchimedeanLocalField.IsUnramifiedValuedExtension
        vK.Completion E := by
    simpa [ChosenFinitePlaceIsUnramified] using hunram
  let πData :=
    chosenFinitePlaceCompletionIntegralUniformizer v
  let baseDVF :
      ValuationTheory.DiscreteValuationField.DVF
        vK.Completion :=
    { ValueGroup := ValuativeRel.ValueGroupWithZero vK.Completion
      valuation := ValuativeRel.valuation vK.Completion }
  have hpiBaseMaximalIdeal :
      (𝓂[vK.Completion] :
          Ideal 𝒪[vK.Completion]) =
        Ideal.span ({πData.completionInteger} :
          Set 𝒪[vK.Completion]) :=
    baseDVF.maximalIdeal_eq_span_uniformizer
      πData.completionInteger_isUniformizer
  let integerMap :
      𝒪[vK.Completion] →+* 𝒪[E] :=
    algebraMap 𝒪[vK.Completion] 𝒪[E]
  let πTarget : 𝒪[E] :=
    integerMap πData.completionInteger
  have hpiTargetMaximalIdeal :
      (𝓂[E] : Ideal 𝒪[E]) =
        Ideal.span ({πTarget} : Set 𝒪[E]) := by
    calc
      (𝓂[E] : Ideal 𝒪[E]) =
          Ideal.map
            integerMap
            (𝓂[vK.Completion] :
              Ideal 𝒪[vK.Completion]) :=
        (maximalIdeal_map_eq_maximalIdeal_of_unramifiedValuation
          vK.Completion E).symm
      _ =
          Ideal.map
            integerMap
            (Ideal.span ({πData.completionInteger} :
              Set 𝒪[vK.Completion])) := by
        exact congrArg
          (Ideal.map integerMap)
          hpiBaseMaximalIdeal
      _ = Ideal.span ({πTarget} : Set 𝒪[E]) := by
        rw [Ideal.map_span, Set.image_singleton]
  let targetDVF :
      ValuationTheory.DiscreteValuationField.DVF E :=
    { ValueGroup := ValuativeRel.ValueGroupWithZero E
      valuation := ValuativeRel.valuation E }
  change
    targetDVF.valuation.IsUniformizer
      (πTarget : E)
  exact
    Valuation.isUniformizer_of_maximalIdeal_eq_span
      (v := targetDVF.valuation) hpiTargetMaximalIdeal

/-- Completed unramifiedness forces ramification index one at the actual
global centre of the chosen finite-place extension. -/
theorem
    finitePlaceExtensionCentre_ramificationIdx'_eq_one_of_chosenFinitePlaceIsUnramified
    (v : HeightOneSpectrum (𝓞 K))
    (hunram :
      ChosenFinitePlaceIsUnramified
        (K := K) (L := L) v) :
    v.asIdeal.ramificationIdx'
        (finitePlaceExtensionCentre
          (K := K) (L := L) v
          (chosenFinitePlaceExtension (L := L) v)).asIdeal =
      1 := by
  let vK := HeightOneSpectrum.adicAbv K v
  let w := chosenFinitePlaceExtension (L := L) v
  let W :=
    finitePlaceExtensionCentre
      (K := K) (L := L) v w
  let E :=
    ChosenFinitePlaceLocalizedCompletion
      (K := K) (L := L) v
  let πData :=
    chosenFinitePlaceCompletionIntegralUniformizer v
  let πTarget : 𝒪[E] :=
    chosenFinitePlaceTargetIntegralUniformizer
      (K := K) (L := L) v
  let eTarget :
      𝒪[E] ≃+* W.adicCompletionIntegers L :=
    chosenFinitePlaceLocalizedIntegerRingEquiv
      (K := K) (L := L) v
  have hpiTargetConcreteIrreducible :
      Irreducible (eTarget πTarget) := by
    apply (MulEquiv.irreducible_iff eTarget.toMulEquiv).2
    rw [IsDiscreteValuationRing.irreducible_iff_uniformizer]
    let targetIntrinsicDVF :
        ValuationTheory.DiscreteValuationField.DVF E :=
      { ValueGroup := ValuativeRel.ValueGroupWithZero E
        valuation := ValuativeRel.valuation E }
    exact
      targetIntrinsicDVF.maximalIdeal_eq_span_uniformizer
        (by
          simpa only [πTarget] using
            chosenFinitePlace_integralUniformizer_map_isUniformizer
              (K := K) (L := L) v hunram)
  let targetDVF :
      ValuationTheory.DiscreteValuationField.DVF
        (W.adicCompletion L) :=
    { ValueGroup := WithZero (Multiplicative ℤ)
      valuation := Valued.v }
  have hpiTargetConcreteUniformizer :
      targetDVF.valuation.IsUniformizer
        ((eTarget πTarget :
          W.adicCompletionIntegers L) :
          W.adicCompletion L) :=
    Valuation.isUniformizer_of_maximalIdeal_eq_span
      (v := targetDVF.valuation)
      hpiTargetConcreteIrreducible.maximalIdeal_eq
  have hpiTargetConcreteValuation :
      targetDVF.valuation
          ((eTarget πTarget :
            W.adicCompletionIntegers L) :
            W.adicCompletion L) =
        WithZero.exp (-1 : ℤ) := by
    have h := hpiTargetConcreteUniformizer
    rw [Valuation.IsUniformizer.iff,
      Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
        (W.valuedAdicCompletion_surjective L)] at h
    exact h
  have hpiTargetField :
      (eTarget πTarget : W.adicCompletion L) =
        algebraMap L (W.adicCompletion L)
          (algebraMap K L (πData.integer : K)) := by
    change
      finitePlaceExtensionAdicCompletionRingEquiv
            (K := K) (L := L) v w
            (localizedCompletionEquivCompletion
              vK (RayClass.adicAbv_isNontrivial v) w
              (algebraMap vK.Completion E
                (πData.completionInteger :
                  vK.Completion))) =
        _
    rw [(localizedCompletionEquivCompletion
      vK (RayClass.adicAbv_isNontrivial v) w).commutes,
      πData.coe_completionInteger]
    change
      finitePlaceExtensionAdicCompletionRingEquiv
            (K := K) (L := L) v w
            (AbsoluteValue.completionMap
              vK w.1 w.2
              (algebraMap K vK.Completion
                (πData.integer : K))) =
        _
    rw [AbsoluteValue.completionMap_coe,
      finitePlaceExtensionAdicCompletionRingEquiv_toCompletion]
    rfl
  have hmapPi :
      finitePlaceExtensionAdicCompletionMap K L v w
          (algebraMap K (v.adicCompletion K)
            (πData.integer : K)) =
        (eTarget πTarget : W.adicCompletion L) := by
    rw [hpiTargetField]
    change
      finitePlaceExtensionAdicCompletionMap K L v w
          ((πData.integer : K) : v.adicCompletion K) =
        ((algebraMap K L (πData.integer : K) : L) :
          W.adicCompletion L)
    exact
      finitePlaceExtensionAdicCompletionMap_coe
        K L v w (πData.integer : K)
  have hpiConcreteValuation :
      Valued.v
          (algebraMap K (v.adicCompletion K)
            (πData.integer : K)) =
        WithZero.exp (-1 : ℤ) := by
    change
      Valued.v
          (πData.integer : v.adicCompletion K) =
        WithZero.exp (-1 : ℤ)
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
      HeightOneSpectrum.valuation_of_algebraMap,
      πData.intValuation_eq_exp_neg_one]
  let eGlobal : ℕ :=
    v.asIdeal.ramificationIdx' W.asIdeal
  have hvalued :
      WithZero.exp (-1 : ℤ) =
        WithZero.exp (-1 : ℤ) ^ eGlobal := by
    calc
      WithZero.exp (-1 : ℤ) =
          Valued.v
            (eTarget πTarget :
              W.adicCompletion L) :=
        hpiTargetConcreteValuation.symm
      _ =
          Valued.v
            (finitePlaceExtensionAdicCompletionMap
              K L v w
              (algebraMap K (v.adicCompletion K)
                (πData.integer : K))) := by
        exact congrArg
          (fun x : W.adicCompletion L => Valued.v x)
          hmapPi.symm
      _ =
          Valued.v
              (algebraMap K (v.adicCompletion K)
                (πData.integer : K)) ^
            eGlobal := by
        exact
          finitePlaceExtensionAdicCompletionMap_valued
              K L v w
              (algebraMap K (v.adicCompletion K)
                (πData.integer : K))
      _ = WithZero.exp (-1 : ℤ) ^ eGlobal := by
        exact congrArg (fun z => z ^ eGlobal)
          hpiConcreteValuation
  have hexp :
      WithZero.exp (-1 : ℤ) =
        WithZero.exp (-(eGlobal : ℤ)) := by
    calc
      WithZero.exp (-1 : ℤ) =
          WithZero.exp (-1 : ℤ) ^ eGlobal :=
        hvalued
      _ =
          WithZero.exp (eGlobal • (-1 : ℤ)) :=
        (WithZero.exp_nsmul _ _).symm
      _ =
          WithZero.exp (-(eGlobal : ℤ)) := by
        congr 1
        simp
  have hint :
      (-1 : ℤ) = -(eGlobal : ℤ) :=
    WithZero.exp_injective hexp
  have heGlobal : eGlobal = 1 := by
    have heInt : (1 : ℤ) = (eGlobal : ℤ) :=
      neg_injective hint
    exact_mod_cast heInt.symm
  exact heGlobal

/-- Unramifiedness of the actual chosen localized completion forces
ideal-theoretic unramifiedness at its global centre. -/
theorem isUnramifiedAt_of_chosenFinitePlaceIsUnramified
    (v : HeightOneSpectrum (𝓞 K))
    (hunram :
      ChosenFinitePlaceIsUnramified
        (K := K) (L := L) v) :
    Algebra.IsUnramifiedAt (𝓞 K)
      (finitePlaceExtensionCentre
        (K := K) (L := L) v
        (chosenFinitePlaceExtension (L := L) v)).asIdeal := by
  let w := chosenFinitePlaceExtension (L := L) v
  let W :=
    finitePlaceExtensionCentre
      (K := K) (L := L) v w
  let : W.asIdeal.LiesOver v.asIdeal :=
    finitePlaceExtensionCentre_liesOver
      (K := K) (L := L) v w
  have hBasePrime :
      W.asIdeal.under (𝓞 K) ≠ ⊥ := by
    rw [← W.asIdeal.over_def v.asIdeal]
    exact v.ne_bot
  let : Finite ((𝓞 K) ⧸ W.asIdeal.under (𝓞 K)) :=
    Ring.HasFiniteQuotients.finiteQuotient hBasePrime
  let :
      PerfectField
        (W.asIdeal.under (𝓞 K)).ResidueField :=
    PerfectField.ofFinite
  apply Ideal.ramificationIdx_eq_one_iff.mp
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx
    v.asIdeal W.asIdeal v.ne_bot]
  exact
    finitePlaceExtensionCentre_ramificationIdx'_eq_one_of_chosenFinitePlaceIsUnramified
      (K := K) (L := L) v hunram

/-- In a finite Galois number-field extension, completed unramifiedness at
the chosen place implies ideal-theoretic unramifiedness at every finite place
above the same base place. -/
theorem
    isUnramifiedAt_at_finitePlaceAbove_of_chosenFinitePlaceIsUnramified
    (v : HeightOneSpectrum (𝓞 K))
    (P : HeightOneSpectrum (𝓞 L))
    (hP : finitePlaceBelow (K := K) P = v)
    (hunram :
      ChosenFinitePlaceIsUnramified
        (K := K) (L := L) v) :
    Algebra.IsUnramifiedAt (𝓞 K) P.asIdeal := by
  let w := chosenFinitePlaceExtension (L := L) v
  let W :=
    finitePlaceExtensionCentre
      (K := K) (L := L) v w
  let : Finite (L ≃ₐ[K] L) :=
    IsGaloisGroup.finite (L ≃ₐ[K] L) K L
  let :
      IsGaloisGroup
        (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) :=
    IsGaloisGroup.of_isFractionRing
      (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) K L
  let : P.asIdeal.LiesOver v.asIdeal := by
    constructor
    have h := congrArg HeightOneSpectrum.asIdeal hP
    simpa only [finitePlaceBelow_asIdeal] using h.symm
  let : W.asIdeal.LiesOver v.asIdeal :=
    finitePlaceExtensionCentre_liesOver
      (K := K) (L := L) v w
  have hChosen :
      Algebra.IsUnramifiedAt (𝓞 K) W.asIdeal :=
    isUnramifiedAt_of_chosenFinitePlaceIsUnramified
      (K := K) (L := L) v hunram
  have hChosenRamification :
      W.asIdeal.ramificationIdx (𝓞 K) = 1 := by
    let : Algebra.IsUnramifiedAt (𝓞 K) W.asIdeal :=
      hChosen
    exact Ideal.ramificationIdx_eq_one W.asIdeal (𝓞 K)
  have hRamification :
      P.asIdeal.ramificationIdx (𝓞 K) =
        W.asIdeal.ramificationIdx (𝓞 K) :=
    HilbertRamification.Dedekind.dedekindRamification_ramificationIdx_eq
      v.asIdeal P.asIdeal W.asIdeal (L ≃ₐ[K] L)
  have hWBasePrime :
      W.asIdeal.under (𝓞 K) ≠ ⊥ := by
    rw [← W.asIdeal.over_def v.asIdeal]
    exact v.ne_bot
  let : Finite ((𝓞 K) ⧸ W.asIdeal.under (𝓞 K)) :=
    Ring.HasFiniteQuotients.finiteQuotient hWBasePrime
  let :
      PerfectField
        (W.asIdeal.under (𝓞 K)).ResidueField :=
    PerfectField.ofFinite
  have hPBasePrime :
      P.asIdeal.under (𝓞 K) ≠ ⊥ := by
    rw [← P.asIdeal.over_def v.asIdeal]
    exact v.ne_bot
  let : Finite ((𝓞 K) ⧸ P.asIdeal.under (𝓞 K)) :=
    Ring.HasFiniteQuotients.finiteQuotient hPBasePrime
  let :
      PerfectField
        (P.asIdeal.under (𝓞 K)).ResidueField :=
    PerfectField.ofFinite
  apply Ideal.ramificationIdx_eq_one_iff.mp
  exact hRamification.trans hChosenRamification
