/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Completion.UnramifiedComparison.IdealToCompletion
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.Henselian.AlgebraicExtensionUniqueness
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.LocalRingEquiv
/-!
# Ramification index and finite-place completion

The ideal-theoretic ramification index at the centre of a finite-place
extension agrees with the ramification index of the corresponding explicit
localized completions.  The comparison uses a global integral uniformizer:
its valuation in the completed target is the global ramification index, and
its image generates the completed base maximal ideal.
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

/-- The ramification index of the maximal ideals in the explicit localized
completions is the ramification index of the corresponding global ideals. -/
theorem chosenFinitePlace_completed_ramificationIdx'_eq_centre
    (v : HeightOneSpectrum (𝓞 K)) :
    (𝓂[ChosenFinitePlaceBaseCompletion (K := K) v] :
        Ideal 𝒪[ChosenFinitePlaceBaseCompletion (K := K) v]).ramificationIdx'
      (𝓂[ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v] :
        Ideal 𝒪[ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v]) =
      v.asIdeal.ramificationIdx'
        (finitePlaceExtensionCentre
          (K := K) (L := L) v
          (chosenFinitePlaceExtension (L := L) v)).asIdeal := by
  let vK := HeightOneSpectrum.adicAbv K v
  let w := chosenFinitePlaceExtension (L := L) v
  let W := finitePlaceExtensionCentre (K := K) (L := L) v w
  let : W.asIdeal.LiesOver v.asIdeal :=
    finitePlaceExtensionCentre_liesOver (K := K) (L := L) v w
  let E := ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v
  let πData := chosenFinitePlaceCompletionIntegralUniformizer v
  let πBase : 𝒪[vK.Completion] := πData.completionInteger
  let integerMap : 𝒪[vK.Completion] →+* 𝒪[E] :=
    algebraMap 𝒪[vK.Completion] 𝒪[E]
  let πTarget : 𝒪[E] :=
    integerMap πBase
  let eTarget : 𝒪[E] ≃+* W.adicCompletionIntegers L :=
    chosenFinitePlaceLocalizedIntegerRingEquiv (K := K) (L := L) v
  let eGlobal : ℕ := v.asIdeal.ramificationIdx' W.asIdeal
  have hπTargetField :
      (eTarget πTarget : W.adicCompletion L) =
        algebraMap L (W.adicCompletion L)
          (algebraMap K L (πData.integer : K)) := by
    change
      finitePlaceExtensionAdicCompletionRingEquiv
            (K := K) (L := L) v w
            (localizedCompletionEquivCompletion
              vK (RayClass.adicAbv_isNontrivial v) w
              (algebraMap vK.Completion E
                (πData.completionInteger : vK.Completion))) =
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
  have hπTargetValuation :
      Valued.v (eTarget πTarget : W.adicCompletion L) =
        WithZero.exp (-(eGlobal : ℤ)) := by
    rw [hπTargetField]
    calc
      Valued.v
          (algebraMap L (W.adicCompletion L)
            (algebraMap K L (πData.integer : K))) =
          W.valuation L (algebraMap K L (πData.integer : K)) :=
        HeightOneSpectrum.valuedAdicCompletion_eq_valuation'
          W (algebraMap K L (πData.integer : K))
      _ = (v.valuation K (πData.integer : K)) ^ eGlobal := by
        symm
        exact HeightOneSpectrum.valuation_liesOver
          L v W (πData.integer : K)
      _ = WithZero.exp (-1 : ℤ) ^ eGlobal := by
        rw [HeightOneSpectrum.valuation_of_algebraMap,
          πData.intValuation_eq_exp_neg_one]
      _ = WithZero.exp (eGlobal • (-1 : ℤ)) :=
        (WithZero.exp_nsmul _ _).symm
      _ = WithZero.exp (-(eGlobal : ℤ)) := by
        congr 1
        simp only [nsmul_eq_mul, mul_neg, mul_one]
  let targetDVF :
      ValuationTheory.DiscreteValuationField.DVF
        (W.adicCompletion L) :=
    { ValueGroup := WithZero (Multiplicative ℤ)
      valuation := Valued.v }
  let concreteRingEquiv :
      targetDVF.valuationSubring ≃+* W.adicCompletionIntegers L :=
    RingEquiv.subringCongr
      (show targetDVF.valuation.valuationSubring.toSubring =
        (W.adicCompletionIntegers L).toSubring by rfl)
  let πConcrete : targetDVF.valuationSubring :=
    concreteRingEquiv.symm (eTarget πTarget)
  obtain ⟨ϖ, hϖ⟩ := targetDVF.exists_uniformizer
  have hϖValuation :
      Valued.v (ϖ : W.adicCompletion L) =
        WithZero.exp (-1 : ℤ) := by
    have h := hϖ
    rw [Valuation.IsUniformizer.iff,
      Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
        (W.valuedAdicCompletion_surjective L)] at h
    exact h
  have hπConcreteMem (n : ℕ) :
      πConcrete ∈ targetDVF.maximalIdeal ^ n ↔ n ≤ eGlobal := by
    rw [ValuationTheory.DiscreteValuationField.Valuation.mem_maximalIdeal_pow_iff_valuation_le_uniformizer_pow
      targetDVF.valuation hϖ n]
    change Valued.v (πConcrete : W.adicCompletion L) ≤
      Valued.v ((ϖ : W.adicCompletion L) ^ n) ↔ n ≤ eGlobal
    have hCoe :
        (πConcrete : W.adicCompletion L) =
          (eTarget πTarget : W.adicCompletion L) := rfl
    rw [hCoe]
    rw [hπTargetValuation, map_pow, hϖValuation]
    rw [← WithZero.exp_nsmul]
    simp only [nsmul_eq_mul, mul_neg, mul_one]
    rw [WithZero.exp_le_exp]
    omega
  have hπTargetConcreteMem (n : ℕ) :
      eTarget πTarget ∈
          (IsLocalRing.maximalIdeal
            (W.adicCompletionIntegers L)) ^ n ↔
        n ≤ eGlobal := by
    have htransport :=
      ValuationTheory.ringEquiv_mem_maximalIdeal_pow_iff
        concreteRingEquiv n πConcrete
    rw [concreteRingEquiv.apply_symm_apply] at htransport
    exact htransport.trans (hπConcreteMem n)
  have hπTargetMem (n : ℕ) :
      πTarget ∈ (𝓂[E] : Ideal 𝒪[E]) ^ n ↔ n ≤ eGlobal :=
    (ValuationTheory.ringEquiv_mem_maximalIdeal_pow_iff
      eTarget n πTarget).symm.trans (hπTargetConcreteMem n)
  let baseDVF :
      ValuationTheory.DiscreteValuationField.DVF vK.Completion :=
    { ValueGroup := ValuativeRel.ValueGroupWithZero vK.Completion
      valuation := ValuativeRel.valuation vK.Completion }
  have hπBaseGenerates :
      (𝓂[vK.Completion] : Ideal 𝒪[vK.Completion]) =
        Ideal.span ({πBase} : Set 𝒪[vK.Completion]) :=
    baseDVF.maximalIdeal_eq_span_uniformizer
      πData.completionInteger_isUniformizer
  change
    (𝓂[vK.Completion] : Ideal 𝒪[vK.Completion]).ramificationIdx'
      (𝓂[E] : Ideal 𝒪[E]) = eGlobal
  apply Ideal.ramificationIdx'_spec
  · calc
      Ideal.map integerMap
          (𝓂[vK.Completion] : Ideal 𝒪[vK.Completion]) =
          Ideal.map integerMap
            (Ideal.span ({πBase} : Set 𝒪[vK.Completion])) :=
        congrArg (Ideal.map integerMap) hπBaseGenerates
      _ ≤ (𝓂[E] : Ideal 𝒪[E]) ^ eGlobal := by
        apply Ideal.map_le_iff_le_comap.mpr
        rw [Ideal.span_le]
        intro x hx
        have hxπ : x = πBase := Set.mem_singleton_iff.mp hx
        subst x
        change πTarget ∈ (𝓂[E] : Ideal 𝒪[E]) ^ eGlobal
        exact (hπTargetMem eGlobal).2 le_rfl
  · intro hdeep
    have hπDeep : πTarget ∈ (𝓂[E] : Ideal 𝒪[E]) ^ (eGlobal + 1) :=
      hdeep (Ideal.mem_map_of_mem
        integerMap
        πData.completionInteger_mem_maximalIdeal)
    exact (Nat.not_succ_le_self eGlobal)
      ((hπTargetMem (eGlobal + 1)).1 hπDeep)

/-- The ramification index computed using the integral-closure valuation
chosen for the finite local extension equals the ideal-theoretic index at
the corresponding global centre. -/
theorem chosenFinitePlace_chosenLocal_ramificationIndex_eq_centre
    (v : HeightOneSpectrum (𝓞 K)) :
    let C := ChosenFinitePlaceBaseCompletion (K := K) v;
    let E := ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v;
    letI : FiniteDimensional C E :=
      chosenFinitePlaceLocalizedFiniteDimensional (K := K) (L := L) v;
    letI : Algebra.IsSeparable C E :=
      (chosenFinitePlaceLocalizedIsGalois
        (K := K) (L := L) v).to_isSeparable;
    ValuationTheory.DiscreteValuationField.ValuedExtension.ramificationIndex
      (localCompleteDVF C).toDVF
      (chosenLocalExtensionCompleteDVF C E).toDVF =
      v.asIdeal.ramificationIdx'
        (finitePlaceExtensionCentre
          (K := K) (L := L) v
          (chosenFinitePlaceExtension (L := L) v)).asIdeal := by
  dsimp only
  let C := ChosenFinitePlaceBaseCompletion (K := K) v
  let E := ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v
  let : FiniteDimensional C E :=
    chosenFinitePlaceLocalizedFiniteDimensional (K := K) (L := L) v
  let : Algebra.IsSeparable C E :=
    (chosenFinitePlaceLocalizedIsGalois
      (K := K) (L := L) v).to_isSeparable
  let base := localCompleteDVF C
  let target := chosenLocalExtensionCompleteDVF C E
  let V := base.valuation.valuationSubring
  let : HenselianRing V (IsLocalRing.maximalIdeal V) :=
    ValuationTheory.DiscreteValuationField.Valuation.henselianRing
      base.valuation
  let : base.valuation.HasExtension target.valuation :=
    chosenLocalExtensionCompleteDVF_hasExtension C E
  let : base.valuation.HasExtension (ValuativeRel.valuation E) :=
    chosenFinitePlaceLocalizedValuationHasExtension
      (K := K) (L := L) v
  let : V.valuation.HasExtension target.valuation :=
    ⟨(Valuation.isEquiv_valuation_valuationSubring
      base.valuation).symm.trans
        (Valuation.HasExtension.val_isEquiv_comap
          (vR := base.valuation) (vA := target.valuation))⟩
  let : V.valuation.HasExtension (ValuativeRel.valuation E) :=
    ⟨(Valuation.isEquiv_valuation_valuationSubring
      base.valuation).symm.trans
        (Valuation.HasExtension.val_isEquiv_comap
          (vR := base.valuation) (vA := ValuativeRel.valuation E))⟩
  have hRing :
      target.valuation.valuationSubring =
        (ValuativeRel.valuation E).valuationSubring :=
    ValuationTheory.Henselian.valuationSubring_eq_of_henselianRing
      V target.valuation (ValuativeRel.valuation E)
  let intrinsic := (ValuativeRel.valuation E).valuationSubring
  let : Algebra base.valuationSubring intrinsic :=
    Valuation.HasExtension.instAlgebra_valuationSubring
      base.valuation (ValuativeRel.valuation E)
  let eTarget : target.valuationSubring ≃+* intrinsic :=
    RingEquiv.subringCongr
      (congrArg ValuationSubring.toSubring hRing)
  let eAlg : target.valuationSubring ≃ₐ[base.valuationSubring] intrinsic :=
    AlgEquiv.ofRingEquiv (f := eTarget) (by
      intro a
      apply Subtype.ext
      rfl)
  have htransport :=
    Ideal.ramificationIdx'_map_eq
      (base.maximalIdeal) (target.maximalIdeal) eAlg
  have hMax :
      Ideal.map eTarget target.maximalIdeal =
        IsLocalRing.maximalIdeal intrinsic :=
    ValuationTheory.ringEquiv_map_maximalIdeal eTarget
  change
    ValuationTheory.DiscreteValuationField.ValuedExtension.ramificationIndex
      base.toDVF target.toDVF = _
  calc
    ValuationTheory.DiscreteValuationField.ValuedExtension.ramificationIndex
        base.toDVF target.toDVF =
        Ideal.ramificationIdx' base.maximalIdeal target.maximalIdeal := rfl
    _ = Ideal.ramificationIdx' base.maximalIdeal
          (Ideal.map eTarget target.maximalIdeal) := htransport.symm
    _ = Ideal.ramificationIdx' base.maximalIdeal
          (IsLocalRing.maximalIdeal intrinsic) := by rw [hMax]
    _ = v.asIdeal.ramificationIdx'
          (finitePlaceExtensionCentre
            (K := K) (L := L) v
            (chosenFinitePlaceExtension (L := L) v)).asIdeal := by
      change
        (𝓂[C] : Ideal 𝒪[C]).ramificationIdx'
          (𝓂[E] : Ideal 𝒪[E]) = _
      exact chosenFinitePlace_completed_ramificationIdx'_eq_centre
        (K := K) (L := L) v

end
