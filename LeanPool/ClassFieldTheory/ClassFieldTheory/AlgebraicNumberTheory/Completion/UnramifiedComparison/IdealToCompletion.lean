/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Completion.IntegerRingComparison
import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.RamificationIdeal
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.LocalRingEquiv
/-!
# From ideal-theoretic to completed unramifiedness

This file proves that ideal-theoretic unramifiedness at the centre of the
actual chosen finite-place extension implies unramifiedness of its localized
completion.
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

/-- A uniformizer of a finite-place completion induced by an element of the
global integer ring, together with its valuation and comparison properties. -/
structure FinitePlaceCompletionIntegralUniformizer
    {F : Type} [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) where
  /-- The inducing element of the global integer ring. -/
  integer : 𝓞 F
  /-- The corresponding element of the completion integer ring. -/
  completionInteger :
    𝒪[ChosenFinitePlaceBaseCompletion (K := F) v]
  /-- The inducing global integer has normalized valuation `-1`. -/
  intValuation_eq_exp_neg_one :
    v.intValuation integer = WithZero.exp (-1 : ℤ)
  /-- The completion element is the image of the global integer. -/
  coe_completionInteger :
    (completionInteger :
        ChosenFinitePlaceBaseCompletion (K := F) v) =
      algebraMap F
        (ChosenFinitePlaceBaseCompletion (K := F) v)
        (integer : F)
  /-- The completion element is a uniformizer for the intrinsic valuation. -/
  completionInteger_isUniformizer :
    (ValuativeRel.valuation
        (ChosenFinitePlaceBaseCompletion (K := F) v)).IsUniformizer
      (completionInteger :
        ChosenFinitePlaceBaseCompletion (K := F) v)
  /-- The completion element lies in the completion's maximal ideal. -/
  completionInteger_mem_maximalIdeal :
    completionInteger ∈
      (𝓂[ChosenFinitePlaceBaseCompletion (K := F) v] :
        Ideal
          𝒪[ChosenFinitePlaceBaseCompletion (K := F) v])

/-- A chosen global integral uniformizer and its image in a finite-place
completion. -/
noncomputable def chosenFinitePlaceCompletionIntegralUniformizer
    {F : Type} [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) :
    FinitePlaceCompletionIntegralUniformizer v := by
  let vF := HeightOneSpectrum.adicAbv F v
  let eBaseField :
      vF.Completion ≃+* v.adicCompletion F :=
    finitePlaceCompletionRingEquiv v
  let eBase :
      𝒪[vF.Completion] ≃+*
        v.adicCompletionIntegers F :=
    finitePlaceCompletionIntegerRingEquiv v
  let π : 𝓞 F :=
    Classical.choose v.intValuation_exists_uniformizer
  have hπ :
      v.intValuation π = WithZero.exp (-1 : ℤ) :=
    Classical.choose_spec v.intValuation_exists_uniformizer
  let πConcrete :
      v.adicCompletionIntegers F :=
    ⟨algebraMap (𝓞 F) (v.adicCompletion F) π, by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers]
      change Valued.v (π : v.adicCompletion F) ≤ 1
      rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
        HeightOneSpectrum.valuation_of_algebraMap, hπ]
      change WithZero.exp (-1 : ℤ) ≤ WithZero.exp 0
      rw [WithZero.exp_le_exp]
      omega⟩
  let baseDVF :
      ValuationTheory.DiscreteValuationField.DVF
        (v.adicCompletion F) :=
    { ValueGroup := WithZero (Multiplicative ℤ)
      valuation := Valued.v }
  have hπConcreteUniformizer :
      baseDVF.valuation.IsUniformizer
        (πConcrete : v.adicCompletion F) := by
    rw [Valuation.IsUniformizer.iff,
      Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
        (v.valuedAdicCompletion_surjective F)]
    change Valued.v (π : v.adicCompletion F) =
      WithZero.exp (-1 : ℤ)
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
      HeightOneSpectrum.valuation_of_algebraMap, hπ]
  let πCompletion : 𝒪[vF.Completion] :=
    eBase.symm πConcrete
  have hπCompletionField :
      (πCompletion : vF.Completion) =
        algebraMap F vF.Completion (π : F) := by
    apply eBaseField.injective
    have happ :=
      congrArg Subtype.val
        (eBase.apply_symm_apply πConcrete)
    change
      eBaseField (πCompletion : vF.Completion) =
        (πConcrete : v.adicCompletion F) at happ
    rw [happ]
    let x : WithAbs vF :=
      (WithAbs.equiv vF).symm (π : F)
    change
      (π : v.adicCompletion F) =
        finitePlaceCompletionRingHom v
          (x : vF.Completion)
    rw [finitePlaceCompletionRingHom_coe]
    rfl
  have hπCompletionMaximal :
      πCompletion ∈
        (IsLocalRing.maximalIdeal
          𝒪[vF.Completion]) := by
    have hπConcreteMaximal :
        πConcrete ∈
          (IsLocalRing.maximalIdeal
            (v.adicCompletionIntegers F)) :=
      baseDVF.uniformizer_mem_maximalIdeal
        hπConcreteUniformizer
    have hpow :
        eBase πCompletion ∈
          (IsLocalRing.maximalIdeal
              (v.adicCompletionIntegers F)) ^ 1 := by
      simpa [πCompletion] using hπConcreteMaximal
    have hmem :=
      (ValuationTheory.ringEquiv_mem_maximalIdeal_pow_iff
        eBase 1 πCompletion).1 hpow
    simpa using hmem
  have hπConcreteNotDeep :
      πConcrete ∉
        (IsLocalRing.maximalIdeal
          (v.adicCompletionIntegers F)) ^ 2 :=
    baseDVF.uniformizer_not_mem_maximalIdeal_sq
      hπConcreteUniformizer
  have hπCompletionNotDeep :
      πCompletion ∉
        (IsLocalRing.maximalIdeal
          𝒪[vF.Completion]) ^ 2 := by
    intro hdeep
    apply hπConcreteNotDeep
    simpa [πCompletion] using
      ((ValuationTheory.ringEquiv_mem_maximalIdeal_pow_iff
        eBase 2 πCompletion).2 hdeep)
  let completionDVF :
      ValuationTheory.DiscreteValuationField.DVF
        vF.Completion :=
    { ValueGroup := ValuativeRel.ValueGroupWithZero vF.Completion
      valuation := ValuativeRel.valuation vF.Completion }
  have hπCompletionUniformizer :
      completionDVF.valuation.IsUniformizer
        (πCompletion : vF.Completion) :=
    completionDVF.isUniformizer_of_mem_maximalIdeal_of_not_mem_maximalIdeal_sq
      hπCompletionMaximal hπCompletionNotDeep
  exact
    { integer := π
      completionInteger := πCompletion
      intValuation_eq_exp_neg_one := hπ
      coe_completionInteger := hπCompletionField
      completionInteger_isUniformizer :=
        hπCompletionUniformizer
      completionInteger_mem_maximalIdeal :=
        hπCompletionMaximal }

/-- If the centre of the chosen finite-place extension has ramification
index one, a global integral uniformizer remains a uniformizer after passing
to the chosen localized completion. In particular it is not in the square of
the target maximal ideal. -/
theorem chosenFinitePlace_integral_uniformizer_not_mem_maximalIdeal_sq
    (v : HeightOneSpectrum (𝓞 K))
    (π : 𝓞 K)
    (πBase :
      𝒪[ChosenFinitePlaceBaseCompletion (K := K) v])
    (hπ :
      v.intValuation π = WithZero.exp (-1 : ℤ))
    (hπBase :
      (πBase :
          ChosenFinitePlaceBaseCompletion (K := K) v) =
        algebraMap K
          (ChosenFinitePlaceBaseCompletion (K := K) v)
          (π : K))
    (hglobal :
      v.asIdeal.ramificationIdx'
          (finitePlaceExtensionCentre
            (K := K) (L := L) v
            (chosenFinitePlaceExtension (L := L) v)).asIdeal =
        1) :
    algebraMap
        𝒪[ChosenFinitePlaceBaseCompletion (K := K) v]
        𝒪[ChosenFinitePlaceLocalizedCompletion
          (K := K) (L := L) v] πBase ∉
      (𝓂[ChosenFinitePlaceLocalizedCompletion
        (K := K) (L := L) v] :
          Ideal
            𝒪[ChosenFinitePlaceLocalizedCompletion
              (K := K) (L := L) v]) ^ 2 := by
  let vK := HeightOneSpectrum.adicAbv K v
  let w := chosenFinitePlaceExtension (L := L) v
  let W :=
    finitePlaceExtensionCentre
      (K := K) (L := L) v w
  let : W.asIdeal.LiesOver v.asIdeal :=
    finitePlaceExtensionCentre_liesOver
      (K := K) (L := L) v w
  let E :=
    ChosenFinitePlaceLocalizedCompletion
      (K := K) (L := L) v
  let eTarget :
      𝒪[E] ≃+* W.adicCompletionIntegers L :=
    chosenFinitePlaceLocalizedIntegerRingEquiv
      (K := K) (L := L) v
  let πTarget : 𝒪[E] :=
    algebraMap 𝒪[vK.Completion] 𝒪[E] πBase
  change πTarget ∉
    (IsLocalRing.maximalIdeal 𝒪[E]) ^ 2
  intro hπTargetDeep
  have hπTargetConcrete :
      eTarget πTarget ∈
        (IsLocalRing.maximalIdeal
          (W.adicCompletionIntegers L)) ^ 2 :=
    (ValuationTheory.ringEquiv_mem_maximalIdeal_pow_iff
      eTarget 2 πTarget).2 hπTargetDeep
  have hπTargetField :
      (eTarget πTarget : W.adicCompletion L) =
        (algebraMap L (W.adicCompletion L)
          (algebraMap K L (π : K))) := by
    change
      finitePlaceExtensionAdicCompletionRingEquiv
            (K := K) (L := L) v w
            (localizedCompletionEquivCompletion
              vK (RayClass.adicAbv_isNontrivial v) w
              (algebraMap vK.Completion E
                (πBase : vK.Completion))) =
        _
    rw [(localizedCompletionEquivCompletion
      vK (RayClass.adicAbv_isNontrivial v) w).commutes, hπBase]
    change
      finitePlaceExtensionAdicCompletionRingEquiv
            (K := K) (L := L) v w
            (AbsoluteValue.completionMap
              vK w.1 w.2
              (algebraMap K vK.Completion
                (π : K))) =
        _
    rw [AbsoluteValue.completionMap_coe,
      finitePlaceExtensionAdicCompletionRingEquiv_toCompletion]
    rfl
  let targetDVF :
      ValuationTheory.DiscreteValuationField.DVF
        (W.adicCompletion L) :=
    { ValueGroup := WithZero (Multiplicative ℤ)
      valuation := Valued.v }
  have hπTargetValuation :
      targetDVF.valuation
          (eTarget πTarget : W.adicCompletion L) =
        WithZero.exp (-1 : ℤ) := by
    rw [hπTargetField]
    change
      Valued.v
          (algebraMap L (W.adicCompletion L)
            (algebraMap K L (π : K))) =
        WithZero.exp (-1 : ℤ)
    calc
      Valued.v
          (algebraMap L (W.adicCompletion L)
            (algebraMap K L (π : K))) =
          W.valuation L (algebraMap K L (π : K)) :=
        HeightOneSpectrum.valuedAdicCompletion_eq_valuation'
          W (algebraMap K L (π : K))
      _ =
          (v.valuation K (π : K)) ^
            v.asIdeal.ramificationIdx' W.asIdeal := by
        symm
        exact HeightOneSpectrum.valuation_liesOver
          L v W (π : K)
      _ = WithZero.exp (-1 : ℤ) := by
        rw [hglobal, pow_one,
          HeightOneSpectrum.valuation_of_algebraMap, hπ]
  have hπTargetUniformizer :
      targetDVF.valuation.IsUniformizer
        (eTarget πTarget : W.adicCompletion L) := by
    rw [Valuation.IsUniformizer.iff,
      Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
        (W.valuedAdicCompletion_surjective L)]
    exact hπTargetValuation
  exact
    (targetDVF.uniformizer_not_mem_maximalIdeal_sq
      hπTargetUniformizer) hπTargetConcrete

/-- Ramification index one at the global centre prevents the image of the
completed base maximal ideal from lying in the square of the target maximal
ideal. -/
theorem chosenFinitePlace_maximalIdeal_map_not_le_sq_of_centre_ramificationIdx_eq_one
    (v : HeightOneSpectrum (𝓞 K))
    (hglobal :
      v.asIdeal.ramificationIdx'
          (finitePlaceExtensionCentre
            (K := K) (L := L) v
            (chosenFinitePlaceExtension (L := L) v)).asIdeal =
        1) :
    ¬ (𝓂[ChosenFinitePlaceBaseCompletion (K := K) v] :
          Ideal
            𝒪[ChosenFinitePlaceBaseCompletion (K := K) v]).map
        (algebraMap
          𝒪[ChosenFinitePlaceBaseCompletion (K := K) v]
          𝒪[ChosenFinitePlaceLocalizedCompletion
            (K := K) (L := L) v]) ≤
      (𝓂[ChosenFinitePlaceLocalizedCompletion
        (K := K) (L := L) v] :
          Ideal
            𝒪[ChosenFinitePlaceLocalizedCompletion
              (K := K) (L := L) v]) ^ 2 := by
  let πData :=
    chosenFinitePlaceCompletionIntegralUniformizer v
  intro hdeep
  apply
    chosenFinitePlace_integral_uniformizer_not_mem_maximalIdeal_sq
      (K := K) (L := L) v
      πData.integer πData.completionInteger
      πData.intValuation_eq_exp_neg_one
      πData.coe_completionInteger hglobal
  exact
    hdeep
      (Ideal.mem_map_of_mem
        (algebraMap
          𝒪[ChosenFinitePlaceBaseCompletion (K := K) v]
          𝒪[ChosenFinitePlaceLocalizedCompletion
            (K := K) (L := L) v])
        πData.completionInteger_mem_maximalIdeal)

/-- Ramification index one at the global centre gives ramification index one
for the completed maximal ideals in the multiplicity formulation. -/
theorem chosenFinitePlace_maximalIdeal_ramificationIdx'_eq_one_of_centre_ramificationIdx_eq_one
    (v : HeightOneSpectrum (𝓞 K))
    (hglobal :
      v.asIdeal.ramificationIdx'
          (finitePlaceExtensionCentre
            (K := K) (L := L) v
            (chosenFinitePlaceExtension (L := L) v)).asIdeal =
        1) :
    (𝓂[ChosenFinitePlaceBaseCompletion (K := K) v] :
        Ideal
          𝒪[ChosenFinitePlaceBaseCompletion (K := K) v]).ramificationIdx'
      (𝓂[ChosenFinitePlaceLocalizedCompletion
        (K := K) (L := L) v] :
          Ideal
            𝒪[ChosenFinitePlaceLocalizedCompletion
              (K := K) (L := L) v]) =
      1 := by
  let vK := HeightOneSpectrum.adicAbv K v
  let E :=
    ChosenFinitePlaceLocalizedCompletion
      (K := K) (L := L) v
  change
    (𝓂[vK.Completion] :
        Ideal 𝒪[vK.Completion]).ramificationIdx'
      (𝓂[E] : Ideal 𝒪[E]) = 1
  let :
      IsLocalHom (algebraMap vK.Completion E) :=
    IsLocalRing.instIsLocalHomRingHomOfNontrivial
      (algebraMap vK.Completion E)
  let :
      IsLocalHom
        (algebraMap 𝒪[vK.Completion] 𝒪[E]) :=
    Valuation.HasExtension.instIsLocalHomValuationInteger
  rw [← not_ne_iff,
    Ideal.ramificationIdx'_ne_one_iff
      (IsLocalRing.map_maximalIdeal_le
        (algebraMap 𝒪[vK.Completion] 𝒪[E]))]
  exact
    chosenFinitePlace_maximalIdeal_map_not_le_sq_of_centre_ramificationIdx_eq_one
      (K := K) (L := L) v hglobal

omit [FiniteDimensional K L] in
/-- Ideal-theoretic unramifiedness gives ramification index one at the actual
centre of the chosen finite-place extension. -/
theorem finitePlaceExtensionCentre_ramificationIdx_eq_one_of_isUnramifiedAt
    (v : HeightOneSpectrum (𝓞 K))
    (hunram :
      Algebra.IsUnramifiedAt (𝓞 K)
        (finitePlaceExtensionCentre
          (K := K) (L := L) v
          (chosenFinitePlaceExtension (L := L) v)).asIdeal) :
    v.asIdeal.ramificationIdx'
        (finitePlaceExtensionCentre
          (K := K) (L := L) v
          (chosenFinitePlaceExtension (L := L) v)).asIdeal =
      1 := by
  let w := chosenFinitePlaceExtension (L := L) v
  let W :=
    finitePlaceExtensionCentre
      (K := K) (L := L) v w
  let : W.asIdeal.LiesOver v.asIdeal :=
    finitePlaceExtensionCentre_liesOver
      (K := K) (L := L) v w
  rw [Ideal.ramificationIdx'_eq_ramificationIdx
    v.asIdeal W.asIdeal v.ne_bot]
  let : Algebra.IsUnramifiedAt (𝓞 K) W.asIdeal := hunram
  exact Ideal.ramificationIdx_eq_one W.asIdeal (𝓞 K)

/-- Ramification index one at the actual global centre gives ramification
index one for the maximal ideals of the corresponding completed valued-field
extension. -/
theorem chosenFinitePlace_maximalIdeal_ramificationIdx_eq_one_of_centre_ramificationIdx_eq_one
    (v : HeightOneSpectrum (𝓞 K))
    (hglobal :
      v.asIdeal.ramificationIdx'
          (finitePlaceExtensionCentre
            (K := K) (L := L) v
            (chosenFinitePlaceExtension (L := L) v)).asIdeal =
        1) :
    (𝓂[ChosenFinitePlaceLocalizedCompletion
        (K := K) (L := L) v] :
          Ideal
            𝒪[ChosenFinitePlaceLocalizedCompletion
              (K := K) (L := L) v]).ramificationIdx
        𝒪[ChosenFinitePlaceBaseCompletion (K := K) v] =
      1 := by
  let vK := HeightOneSpectrum.adicAbv K v
  let E :=
    ChosenFinitePlaceLocalizedCompletion
      (K := K) (L := L) v
  change
    (𝓂[E] : Ideal 𝒪[E]).ramificationIdx
      𝒪[vK.Completion] = 1
  have hbaseBot :
      (𝓂[vK.Completion] : Ideal 𝒪[vK.Completion]) ≠ ⊥ :=
    Ring.ne_bot_of_isMaximal_of_not_isField
      (IsLocalRing.maximalIdeal.isMaximal
        𝒪[vK.Completion])
      (IsDiscreteValuationRing.not_isField
        𝒪[vK.Completion])
  let :
      Module.IsTorsionFree vK.Completion E :=
    DivisionSemiring.to_moduleIsTorsionFree
  let :
      Module.IsTorsionFree
        𝒪[vK.Completion] 𝒪[E] :=
    Valuation.HasExtension.instIsTorsionFreeInteger
  let :
      (𝓂[E] : Ideal 𝒪[E]).LiesOver
        (𝓂[vK.Completion] : Ideal 𝒪[vK.Completion]) := by
    exact
      ⟨(Valuation.HasExtension.maximalIdeal_comap_algebraMap_eq_maximalIdeal
        (ValuativeRel.valuation vK.Completion)
        (ValuativeRel.valuation E)).symm⟩
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx
    (𝓂[vK.Completion] : Ideal 𝒪[vK.Completion])
    (𝓂[E] : Ideal 𝒪[E]) hbaseBot]
  exact
    chosenFinitePlace_maximalIdeal_ramificationIdx'_eq_one_of_centre_ramificationIdx_eq_one
      (K := K) (L := L) v hglobal

/-- Ramification index one at the actual global centre implies
unramifiedness of the corresponding completed valued-field extension. -/
theorem chosenFinitePlaceIsUnramified_of_centre_ramificationIdx_eq_one
    (v : HeightOneSpectrum (𝓞 K))
    (hglobal :
      v.asIdeal.ramificationIdx'
          (finitePlaceExtensionCentre
            (K := K) (L := L) v
            (chosenFinitePlaceExtension (L := L) v)).asIdeal =
        1) :
    ChosenFinitePlaceIsUnramified
      (K := K) (L := L) v := by
  change
    IsNonarchimedeanLocalField.IsUnramifiedValuedExtension
      (ChosenFinitePlaceBaseCompletion (K := K) v)
      (ChosenFinitePlaceLocalizedCompletion
        (K := K) (L := L) v)
  refine
    { maximalIdeal_ramificationIdx_eq_one := ?_ }
  exact
    chosenFinitePlace_maximalIdeal_ramificationIdx_eq_one_of_centre_ramificationIdx_eq_one
      (K := K) (L := L) v hglobal

/-- Algebraic unramifiedness of the centre of the chosen extension
implies unramifiedness of the corresponding completed valued-field
extension. -/
theorem chosenFinitePlaceIsUnramified_of_isUnramifiedAt
    (v : HeightOneSpectrum (𝓞 K))
    (hunram :
      Algebra.IsUnramifiedAt (𝓞 K)
        (finitePlaceExtensionCentre
          (K := K) (L := L) v
          (chosenFinitePlaceExtension (L := L) v)).asIdeal) :
    ChosenFinitePlaceIsUnramified
      (K := K) (L := L) v := by
  apply
    chosenFinitePlaceIsUnramified_of_centre_ramificationIdx_eq_one
      (K := K) (L := L) v
  exact
    finitePlaceExtensionCentre_ramificationIdx_eq_one_of_isUnramifiedAt
      (K := K) (L := L) v hunram
