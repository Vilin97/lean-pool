/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Adele.IntegralLocalFactor
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.HilbertRamification.DecompositionFieldLocalization
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.Completion.FiniteLocalization
import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuativeExtension
/-!
# Valuation rings of algebraic localizations

This file equips nonarchimedean absolute-value completions and their algebraic
localizations with the norm-induced valuation structures. It identifies the
localized valuation ring with the integral closure of the base valuation ring.
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

section LocalValuation

variable (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK L)

omit [NumberField K] in
/-- A nonarchimedean absolute value makes its completion an ultrametric
space. -/
theorem completionIsUltrametricDist
    (hvKna : IsNonarchimedean (vK : K → ℝ)) :
    IsUltrametricDist vK.Completion :=
  IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
    (AbsoluteValue.completionAbsoluteValue_isNonarchimedean
      vK hvKna)

/-- The norm-induced valued-field structure on a nonarchimedean completion. -/
@[reducible]
noncomputable def finitePlaceCompletionValued
    (hvKna : IsNonarchimedean (vK : K → ℝ)) :
    Valued vK.Completion ℝ≥0 :=
  letI : IsUltrametricDist vK.Completion :=
    completionIsUltrametricDist vK hvKna
  NormedField.toValued

/-- The valuation relation induced by the norm valuation on a
nonarchimedean completion. -/
@[reducible]
noncomputable def finitePlaceCompletionValuativeRel
    (hvKna : IsNonarchimedean (vK : K → ℝ)) :
    ValuativeRel vK.Completion := by
  letI : Valued vK.Completion ℝ≥0 :=
    finitePlaceCompletionValued vK hvKna
  exact ValuativeRel.ofValuation
    (Valued.v : Valuation vK.Completion ℝ≥0)

omit [NumberField K] in
/-- Membership in the valuation ring of a nonarchimedean completion is
equivalent to the usual norm bound by one, for the canonical norm-induced
valuation used in this file. -/
theorem finitePlaceCompletion_mem_integers_iff_norm_le_one
    (hvKna : IsNonarchimedean (vK : K → ℝ))
    (x : vK.Completion) :
    letI : Valued vK.Completion ℝ≥0 :=
      finitePlaceCompletionValued vK hvKna
    letI : ValuativeRel vK.Completion :=
      finitePlaceCompletionValuativeRel vK hvKna
    x ∈ 𝒪[vK.Completion] ↔ ‖x‖ ≤ 1 := by
  let : Valued vK.Completion ℝ≥0 :=
    finitePlaceCompletionValued vK hvKna
  let ν : Valuation vK.Completion ℝ≥0 := Valued.v
  let : ValuativeRel vK.Completion :=
    finitePlaceCompletionValuativeRel vK hvKna
  rw [Valuation.mem_integer_iff,
    ← map_one (ValuativeRel.valuation vK.Completion),
    ← Valuation.Compatible.vle_iff_le
      (v := ValuativeRel.valuation vK.Completion)]
  change ν x ≤ ν 1 ↔ _
  simp only [map_one]
  change ‖x‖₊ ≤ 1 ↔ ‖x‖ ≤ 1
  exact NNReal.coe_le_coe

omit [NumberField K] [NumberField L] [FiniteDimensional K L]
    [IsGalois K L] in
/-- A chosen localization above a nonarchimedean place inherits an
ultrametric distance. -/
theorem localizedCompletionIsUltrametricDist
    (hvKna : IsNonarchimedean (vK : K → ℝ)) :
    IsUltrametricDist (LocalizedCompletion vK w) := by
  let hw : IsNonarchimedean (w.1 : L → ℝ) :=
    absoluteValueExtension_isNonarchimedean
      vK hvKna w
  let : IsUltrametricDist w.1.Completion :=
    IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
      (AbsoluteValue.completionAbsoluteValue_isNonarchimedean
        w.1 hw)
  infer_instance

/-- The norm-induced valued-field structure on the chosen algebraic
localization. -/
@[reducible]
noncomputable def localizedCompletionFinitePlaceValued
    (hvKna : IsNonarchimedean (vK : K → ℝ)) :
    Valued (LocalizedCompletion vK w) ℝ≥0 :=
  letI : IsUltrametricDist (LocalizedCompletion vK w) :=
    localizedCompletionIsUltrametricDist vK w hvKna
  NormedField.toValued

/-- The valuation relation induced by the norm valuation on the chosen
algebraic localization. -/
@[reducible]
noncomputable def localizedCompletionFinitePlaceValuativeRel
    (hvKna : IsNonarchimedean (vK : K → ℝ)) :
    ValuativeRel (LocalizedCompletion vK w) := by
  letI : Valued (LocalizedCompletion vK w) ℝ≥0 :=
    localizedCompletionFinitePlaceValued vK w hvKna
  exact ValuativeRel.ofValuation
    (Valued.v : Valuation (LocalizedCompletion vK w) ℝ≥0)

omit [NumberField K] [NumberField L] [FiniteDimensional K L]
    [IsGalois K L] in
/-- Membership in the valuation ring of a chosen algebraic localization is
equivalent to the usual norm bound by one, for the canonical norm-induced
valuation used in this file. -/
theorem localizedCompletion_mem_integers_iff_norm_le_one
    (hvKna : IsNonarchimedean (vK : K → ℝ))
    (x : LocalizedCompletion vK w) :
    letI : Valued (LocalizedCompletion vK w) ℝ≥0 :=
      localizedCompletionFinitePlaceValued vK w hvKna
    letI : ValuativeRel (LocalizedCompletion vK w) :=
      localizedCompletionFinitePlaceValuativeRel vK w hvKna
    x ∈ 𝒪[LocalizedCompletion vK w] ↔ ‖x‖ ≤ 1 := by
  let : Valued (LocalizedCompletion vK w) ℝ≥0 :=
    localizedCompletionFinitePlaceValued vK w hvKna
  let ν : Valuation (LocalizedCompletion vK w) ℝ≥0 := Valued.v
  let : ValuativeRel (LocalizedCompletion vK w) :=
    localizedCompletionFinitePlaceValuativeRel vK w hvKna
  rw [Valuation.mem_integer_iff,
    ← map_one (ValuativeRel.valuation (LocalizedCompletion vK w)),
    ← Valuation.Compatible.vle_iff_le
      (v := ValuativeRel.valuation (LocalizedCompletion vK w))]
  change ν x ≤ ν 1 ↔ _
  simp only [map_one]
  change ‖x‖₊ ≤ 1 ↔ ‖x‖ ≤ 1
  exact NNReal.coe_le_coe

omit [NumberField K] [NumberField L] [IsGalois K L] in
/-- The norm-defined integer ring of the chosen localization is the
integral closure of the norm-defined integer ring of the completed base.
This is the concrete Henselian source of the local integer-ring action. -/
theorem localizedCompletion_integerRing_eq_integralClosure
    (hvK : vK.IsNontrivial)
    (hvKna : IsNonarchimedean (vK : K → ℝ)) :
    letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI := AbsoluteValue.completionAlgebra vK w.1 w.2
    letI : Valued vK.Completion ℝ≥0 :=
      finitePlaceCompletionValued vK hvKna
    letI : ValuativeRel vK.Completion :=
      finitePlaceCompletionValuativeRel vK hvKna
    letI : Valued (LocalizedCompletion vK w) ℝ≥0 :=
      localizedCompletionFinitePlaceValued vK w hvKna
    letI : ValuativeRel (LocalizedCompletion vK w) :=
      localizedCompletionFinitePlaceValuativeRel vK w hvKna
    (ValuativeRel.valuation
        (LocalizedCompletion vK w)).integer =
      (integralClosure
        (ValuativeRel.valuation vK.Completion).integer
        (LocalizedCompletion vK w)).toSubring := by
  let hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  let : SMul K w.1.Completion := hK.toSMul
  let := AbsoluteValue.completionAlgebra vK w.1 w.2
  let : Valued vK.Completion ℝ≥0 :=
    finitePlaceCompletionValued vK hvKna
  let : ValuativeRel vK.Completion :=
    finitePlaceCompletionValuativeRel vK hvKna
  let : Valued (LocalizedCompletion vK w) ℝ≥0 :=
    localizedCompletionFinitePlaceValued vK w hvKna
  let : ValuativeRel (LocalizedCompletion vK w) :=
    localizedCompletionFinitePlaceValuativeRel vK w hvKna
  let aC := AbsoluteValue.completionAbsoluteValue vK
  let bE :=
    AbsoluteValue.algebraicLocalizationAbsoluteValue
      vK w.1 w.2
  let haC :
      LubinTate.Valuations.NonarchimedeanAbsoluteValue aC :=
    (AbsoluteValue.isNonarchimedean_iff_bounded_nat aC).1
      (AbsoluteValue.completionAbsoluteValue_isNonarchimedean
        vK hvKna)
  let hbE :
      LubinTate.Valuations.NonarchimedeanAbsoluteValue bE :=
    (AbsoluteValue.isNonarchimedean_iff_bounded_nat bE).1
      (absoluteValueExtension_isNonarchimedean
        aC
        (AbsoluteValue.completionAbsoluteValue_isNonarchimedean
          vK hvKna)
        ⟨bE,
          AbsoluteValue.algebraicLocalizationAbsoluteValue_extends
            vK w.1 w.2⟩)
  let va := absoluteValueExponentialValuation aC haC
  let vb := absoluteValueExponentialValuation bE hbE
  let : Module.Finite vK.Completion
      (LocalizedCompletion vK w) :=
    localizedCompletionModuleFinite vK hvK w
  let : Algebra.IsAlgebraic vK.Completion
      (LocalizedCompletion vK w) :=
    Algebra.IsAlgebraic.of_finite
      vK.Completion (LocalizedCompletion vK w)
  have hVaAbs :
      LubinTate.Valuations.exponentialValuationSubringAsValuationSubring va =
        absoluteValueValuationSubring aC haC :=
    associatedAbsoluteValue_valuationSubring_eq
      va (Real.exp 1) aC haC
        (absoluteValueExponentialValuation_associated aC haC)
  have hVbAbs :
      LubinTate.Valuations.exponentialValuationSubringAsValuationSubring vb =
        absoluteValueValuationSubring bE hbE :=
    associatedAbsoluteValue_valuationSubring_eq
      vb (Real.exp 1) bE hbE
        (absoluteValueExponentialValuation_associated bE hbE)
  have hVa :
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring
        va).toSubring =
        (ValuativeRel.valuation vK.Completion).integer := by
    rw [hVaAbs]
    ext x
    change
      x ∈ absoluteValueValuationSubring aC haC ↔
        x ∈ (ValuativeRel.valuation vK.Completion).integer
    rw [mem_absoluteValueValuationSubring_iff,
      finitePlaceCompletion_mem_integers_iff_norm_le_one]
    rfl
  have hVb :
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring
        vb).toSubring =
        (ValuativeRel.valuation
          (LocalizedCompletion vK w)).integer := by
    rw [hVbAbs]
    ext x
    change
      x ∈ absoluteValueValuationSubring bE hbE ↔
        x ∈ (ValuativeRel.valuation
          (LocalizedCompletion vK w)).integer
    rw [mem_absoluteValueValuationSubring_iff,
      localizedCompletion_mem_integers_iff_norm_le_one]
    rfl
  have hhensAbs :
      ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
        (absoluteValueValuationSubring aC haC).valuation :=
    henselianValuation_of_complete aC
      ((absoluteValueCompleteness_completeSpace_withAbs_iff_complete aC).1
        (AbsoluteValue.completionAbsoluteValue_complete vK))
      haC
  have hhens :
      ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
        (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring
          va).valuation := by
    rw [hVaAbs]
    exact hhensAbs
  have hExt : ∀ x : vK.Completion,
      vb (algebraMap vK.Completion
        (LocalizedCompletion vK w) x) = va x :=
    absoluteValueExponentialValuation_extends
      aC bE haC hbE
      (AbsoluteValue.algebraicLocalizationAbsoluteValue_extends
        vK w.1 w.2)
  let W :=
    LubinTate.Valuations.exponentialValuationSubringAsValuationSubring va
  let : Algebra W (LocalizedCompletion vK w) := inferInstance
  have hclosure :=
    exponentialValuationSubring_eq_integralClosure_of_henselian
      va vb hExt hhens
  let O := (ValuativeRel.valuation vK.Completion).integer
  have hWO : W.toSubring = O := by
    simpa only [W, O] using hVa
  let eWO : W ≃+* O :=
    { toFun := fun x =>
        ⟨x, by
          rw [← hWO]
          exact x.property⟩
      invFun := fun x =>
        ⟨x, by
          change (x : vK.Completion) ∈ W.toSubring
          rw [hWO]
          exact x.property⟩
      left_inv := fun x ↦ by
        apply Subtype.ext
        rfl
      right_inv := fun x ↦ by
        apply Subtype.ext
        rfl
      map_mul' := fun x y ↦ by
        apply Subtype.ext
        rfl
      map_add' := fun x y ↦ by
        apply Subtype.ext
        rfl }
  have heWO :
      (algebraMap O (LocalizedCompletion vK w)).comp
          eWO.toRingHom =
        algebraMap W (LocalizedCompletion vK w) := by
    ext x
    rw [RingHom.comp_apply,
      IsScalarTower.algebraMap_apply O vK.Completion,
      IsScalarTower.algebraMap_apply W vK.Completion]
    rfl
  ext x
  change
    x ∈ (ValuativeRel.valuation
      (LocalizedCompletion vK w)).integer ↔
      IsIntegral O x
  constructor
  · intro hx
    have hxv :
        x ∈
          (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring
            vb).toSubring := by
      rw [hVb]
      exact hx
    rw [hclosure] at hxv
    have hxW : IsIntegral W x := hxv
    exact (eWO.isIntegral_iff heWO x).1 hxW
  · intro hx
    have hxW : IsIntegral W x :=
      (eWO.isIntegral_iff heWO x).2 hx
    have hxv :
        x ∈
          (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring
            vb).toSubring := by
      rw [hclosure]
      exact hxW
    rw [← hVb]
    exact hxv

omit [NumberField K] [NumberField L] [IsGalois K L] in
/-- The norm-defined integer ring of the chosen localization is the
actual integral closure of the norm-defined completed-base integer ring. -/
theorem localizedCompletionIsIntegralClosure
    (hvK : vK.IsNontrivial)
    (hvKna : IsNonarchimedean (vK : K → ℝ)) :
    letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI := AbsoluteValue.completionAlgebra vK w.1 w.2
    letI : Valued vK.Completion ℝ≥0 :=
      finitePlaceCompletionValued vK hvKna
    letI : ValuativeRel vK.Completion :=
      finitePlaceCompletionValuativeRel vK hvKna
    letI : Valued (LocalizedCompletion vK w) ℝ≥0 :=
      localizedCompletionFinitePlaceValued vK w hvKna
    letI : ValuativeRel (LocalizedCompletion vK w) :=
      localizedCompletionFinitePlaceValuativeRel vK w hvKna
    IsIntegralClosure
      𝒪[LocalizedCompletion vK w]
      𝒪[vK.Completion]
      (LocalizedCompletion vK w) := by
  let hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  let : SMul K w.1.Completion := hK.toSMul
  let := AbsoluteValue.completionAlgebra vK w.1 w.2
  let : Valued vK.Completion ℝ≥0 :=
    finitePlaceCompletionValued vK hvKna
  let : ValuativeRel vK.Completion :=
    finitePlaceCompletionValuativeRel vK hvKna
  let : Valued (LocalizedCompletion vK w) ℝ≥0 :=
    localizedCompletionFinitePlaceValued vK w hvKna
  let : ValuativeRel (LocalizedCompletion vK w) :=
    localizedCompletionFinitePlaceValuativeRel vK w hvKna
  let h :=
    localizedCompletion_integerRing_eq_integralClosure
      vK w hvK hvKna
  refine
    { algebraMap_injective :=
        (ValuativeRel.valuation
          (LocalizedCompletion vK w)).integer.subtype_injective
      isIntegral_iff := ?_ }
  intro x
  constructor
  · intro hx
    have hxO : x ∈ 𝒪[LocalizedCompletion vK w] := by
      rw [h]
      exact hx
    exact ⟨⟨x, hxO⟩, rfl⟩
  · rintro ⟨y, rfl⟩
    change (y : LocalizedCompletion vK w) ∈
      (integralClosure 𝒪[vK.Completion]
        (LocalizedCompletion vK w)).toSubring
    rw [← h]
    exact y.property

omit [NumberField K] [NumberField L] [FiniteDimensional K L]
    [IsGalois K L] in
/-- The intrinsic norm valuations on the completed base and on the
chosen localization form an extension pair. -/
theorem localizedCompletionValuationHasExtension
    (hvKna : IsNonarchimedean (vK : K → ℝ)) :
    letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI := AbsoluteValue.completionAlgebra vK w.1 w.2
    letI : Valued vK.Completion ℝ≥0 :=
      finitePlaceCompletionValued vK hvKna
    letI : ValuativeRel vK.Completion :=
      finitePlaceCompletionValuativeRel vK hvKna
    letI : Valued (LocalizedCompletion vK w) ℝ≥0 :=
      localizedCompletionFinitePlaceValued vK w hvKna
    letI : ValuativeRel (LocalizedCompletion vK w) :=
      localizedCompletionFinitePlaceValuativeRel vK w hvKna
    Valuation.HasExtension
      (ValuativeRel.valuation vK.Completion)
      (ValuativeRel.valuation (LocalizedCompletion vK w)) := by
  let hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  let : SMul K w.1.Completion := hK.toSMul
  let := AbsoluteValue.completionAlgebra vK w.1 w.2
  let : Valued vK.Completion ℝ≥0 :=
    finitePlaceCompletionValued vK hvKna
  let : ValuativeRel vK.Completion :=
    finitePlaceCompletionValuativeRel vK hvKna
  let : Valued (LocalizedCompletion vK w) ℝ≥0 :=
    localizedCompletionFinitePlaceValued vK w hvKna
  let : ValuativeRel (LocalizedCompletion vK w) :=
    localizedCompletionFinitePlaceValuativeRel vK w hvKna
  apply Valuation.HasExtension.ofComapInteger
  ext x
  rw [Subring.mem_comap,
    localizedCompletion_mem_integers_iff_norm_le_one,
    finitePlaceCompletion_mem_integers_iff_norm_le_one]
  have h :=
    AbsoluteValue.algebraicLocalizationAbsoluteValue_extends
      vK w.1 w.2 x
  change
    AbsoluteValue.algebraicLocalizationAbsoluteValue
          vK w.1 w.2
          (algebraMap vK.Completion
            (LocalizedCompletion vK w) x) ≤ 1 ↔
      AbsoluteValue.completionAbsoluteValue vK x ≤ 1
  rw [h]

omit [NumberField K] [NumberField L] [IsGalois K L] in
/-- The integral-closure certificate with the canonical algebra structure
on valuation rings supplied by `Valuation.HasExtension`. -/
theorem localizedCompletionIsIntegralClosureWithExtension
    (hvK : vK.IsNontrivial)
    (hvKna : IsNonarchimedean (vK : K → ℝ)) :
    letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI := AbsoluteValue.completionAlgebra vK w.1 w.2
    letI : Valued vK.Completion ℝ≥0 :=
      finitePlaceCompletionValued vK hvKna
    letI : ValuativeRel vK.Completion :=
      finitePlaceCompletionValuativeRel vK hvKna
    letI : Valued (LocalizedCompletion vK w) ℝ≥0 :=
      localizedCompletionFinitePlaceValued vK w hvKna
    letI : ValuativeRel (LocalizedCompletion vK w) :=
      localizedCompletionFinitePlaceValuativeRel vK w hvKna
    letI : Algebra 𝒪[vK.Completion] (LocalizedCompletion vK w) :=
      Algebra.ofSubsemiring 𝒪[vK.Completion]
    letI := localizedCompletionValuationHasExtension vK w hvKna
    IsIntegralClosure
      𝒪[LocalizedCompletion vK w]
      𝒪[vK.Completion]
      (LocalizedCompletion vK w) := by
  let hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  let : SMul K w.1.Completion := hK.toSMul
  let := AbsoluteValue.completionAlgebra vK w.1 w.2
  let : Valued vK.Completion ℝ≥0 :=
    finitePlaceCompletionValued vK hvKna
  let : ValuativeRel vK.Completion :=
    finitePlaceCompletionValuativeRel vK hvKna
  let : Valued (LocalizedCompletion vK w) ℝ≥0 :=
    localizedCompletionFinitePlaceValued vK w hvKna
  let : ValuativeRel (LocalizedCompletion vK w) :=
    localizedCompletionFinitePlaceValuativeRel vK w hvKna
  let : Algebra 𝒪[vK.Completion] (LocalizedCompletion vK w) :=
    Algebra.ofSubsemiring 𝒪[vK.Completion]
  let := localizedCompletionValuationHasExtension vK w hvKna
  let h :=
    localizedCompletion_integerRing_eq_integralClosure
      vK w hvK hvKna
  refine
    { algebraMap_injective :=
        (ValuativeRel.valuation
          (LocalizedCompletion vK w)).integer.subtype_injective
      isIntegral_iff := ?_ }
  intro x
  constructor
  · intro hx
    have hxO : x ∈ 𝒪[LocalizedCompletion vK w] := by
      rw [h]
      exact hx
    exact ⟨⟨x, hxO⟩, rfl⟩
  · rintro ⟨y, rfl⟩
    have hyO :
        algebraMap 𝒪[LocalizedCompletion vK w]
            (LocalizedCompletion vK w) y ∈
          𝒪[LocalizedCompletion vK w] := by
      change (y : LocalizedCompletion vK w) ∈
        𝒪[LocalizedCompletion vK w]
      exact y.property
    exact (SetLike.ext_iff.mp h _).1 hyO


end LocalValuation
