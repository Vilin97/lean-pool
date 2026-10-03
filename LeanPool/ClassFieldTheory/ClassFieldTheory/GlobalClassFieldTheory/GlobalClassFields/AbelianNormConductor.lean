/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Adele.FiniteRestrictedProductBaseChange
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.UnramifiedConductor
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.NormConductor
/-!
# Unramified finite places and abelian norm conductors

For a finite abelian extension of number fields, the selected local
higher-unit exponent of the actual idèle-class norm subgroup vanishes
exactly at the finite places where the chosen completed extension is
unramified.

The converse to the general unramifiedness implication uses finite local
reciprocity.  Integral units are transported from the adic completion
used by the idèle library to the absolute-value completion used by local
class field theory, and the local conductor-zero criterion then detects
unramifiedness.
-/

@[expose] public section

open scoped NumberField NNReal ValuativeRel

noncomputable
section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open NumberField IsDedekindDomain
open AlgebraicNumberTheory.Valuations
open LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]

omit [NumberField L] in
open scoped Classical in
/-- For a finite abelian extension, the chosen finite-place norm
conductor has exponent zero exactly when the chosen completed extension
is unramified. -/
theorem
    ideleClassNormLocalHigherUnitExponent_eq_zero_iff_chosenFinitePlaceIsUnramified
    (v : HeightOneSpectrum (𝓞 K)) :
    ideleClassNormLocalHigherUnitExponent
        (K := K) (L := L) v = 0 ↔
      _root_.ChosenFinitePlaceIsUnramified
        (K := K) (L := L) v := by
  constructor
  · intro hzero
    have hadic :
        (v.adicCompletionIntegers K).units ≤
          _root_.chosenFinitePlaceLocalNormSubgroup
            (K := K) (L := L) v :=
      (ideleClassNormLocalHigherUnitExponent_eq_zero_iff
        (K := K) (L := L) v).1 hzero
    let vK := HeightOneSpectrum.adicAbv K v
    let w := _root_.chosenFinitePlaceExtension (L := L) v
    let hvK : vK.IsNontrivial :=
      RayClass.adicAbv_isNontrivial v
    let hvKna : IsNonarchimedean (vK : K → ℝ) :=
      HeightOneSpectrum.isNonarchimedean_adicAbv K v
    let hK :=
      AbsoluteValue.extensionCompletionAlgebra
        (K := K) w.1
    let : SMul K w.1.Completion := hK.toSMul
    let : Algebra vK.Completion w.1.Completion :=
      AbsoluteValue.completionAlgebra vK w.1 w.2
    let :=
      LocalClassFieldTheory.localizedCompletionGlobalAlgebra vK w
    let :=
      LocalClassFieldTheory.localizedCompletionIsScalarTower vK w
    let E := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK w
    let : FiniteDimensional vK.Completion E :=
      AlgebraicNumberTheory.Valuations.localizedCompletionModuleFinite vK hvK w
    let : IsAbelianGalois vK.Completion E :=
      LocalClassFieldTheory.localizedCompletion_isAbelianGalois
        vK hvK w
    let : NontriviallyNormedField vK.Completion :=
      absoluteValueExtensionCompletionNontriviallyNormedField
        vK hvK
    let : LocallyCompactSpace vK.Completion :=
      AbsoluteValue.Completion.locallyCompactSpace
        (_root_.finitePlaceCompletionBaseMap_isometry v)
    let : IsUltrametricDist vK.Completion :=
      completionIsUltrametricDist vK hvKna
    let : Valued vK.Completion ℝ≥0 :=
      _root_.finitePlaceCompletionValued vK hvKna
    let vBase : Valuation vK.Completion ℝ≥0 := Valued.v
    let : vBase.IsNontrivial :=
      (inferInstance :
        (NormedField.valuation
          (K := vK.Completion)).IsNontrivial)
    let : ValuativeRel vK.Completion :=
      _root_.finitePlaceCompletionValuativeRel vK hvKna
    let : vBase.Compatible :=
      Valuation.Compatible.ofValuation vBase
    let : ValuativeRel.IsNontrivial vK.Completion :=
      (ValuativeRel.isNontrivial_iff_isNontrivial vBase).2
        inferInstance
    let : IsValuativeTopology vK.Completion :=
      isValuativeTopology_of_valued_ofValuation
        vK.Completion ℝ≥0
    let : IsNonarchimedeanLocalField vK.Completion :=
      { toIsValuativeTopology := inferInstance
        toLocallyCompactSpace := inferInstance
        toIsNontrivial := inferInstance }
    let : FiniteDimensional vK.Completion w.1.Completion :=
      AlgebraicNumberTheory.Valuations.completionModuleFinite
        vK hvK w
    let : ContinuousSMul vK.Completion w.1.Completion :=
      continuousSMul_of_algebraMap _ _
        (AbsoluteValue.completionMap_isometry
          vK w.1 w.2).continuous
    let : LocallyCompactSpace w.1.Completion :=
      LocallyCompactSpace.of_finiteDimensional_of_complete
        vK.Completion w.1.Completion
    let eCompletion : E ≃ᵢ w.1.Completion :=
      { toEquiv :=
          (AlgebraicNumberTheory.Valuations.localizedCompletionEquivCompletion
            vK hvK w).toEquiv
        isometry_toFun := Isometry.of_dist_eq fun _ _ => rfl }
    let : LocallyCompactSpace E :=
      (eCompletion.toHomeomorph.locallyCompactSpace_iff).2
        inferInstance
    let : IsUltrametricDist E :=
      _root_.localizedCompletionIsUltrametricDist
        vK w hvKna
    let : Valued E ℝ≥0 :=
      _root_.localizedCompletionFinitePlaceValued
        vK w hvKna
    let : ValuativeRel E :=
      _root_.localizedCompletionFinitePlaceValuativeRel
        vK w hvKna
    let vExtension : Valuation E ℝ≥0 := Valued.v
    let : vExtension.Compatible :=
      Valuation.Compatible.ofValuation vExtension
    let vExtensionRel := ValuativeRel.valuation E
    let : Valuation.HasExtension
        (ValuativeRel.valuation vK.Completion)
        vExtensionRel :=
      _root_.localizedCompletionValuationHasExtension
        vK w hvKna
    let : vExtensionRel.IsNontrivial :=
      Valuation.IsNontrivial.of_hasExtension
        (ValuativeRel.valuation vK.Completion)
        vExtensionRel
    let : ValuativeRel.IsNontrivial E :=
      (ValuativeRel.isNontrivial_iff_isNontrivial
        vExtensionRel).2 inferInstance
    let : IsValuativeTopology E :=
      isValuativeTopology_of_valued_ofValuation E ℝ≥0
    let : IsNonarchimedeanLocalField E :=
      { toIsValuativeTopology := inferInstance
        toLocallyCompactSpace := inferInstance
        toIsNontrivial := inferInstance }
    let : Algebra 𝒪[vK.Completion] E :=
      Algebra.ofSubsemiring 𝒪[vK.Completion]
    let :
        IsIntegralClosure 𝒪[E] 𝒪[vK.Completion] E :=
      _root_.localizedCompletionIsIntegralClosureWithExtension
        vK w hvK hvKna
    let : Module.Finite 𝒪[vK.Completion] 𝒪[E] :=
      integerRing_moduleFinite_of_isIntegralClosure
        vK.Completion E
    let eField :
        vK.Completion ≃+* v.adicCompletion K :=
      _root_.finitePlaceCompletionRingEquiv v
    have hmem (x : vK.Completion) :
        eField x ∈ v.adicCompletionIntegers K ↔
          x ∈ 𝒪[vK.Completion] := by
      simpa [vK, eField] using
        (_root_.finitePlaceCompletionRingEquiv_mem_integers_iff
          v x)
    let e :
        vK.Completionˣ ≃ₜ* (v.adicCompletion K)ˣ :=
      _root_.finitePlaceCompletionUnitsContinuousMulEquiv v
    have hfield :
        LocalFieldTheory.fieldPrincipalUnits
            vK.Completion 0 ≤
          LocalFieldTheory.localNormSubgroup
            vK.Completion E := by
      intro x hx
      change
        x ∈
          (LocalFieldTheory.principalUnits
            vK.Completion 0).map
              (LocalFieldTheory.IsNonarchimedeanLocalField.integerUnitsToFieldUnits
                vK.Completion) at hx
      rcases hx with ⟨u, _hu, rfl⟩
      have hxIntegral :
          LocalFieldTheory.IsNonarchimedeanLocalField.integerUnitsToFieldUnits
              vK.Completion u ∈
            (𝒪[vK.Completion]).units := by
        rw [Submonoid.mem_units_iff]
        exact ⟨u.1.2, u.2.2⟩
      have heIntegral :
          e (LocalFieldTheory.IsNonarchimedeanLocalField.integerUnitsToFieldUnits
                vK.Completion u) ∈
            (v.adicCompletionIntegers K).units := by
        change
          Units.mapEquiv eField.toMulEquiv
                (LocalFieldTheory.IsNonarchimedeanLocalField.integerUnitsToFieldUnits
                  vK.Completion u) ∈
            (v.adicCompletionIntegers K).units
        exact
          (_root_.unitsMapEquiv_mem_units_iff
            eField.toMulEquiv
            (𝒪[vK.Completion]).toSubmonoid
            (v.adicCompletionIntegers K).toSubmonoid
            hmem
            (LocalFieldTheory.IsNonarchimedeanLocalField.integerUnitsToFieldUnits
              vK.Completion u)).2 hxIntegral
      have heNorm := hadic heIntegral
      change
        e (LocalFieldTheory.IsNonarchimedeanLocalField.integerUnitsToFieldUnits
              vK.Completion u) ∈
          (LocalFieldTheory.localNormSubgroup
            vK.Completion E).map e.toMonoidHom at heNorm
      rcases heNorm with ⟨z, hz, hze⟩
      have hzEq :
          z =
            LocalFieldTheory.IsNonarchimedeanLocalField.integerUnitsToFieldUnits
              vK.Completion u :=
        e.injective hze
      exact hzEq ▸ hz
    have hlocalConductor :
        LocalClassFieldTheory.localConductorExponent
            vK.Completion E = 0 :=
      (LocalClassFieldTheory.localConductorExponent_eq_zero_iff
        vK.Completion E).2 hfield
    have hunramified :
        IsNonarchimedeanLocalField.IsUnramifiedValuedExtension
          vK.Completion E :=
      (LocalClassFieldTheory.isUnramifiedValuedExtension_iff_localConductorExponent_eq_zero
        vK.Completion E).2 hlocalConductor
    simpa [_root_.ChosenFinitePlaceIsUnramified] using
      hunramified
  · intro hunramified
    exact
      ideleClassNormLocalHigherUnitExponent_eq_zero_of_chosenUnramified
        (K := K) (L := L) v hunramified

open scoped Classical in
/-- For a finite abelian extension, the constructed norm modulus is
supported at exactly the finite places where the chosen completed
extension is ramified. -/
theorem
    mem_ideleClassNormDefiningModulus_support_iff_not_chosenFinitePlaceIsUnramified
    (v : HeightOneSpectrum (𝓞 K)) :
    v ∈
        (ideleClassNormDefiningModulus
          (K := K) (L := L)).support ↔
      ¬ _root_.ChosenFinitePlaceIsUnramified
        (K := K) (L := L) v := by
  rw [mem_ideleClassNormDefiningModulus_support_iff]
  exact
    not_congr
      ((ideleClassNormLocalHigherUnitExponent_eq_zero_iff
          (K := K) (L := L) v).symm.trans
        (ideleClassNormLocalHigherUnitExponent_eq_zero_iff_chosenFinitePlaceIsUnramified
          (K := K) (L := L) v))

end GlobalClassFields
end GlobalClassFieldTheory
