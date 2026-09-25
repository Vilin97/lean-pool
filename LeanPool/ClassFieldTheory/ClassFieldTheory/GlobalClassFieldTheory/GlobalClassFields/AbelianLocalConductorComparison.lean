/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.AbelianNormConductor
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.FinitePlaceArtin.Construction
/-!
# Comparison of global and local conductor exponents

At a finite place, the absolute-value completion used by local class field
theory is canonically equivalent to the adic completion used by the idèle and
ray-class libraries.  This file proves that the equivalence identifies their
principal-unit filtrations.  For a finite abelian extension, it then identifies
the local exponent occurring in the idèle-class norm conductor with the
conductor exponent of the chosen localized extension.
-/

open scoped NumberField NNReal ValuativeRel

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open NumberField IsDedekindDomain
open LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField

variable {K : Type} [Field K] [NumberField K]

open scoped Classical in
/-- The canonical comparison between the two finite-place completion models
identifies the field principal-unit filtration with the ray-class higher-unit
filtration. -/
theorem finitePlaceFieldPrincipalUnits_map_eq_localHigherUnitGroup
    (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    let vK := HeightOneSpectrum.adicAbv K v
    let hvKna : IsNonarchimedean (vK : K → ℝ) :=
      HeightOneSpectrum.isNonarchimedean_adicAbv K v
    letI : Valued vK.Completion ℝ≥0 :=
      _root_.GlobalClassFieldTheory.Reciprocity.finitePlaceArtinCompletionValued
        vK hvKna
    letI : ValuativeRel vK.Completion :=
      _root_.GlobalClassFieldTheory.Reciprocity.finitePlaceLocalArtinCompletionValuativeRel v
    (LocalFieldTheory.fieldPrincipalUnits vK.Completion n).map
        (_root_.finitePlaceCompletionUnitsContinuousMulEquiv v).toMonoidHom =
      RayClass.localHigherUnitGroup v n := by
  let vK := HeightOneSpectrum.adicAbv K v
  let hvKna : IsNonarchimedean (vK : K → ℝ) :=
    HeightOneSpectrum.isNonarchimedean_adicAbv K v
  let : Valued vK.Completion ℝ≥0 :=
    _root_.GlobalClassFieldTheory.Reciprocity.finitePlaceArtinCompletionValued
      vK hvKna
  let : ValuativeRel vK.Completion :=
    _root_.GlobalClassFieldTheory.Reciprocity.finitePlaceLocalArtinCompletionValuativeRel v
  let eField : vK.Completion ≃+* v.adicCompletion K :=
    _root_.finitePlaceCompletionRingEquiv v
  let eIntegers :
      𝒪[vK.Completion] ≃+* v.adicCompletionIntegers K :=
    _root_.finitePlaceCompletionIntegerRingEquiv v
  let eIntegralUnits :
      𝒪[vK.Completion]ˣ ≃*
        (v.adicCompletionIntegers K).units :=
    (Units.mapEquiv eIntegers.toMulEquiv).trans
      (v.adicCompletionIntegers K).toSubmonoid.unitsEquivUnitsType.symm
  let e :
      vK.Completionˣ ≃ₜ* (v.adicCompletion K)ˣ :=
    _root_.finitePlaceCompletionUnitsContinuousMulEquiv v
  have heField (u : 𝒪[vK.Completion]ˣ) :
      (eIntegralUnits u : (v.adicCompletion K)ˣ) =
        e (LocalFieldTheory.IsNonarchimedeanLocalField.integerUnitsToFieldUnits
          vK.Completion u) := by
    apply Units.ext
    change
      eField ((u : 𝒪[vK.Completion]) : vK.Completion) =
        eField ((u : 𝒪[vK.Completion]) : vK.Completion)
    rfl
  have hePrincipal (u : 𝒪[vK.Completion]ˣ) :
      RayClass.localHigherUnitMap v n (eIntegralUnits u) = 1 ↔
        u ∈ LocalFieldTheory.principalUnits vK.Completion n := by
    rw [RayClass.localHigherUnitMap_eq_one_iff,
      LocalFieldTheory.mem_principalUnits_iff]
    have hvalue :
        RayClass.localIntegralValue v (eIntegralUnits u) =
          eIntegers (u : 𝒪[vK.Completion]) := by
      change
        ((v.adicCompletionIntegers K).toSubmonoid.unitsEquivUnitsType
            (eIntegralUnits u) :
          (v.adicCompletionIntegers K)ˣ).1 =
            eIntegers (u : 𝒪[vK.Completion])
      simp [eIntegralUnits]
    rw [hvalue, ← eIntegers.map_one, ← eIntegers.map_sub]
    exact
      ValuationTheory.ringEquiv_mem_maximalIdeal_pow_iff
        eIntegers n ((u : 𝒪[vK.Completion]) - 1)
  ext x
  constructor
  · rintro ⟨z, ⟨u, hu, rfl⟩, rfl⟩
    apply (RayClass.mem_localHigherUnitGroup_iff v n _).2
    exact ⟨eIntegralUnits u, heField u, (hePrincipal u).2 hu⟩
  · intro hx
    obtain ⟨y, hyx, hy⟩ :=
      (RayClass.mem_localHigherUnitGroup_iff v n x).1 hx
    let u : 𝒪[vK.Completion]ˣ := eIntegralUnits.symm y
    have huy : eIntegralUnits u = y :=
      eIntegralUnits.apply_symm_apply y
    refine
      ⟨LocalFieldTheory.IsNonarchimedeanLocalField.integerUnitsToFieldUnits
          vK.Completion u,
        ⟨u, ?_, rfl⟩, ?_⟩
    · apply (hePrincipal u).1
      simpa only [huy] using hy
    · calc
        e (LocalFieldTheory.IsNonarchimedeanLocalField.integerUnitsToFieldUnits
              vK.Completion u) =
            (eIntegralUnits u : (v.adicCompletion K)ˣ) :=
          (heField u).symm
        _ = y := congrArg Subtype.val huy
        _ = x := hyx

open scoped Classical in
open _root_.GlobalClassFieldTheory.Reciprocity renaming
  finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField →
    finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField in
/-- A ray-class higher unit has valuation zero after transport to the
absolute-value completion used by the finite-place Artin map.  This is the
pointwise endpoint of
`finitePlaceFieldPrincipalUnits_map_eq_localHigherUnitGroup`; consumers need
not reopen the transported principal-unit subgroup. -/
theorem finitePlaceCompletion_valuationMap_eq_zero_of_mem_localHigherUnitGroup
    (v : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (x : (v.adicCompletion K)ˣ)
    (hx : x ∈ RayClass.localHigherUnitGroup v n) :
    let vK := HeightOneSpectrum.adicAbv K v
    letI : ValuativeRel vK.Completion :=
      _root_.GlobalClassFieldTheory.Reciprocity.finitePlaceLocalArtinCompletionValuativeRel v
    letI : IsNonarchimedeanLocalField vK.Completion :=
      finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
    IsNonarchimedeanLocalField.valuationMap vK.Completion
        (Additive.ofMul
          ((_root_.finitePlaceCompletionUnitsContinuousMulEquiv v).symm x)) =
      0 := by
  let vK := HeightOneSpectrum.adicAbv K v
  let : ValuativeRel vK.Completion :=
    _root_.GlobalClassFieldTheory.Reciprocity.finitePlaceLocalArtinCompletionValuativeRel v
  let : IsNonarchimedeanLocalField vK.Completion :=
    finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
  have hxMap :
      x ∈
        (LocalFieldTheory.fieldPrincipalUnits vK.Completion n).map
          (_root_.finitePlaceCompletionUnitsContinuousMulEquiv v).toMonoidHom := by
    dsimp only [vK]
    rw [finitePlaceFieldPrincipalUnits_map_eq_localHigherUnitGroup v n]
    exact hx
  have hxPrincipal :
      (_root_.finitePlaceCompletionUnitsContinuousMulEquiv v).symm x ∈
        LocalFieldTheory.fieldPrincipalUnits vK.Completion n :=
    (Subgroup.mem_map_equiv
      (f := (_root_.finitePlaceCompletionUnitsContinuousMulEquiv v).toMulEquiv)).mp
        hxMap
  change
    (_root_.finitePlaceCompletionUnitsContinuousMulEquiv v).symm x ∈
      (LocalFieldTheory.principalUnits vK.Completion n).map
        (IsNonarchimedeanLocalField.integerUnitsToFieldUnits
          vK.Completion) at hxPrincipal
  rcases hxPrincipal with ⟨u, _hu, hu⟩
  rw [← hu]
  dsimp only
  rw [IsNonarchimedeanLocalField.valuationMap_apply]
  exact
    IsNonarchimedeanLocalField.v_integerUnitsToFieldUnits
      vK.Completion u

variable
    {L : Type}
    [Field L] [NumberField L] [Algebra K L]

section Galois

variable [IsGalois K L]

open scoped Classical in
/-- At a chosen finite place, containment of the ray-class higher-unit group
in the transported local norm subgroup is equivalent to containment of the
corresponding field principal-unit group in the local norm subgroup. -/
theorem
    localHigherUnitGroup_le_normSubgroup_iff_fieldPrincipalUnits_le_normSubgroup
    (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    let vK := HeightOneSpectrum.adicAbv K v
    let hvK : vK.IsNontrivial :=
      RayClass.adicAbv_isNontrivial v
    let hvKna : IsNonarchimedean (vK : K → ℝ) :=
      HeightOneSpectrum.isNonarchimedean_adicAbv K v
    let w := _root_.chosenFinitePlaceExtension (L := L) v
    letI hK :=
      AbsoluteValue.extensionCompletionAlgebra
        (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI : Algebra vK.Completion w.1.Completion :=
      AbsoluteValue.completionAlgebra vK w.1 w.2
    letI :=
      LocalClassFieldTheory.localizedCompletionGlobalAlgebra vK w
    letI :=
      LocalClassFieldTheory.localizedCompletionIsScalarTower vK w
    let E := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK w
    letI : FiniteDimensional vK.Completion E :=
      AlgebraicNumberTheory.Valuations.localizedCompletionModuleFinite vK hvK w
    letI : Valued vK.Completion ℝ≥0 :=
      _root_.finitePlaceCompletionValued vK hvKna
    letI : ValuativeRel vK.Completion :=
      _root_.finitePlaceCompletionValuativeRel vK hvKna
    RayClass.localHigherUnitGroup v n ≤
        _root_.chosenFinitePlaceLocalNormSubgroup
          (K := K) (L := L) v ↔
      LocalFieldTheory.fieldPrincipalUnits vK.Completion n ≤
        LocalFieldTheory.localNormSubgroup vK.Completion E := by
  let vK := HeightOneSpectrum.adicAbv K v
  let hvK : vK.IsNontrivial :=
    RayClass.adicAbv_isNontrivial v
  let hvKna : IsNonarchimedean (vK : K → ℝ) :=
    HeightOneSpectrum.isNonarchimedean_adicAbv K v
  let w := _root_.chosenFinitePlaceExtension (L := L) v
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
  let : Valued vK.Completion ℝ≥0 :=
    _root_.finitePlaceCompletionValued vK hvKna
  let : ValuativeRel vK.Completion :=
    _root_.finitePlaceCompletionValuativeRel vK hvKna
  let e :
      vK.Completionˣ ≃ₜ* (v.adicCompletion K)ˣ :=
    _root_.finitePlaceCompletionUnitsContinuousMulEquiv v
  have hprincipal :
      (LocalFieldTheory.fieldPrincipalUnits vK.Completion n).map
          e.toMonoidHom =
        RayClass.localHigherUnitGroup v n := by
    simpa [vK, hvKna, e] using
      (finitePlaceFieldPrincipalUnits_map_eq_localHigherUnitGroup
        (K := K) v n)
  rw [← hprincipal]
  change
    (LocalFieldTheory.fieldPrincipalUnits vK.Completion n).map
          e.toMonoidHom ≤
        (LocalFieldTheory.localNormSubgroup
          vK.Completion E).map e.toMonoidHom ↔
      LocalFieldTheory.fieldPrincipalUnits vK.Completion n ≤
        LocalFieldTheory.localNormSubgroup vK.Completion E
  constructor
  · intro h x hx
    have hex :
        e x ∈
          (LocalFieldTheory.localNormSubgroup
            vK.Completion E).map e.toMonoidHom :=
      h ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hyx⟩ := hex
    exact (e.injective hyx) ▸ hy
  · rintro h _ ⟨x, hx, rfl⟩
    exact ⟨x, h hx, rfl⟩

end Galois

section Abelian

variable [IsAbelianGalois K L]

open scoped Classical in
/-- The conductor exponent of the chosen localized extension at `v`, with the
completion and valuation instance tower confined to this definition body. -/
noncomputable def ideleClassNormChosenFinitePlaceLocalConductorExponent
    (v : HeightOneSpectrum (𝓞 K)) : ℕ := by
  let vK := HeightOneSpectrum.adicAbv K v
  let hvK : vK.IsNontrivial :=
    RayClass.adicAbv_isNontrivial v
  let hvKna : IsNonarchimedean (vK : K → ℝ) :=
    HeightOneSpectrum.isNonarchimedean_adicAbv K v
  let w := _root_.chosenFinitePlaceExtension (L := L) v
  letI hK :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K) w.1
  letI : SMul K w.1.Completion := hK.toSMul
  letI : Algebra vK.Completion w.1.Completion :=
    AbsoluteValue.completionAlgebra vK w.1 w.2
  letI :=
    LocalClassFieldTheory.localizedCompletionGlobalAlgebra vK w
  letI :=
    LocalClassFieldTheory.localizedCompletionIsScalarTower vK w
  let E := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK w
  letI : FiniteDimensional vK.Completion E :=
    AlgebraicNumberTheory.Valuations.localizedCompletionModuleFinite vK hvK w
  letI : IsAbelianGalois vK.Completion E :=
    LocalClassFieldTheory.localizedCompletion_isAbelianGalois
      vK hvK w
  letI : NontriviallyNormedField vK.Completion :=
    _root_.AlgebraicNumberTheory.Valuations.absoluteValueExtensionCompletionNontriviallyNormedField
      vK hvK
  letI : LocallyCompactSpace vK.Completion :=
    AbsoluteValue.Completion.locallyCompactSpace
      (_root_.finitePlaceCompletionBaseMap_isometry v)
  letI : IsUltrametricDist vK.Completion :=
    completionIsUltrametricDist vK hvKna
  letI : Valued vK.Completion ℝ≥0 :=
    _root_.finitePlaceCompletionValued vK hvKna
  let vBase : Valuation vK.Completion ℝ≥0 := Valued.v
  letI : vBase.IsNontrivial :=
    (inferInstance :
      (NormedField.valuation
        (K := vK.Completion)).IsNontrivial)
  letI : ValuativeRel vK.Completion :=
    _root_.finitePlaceCompletionValuativeRel vK hvKna
  letI : vBase.Compatible :=
    Valuation.Compatible.ofValuation vBase
  letI : ValuativeRel.IsNontrivial vK.Completion :=
    (ValuativeRel.isNontrivial_iff_isNontrivial vBase).2
      inferInstance
  letI : IsValuativeTopology vK.Completion :=
    isValuativeTopology_of_valued_ofValuation
      vK.Completion ℝ≥0
  letI : IsNonarchimedeanLocalField vK.Completion :=
    { toIsValuativeTopology := inferInstance
      toLocallyCompactSpace := inferInstance
      toIsNontrivial := inferInstance }
  exact LocalClassFieldTheory.localConductorExponent
    vK.Completion E

open scoped Classical in
/-- For a finite abelian extension, the local exponent selected by the
idèle-class norm conductor equals the local conductor exponent of the chosen
localized extension. -/
theorem ideleClassNormLocalHigherUnitExponent_eq_localConductorExponent
    (v : HeightOneSpectrum (𝓞 K)) :
    ideleClassNormLocalHigherUnitExponent
        (K := K) (L := L) v =
      ideleClassNormChosenFinitePlaceLocalConductorExponent
        (K := K) (L := L) v := by
  let vK := HeightOneSpectrum.adicAbv K v
  let hvK : vK.IsNontrivial :=
    RayClass.adicAbv_isNontrivial v
  let hvKna : IsNonarchimedean (vK : K → ℝ) :=
    HeightOneSpectrum.isNonarchimedean_adicAbv K v
  let w := _root_.chosenFinitePlaceExtension (L := L) v
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
    _root_.AlgebraicNumberTheory.Valuations.absoluteValueExtensionCompletionNontriviallyNormedField
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
  change
    ideleClassNormLocalHigherUnitExponent (K := K) (L := L) v =
      LocalClassFieldTheory.localConductorExponent vK.Completion E
  have hbridge (n : ℕ) :
      RayClass.localHigherUnitGroup v n ≤
          _root_.chosenFinitePlaceLocalNormSubgroup
            (K := K) (L := L) v ↔
        LocalFieldTheory.fieldPrincipalUnits vK.Completion n ≤
          LocalFieldTheory.localNormSubgroup
            vK.Completion E := by
    simpa [vK, hvK, hvKna, w, E] using
      (localHigherUnitGroup_le_normSubgroup_iff_fieldPrincipalUnits_le_normSubgroup
        (K := K) (L := L) v n)
  apply le_antisymm
  · apply
      ideleClassNormLocalHigherUnitExponent_min
        (K := K) (L := L) v
    exact
      (hbridge
        (LocalClassFieldTheory.localConductorExponent
          vK.Completion E)).2
        (LocalClassFieldTheory.localConductorExponent_spec
          vK.Completion E)
  · apply
      LocalClassFieldTheory.localConductorExponent_min
        vK.Completion E
    exact
      (hbridge
        (ideleClassNormLocalHigherUnitExponent
          (K := K) (L := L) v)).1
        (ideleClassNormLocalHigherUnitExponent_spec
          (K := K) (L := L) v)

end Abelian

end GlobalClassFields
end GlobalClassFieldTheory
