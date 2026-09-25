/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.FinitePlaceArtin.CrossLocalRestriction
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.NormRestriction
/-!
# Norm--restriction for finite-place Artin homomorphisms

This module proves norm--restriction naturality for finite-place Artin maps in an actual square
of number fields and their chosen completed local extensions.
-/

@[expose] public section

open scoped IsMulCommutative NNReal NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open AlgebraicNumberTheory.Valuations
open HilbertRamification
open LocalClassFieldTheory
open LocalFieldTheory

variable {K L : Type}
    [Field K] [NumberField K]
    [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]

open scoped Classical in
private theorem finitePlaceArtinNormUnits_map_ringEquiv
    {F M F' M' : Type}
    [Field F] [Field M] [Field F'] [Field M']
    [Algebra F M] [Algebra F' M']
    (eF : F ≃+* F') (eM : M ≃+* M')
    (he :
      RingHom.comp (algebraMap F' M') eF =
        RingHom.comp eM (algebraMap F M))
    (x : Mˣ) :
    Units.mapEquiv eF.toMulEquiv
        (LocalFieldTheory.normUnits F M x) =
      LocalFieldTheory.normUnits F' M'
        (Units.mapEquiv eM.toMulEquiv x) := by
  apply Units.ext
  change
    eF (Algebra.norm F (x : M)) =
      Algebra.norm F' (eM (x : M))
  rw [Algebra.norm_eq_of_equiv_equiv eF eM he]
  exact eF.apply_symm_apply _

open scoped Classical in
private abbrev finitePlaceNormCompletion
    (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) :=
  (NumberField.HeightOneSpectrum.adicAbv F v).Completion

open scoped Classical in
private abbrev finitePlaceNormLocalizedCompletion
    (F M : Type) [Field F] [Field M] [Algebra F M]
    [NumberField F]
    (v : HeightOneSpectrum (𝓞 F))
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv F v) M) :=
  AlgebraicNumberTheory.Valuations.LocalizedCompletion
    (NumberField.HeightOneSpectrum.adicAbv F v) w

open scoped Classical in
private noncomputable def finitePlaceRelativeNormUnits
    {K' : Type}
    [Field K'] [NumberField K'] [Algebra K K']
    (v : HeightOneSpectrum (𝓞 K))
    (W : HeightOneSpectrum (𝓞 K'))
    (hW : finitePlaceBelow (K := K) W = v) :
    (finitePlaceNormCompletion K' W)ˣ →*
      (finitePlaceNormCompletion K v)ˣ := by
  letI : Algebra
      (finitePlaceNormCompletion K v)
      (finitePlaceNormCompletion K' W) :=
    (finitePlaceArtinRelativeCompletionRingHom
      (K := K) (K' := K') v W hW).toAlgebra
  exact LocalFieldTheory.normUnits
    (finitePlaceNormCompletion K v)
    (finitePlaceNormCompletion K' W)

open scoped Classical in
private noncomputable def finitePlaceConcreteNormUnits
    {K' : Type}
    [Field K'] [NumberField K'] [Algebra K K']
    (v : HeightOneSpectrum (𝓞 K))
    (W : HeightOneSpectrum (𝓞 K'))
    (hW : finitePlaceBelow (K := K) W = v) :
    (W.adicCompletion K')ˣ →* (v.adicCompletion K)ˣ := by
  letI : Algebra (v.adicCompletion K) (W.adicCompletion K') :=
    (finitePlaceAdicCompletionMap
      K K' v ⟨W, hW⟩).toAlgebra
  exact LocalFieldTheory.normUnits
    (v.adicCompletion K) (W.adicCompletion K')

open scoped Classical in
private theorem finitePlaceArtinConcreteNormUnits
    {K' : Type}
    [Field K'] [NumberField K'] [Algebra K K']
    (v : HeightOneSpectrum (𝓞 K))
    (W : HeightOneSpectrum (𝓞 K'))
    (hW : finitePlaceBelow (K := K) W = v)
    (x : (W.adicCompletion K')ˣ) :
      finitePlaceCompletionUnitsContinuousMulEquiv v
        (finitePlaceRelativeNormUnits
          (K := K) (K' := K') v W hW
          ((finitePlaceCompletionUnitsContinuousMulEquiv W).symm x)) =
      finitePlaceConcreteNormUnits
        (K := K) (K' := K') v W hW x := by
  let vK := NumberField.HeightOneSpectrum.adicAbv K v
  let vK' := NumberField.HeightOneSpectrum.adicAbv K' W
  let C := vK.Completion
  let D := vK'.Completion
  let eC :
      C ≃+* v.adicCompletion K :=
    (relativeFinitePlaceCompletionAlgEquiv v).toRingEquiv
  let eD :
      D ≃+* W.adicCompletion K' :=
    (relativeFinitePlaceCompletionAlgEquiv W).toRingEquiv
  let eCUnits :
      Cˣ ≃* (v.adicCompletion K)ˣ :=
    finitePlaceCompletionUnitsContinuousMulEquiv v
  let eDUnits :
      Dˣ ≃* (W.adicCompletion K')ˣ :=
    finitePlaceCompletionUnitsContinuousMulEquiv W
  have hCUnits :
      eCUnits = Units.mapEquiv eC.toMulEquiv := by
    change
      Units.mapEquiv
          (finitePlaceCompletionRingEquiv v).toMulEquiv =
        Units.mapEquiv eC.toMulEquiv
    rw [finitePlaceCompletionRingEquiv_eq_relative]
  have hDUnits :
      eDUnits = Units.mapEquiv eD.toMulEquiv := by
    change
      Units.mapEquiv
          (finitePlaceCompletionRingEquiv W).toMulEquiv =
        Units.mapEquiv eD.toMulEquiv
    rw [finitePlaceCompletionRingEquiv_eq_relative]
  let concreteBaseMap :
      v.adicCompletion K →+* W.adicCompletion K' :=
    finitePlaceAdicCompletionMap K K' v ⟨W, hW⟩
  let : Algebra (v.adicCompletion K) (W.adicCompletion K') :=
    concreteBaseMap.toAlgebra
  let : Algebra C D :=
    (finitePlaceArtinRelativeCompletionRingHom
      (K := K) (K' := K') v W hW).toAlgebra
  have hBaseMap (y : C) :
      eD (algebraMap C D y) =
        concreteBaseMap (eC y) := by
    change
      eD (eD.symm (concreteBaseMap (eC y))) =
        concreteBaseMap (eC y)
    rw [eD.apply_symm_apply]
  have hBaseCompatible :
      RingHom.comp
          (algebraMap
            (v.adicCompletion K) (W.adicCompletion K'))
          eC =
        RingHom.comp eD (algebraMap C D) := by
    apply RingHom.ext
    intro y
    exact (hBaseMap y).symm
  change
    eCUnits
        (LocalFieldTheory.normUnits C D
          (eDUnits.symm x)) =
      LocalFieldTheory.normUnits
        (v.adicCompletion K) (W.adicCompletion K') x
  rw [hCUnits, hDUnits]
  calc
    Units.mapEquiv eC.toMulEquiv
        (LocalFieldTheory.normUnits C D
          (Units.mapEquiv eD.symm.toMulEquiv x)) =
      LocalFieldTheory.normUnits
        (v.adicCompletion K) (W.adicCompletion K')
        (Units.mapEquiv eD.toMulEquiv
          (Units.mapEquiv eD.symm.toMulEquiv x)) :=
      finitePlaceArtinNormUnits_map_ringEquiv
        eC eD hBaseCompatible
        (Units.mapEquiv eD.symm.toMulEquiv x)
    _ =
      LocalFieldTheory.normUnits
        (v.adicCompletion K) (W.adicCompletion K') x := by
      congr 1
      change
        (Units.mapEquiv eD.toMulEquiv)
            ((Units.mapEquiv eD.toMulEquiv).symm x) = x
      exact (Units.mapEquiv eD.toMulEquiv).apply_symm_apply x

open scoped Classical in
private theorem finitePlaceArtinHasExtension_of_norm
    {A B C D : Type}
    [NormedField A] [NormedField B]
    [NormedField C] [NormedField D]
    [Algebra C D]
    [Valued C ℝ≥0] [Valued D ℝ≥0]
    [ValuativeRel C] [ValuativeRel D]
    [(Valued.v : Valuation C ℝ≥0).Compatible]
    [(Valued.v : Valuation D ℝ≥0).Compatible]
    (eC : C ≃+* A) (eD : D ≃+* B)
    (baseMap : A →+* B)
    (hAlgebraMap : ∀ x : C,
      algebraMap C D x =
        eD.symm (baseMap (eC x)))
    (hDNorm : ∀ y : B, ‖eD.symm y‖ = ‖y‖)
    (hCNorm : ∀ x : C, ‖eC x‖ = ‖x‖)
    (hBaseNorm : ∀ x : A,
      ‖baseMap x‖ ≤ 1 ↔ ‖x‖ ≤ 1)
    (hDValuation : ∀ x : D,
      (Valued.v : Valuation D ℝ≥0) x = ‖x‖₊)
    (hCValuation : ∀ x : C,
      (Valued.v : Valuation C ℝ≥0) x = ‖x‖₊) :
    (ValuativeRel.valuation C).HasExtension
      (ValuativeRel.valuation D) := by
  let vC : Valuation C ℝ≥0 := Valued.v
  let vD : Valuation D ℝ≥0 := Valued.v
  apply Valuation.HasExtension.ofComapInteger
  ext x
  simp only [Subring.mem_comap, Valuation.mem_integer_iff]
  rw [
    ← (ValuativeRel.valuation D).vle_one_iff,
    vD.vle_one_iff,
    ← (ValuativeRel.valuation C).vle_one_iff,
    vC.vle_one_iff]
  rw [hDValuation, hCValuation]
  have hTargetNorm :
      ‖algebraMap C D x‖ =
        ‖baseMap (eC x)‖ := by
    rw [hAlgebraMap]
    exact hDNorm (baseMap (eC x))
  have hTargetNormNN :
      ‖algebraMap C D x‖₊ =
        ‖baseMap (eC x)‖₊ := by
    apply NNReal.eq
    exact hTargetNorm
  have hSourceNormNN :
      ‖eC x‖₊ = ‖x‖₊ := by
    apply NNReal.eq
    exact hCNorm x
  rw [hTargetNormNN, ← hSourceNormNN]
  exact_mod_cast hBaseNorm (eC x)

open scoped Classical in
private theorem finitePlaceArtinCompletionHasExtension
    {K' : Type}
    [Field K'] [NumberField K'] [Algebra K K']
    (v : HeightOneSpectrum (𝓞 K))
    (W : HeightOneSpectrum (𝓞 K'))
    (hW : finitePlaceBelow (K := K) W = v) :
    let vK := NumberField.HeightOneSpectrum.adicAbv K v
    let vK' := NumberField.HeightOneSpectrum.adicAbv K' W
    let C := vK.Completion
    let D := vK'.Completion
    let hvKna : IsNonarchimedean (vK : K → ℝ) :=
      NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv K v
    let hvK'na : IsNonarchimedean (vK' : K' → ℝ) :=
      NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv K' W
    letI : IsUltrametricDist C :=
      finitePlaceArtinCompletionIsUltrametricDist vK hvKna
    letI : Valued C ℝ≥0 :=
      finitePlaceArtinCompletionValued vK hvKna
    letI : ValuativeRel C :=
      finitePlaceArtinCompletionValuativeRel vK hvKna
    let vC : Valuation C ℝ≥0 := Valued.v
    letI : vC.Compatible :=
      Valuation.Compatible.ofValuation vC
    letI : IsUltrametricDist D :=
      finitePlaceArtinCompletionIsUltrametricDist vK' hvK'na
    letI : Valued D ℝ≥0 :=
      finitePlaceArtinCompletionValued vK' hvK'na
    letI : ValuativeRel D :=
      finitePlaceArtinCompletionValuativeRel vK' hvK'na
    let vD : Valuation D ℝ≥0 := Valued.v
    letI : vD.Compatible :=
      Valuation.Compatible.ofValuation vD
    letI : Algebra C D :=
      (finitePlaceArtinRelativeCompletionRingHom
        (K := K) (K' := K') v W hW).toAlgebra
    (ValuativeRel.valuation C).HasExtension
      (ValuativeRel.valuation D) := by
  let vK := NumberField.HeightOneSpectrum.adicAbv K v
  let vK' := NumberField.HeightOneSpectrum.adicAbv K' W
  let C := vK.Completion
  let D := vK'.Completion
  let eC :
      C ≃+* v.adicCompletion K :=
    (relativeFinitePlaceCompletionAlgEquiv v).toRingEquiv
  let eD :
      D ≃+* W.adicCompletion K' :=
    (relativeFinitePlaceCompletionAlgEquiv W).toRingEquiv
  let concreteBaseMap :
      v.adicCompletion K →+* W.adicCompletion K' :=
    finitePlaceAdicCompletionMap K K' v ⟨W, hW⟩
  let : Algebra (v.adicCompletion K) (W.adicCompletion K') :=
    concreteBaseMap.toAlgebra
  let : Algebra C D :=
    (finitePlaceArtinRelativeCompletionRingHom
      (K := K) (K' := K') v W hW).toAlgebra
  let hvKna : IsNonarchimedean (vK : K → ℝ) :=
    NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv K v
  let : IsUltrametricDist C :=
    finitePlaceArtinCompletionIsUltrametricDist vK hvKna
  let : Valued C ℝ≥0 :=
    finitePlaceArtinCompletionValued vK hvKna
  let vC : Valuation C ℝ≥0 := Valued.v
  let : ValuativeRel C :=
    finitePlaceArtinCompletionValuativeRel vK hvKna
  let : vC.Compatible :=
    Valuation.Compatible.ofValuation vC
  let hvK'na : IsNonarchimedean (vK' : K' → ℝ) :=
    NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv K' W
  let : IsUltrametricDist D :=
    finitePlaceArtinCompletionIsUltrametricDist vK' hvK'na
  let : Valued D ℝ≥0 :=
    finitePlaceArtinCompletionValued vK' hvK'na
  let vD : Valuation D ℝ≥0 := Valued.v
  let : ValuativeRel D :=
    finitePlaceArtinCompletionValuativeRel vK' hvK'na
  let : vD.Compatible :=
    Valuation.Compatible.ofValuation vD
  exact
    finitePlaceArtinHasExtension_of_norm
      eC eD concreteBaseMap
      (by intro x; rfl)
      (relativeFinitePlaceCompletionAlgEquiv_symm_norm W)
      (fun x =>
        (relativeFinitePlaceCompletionRingHom_isometry
          v).norm_map_of_map_zero
            (map_zero
              (relativeFinitePlaceCompletionRingHom v)) x)
      (finitePlaceAdicCompletionMap_norm_le_one_iff
        K K' v ⟨W, hW⟩)
      (fun _ => rfl)
      (fun _ => rfl)

open scoped Classical in
private theorem finitePlaceLocalArtin_norm_restriction_apply
    {C D E E' : Type}
    [Field C] [ValuativeRel C] [TopologicalSpace C]
    [IsNonarchimedeanLocalField C]
    [Field D] [ValuativeRel D] [TopologicalSpace D]
    [IsNonarchimedeanLocalField D]
    [Field E] [Field E']
    [Algebra C D] [Algebra C E] [Algebra C E']
    [Algebra D E'] [Algebra E E']
    [IsScalarTower C D E'] [IsScalarTower C E E']
    [FiniteDimensional C D] [Algebra.IsSeparable C D]
    [Valuation.HasExtension
      (ValuativeRel.valuation C) (ValuativeRel.valuation D)]
    [FiniteDimensional C E] [IsAbelianGalois C E]
    [FiniteDimensional D E'] [IsAbelianGalois D E']
    (y : Dˣ) :
    AlgEquiv.restrictNormalHom E
        ((AlgEquiv.restrictScalarsHom C)
          (LocalClassFieldTheory.abelianLocalArtinMonoidHom
            D E' y)) =
      LocalClassFieldTheory.abelianLocalArtinMonoidHom C E
        (LocalFieldTheory.normUnits C D y) :=
  DFunLike.congr_fun
    (LocalClassFieldTheory.abelianLocalArtinMonoidHom_norm_restriction
      C D E E') y

open scoped Classical in
private abbrev finitePlaceNormLocalizedAut
    (F M : Type) [Field F] [Field M] [Algebra F M]
    [NumberField F]
    (v : HeightOneSpectrum (𝓞 F))
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv F v) M) :=
  let vF := NumberField.HeightOneSpectrum.adicAbv F v
  letI hwF :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := F) w.1
  letI : SMul F w.1.Completion := hwF.toSMul
  letI : Algebra vF.Completion w.1.Completion :=
    AbsoluteValue.completionAlgebra vF w.1 w.2
  let E :=
    AlgebraicNumberTheory.Valuations.LocalizedCompletion vF w
  E ≃ₐ[vF.Completion] E

section FinitePlaceNormRestrictionInstances

variable {K' L' : Type}
    [Field K'] [NumberField K']
    [Field L'] [NumberField L']
    [Algebra K K'] [Algebra K' L'] [Algebra K L']
    [IsScalarTower K K' L']
    [Algebra L L'] [IsScalarTower K L L']
    [IsAbelianGalois K' L']
    (v : HeightOneSpectrum (𝓞 K))
    (W : HeightOneSpectrum (𝓞 K'))
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L)
    (w' : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K' W) L')

local notation "vKₙ" =>
  NumberField.HeightOneSpectrum.adicAbv K v
local notation "vKₙ'" =>
  NumberField.HeightOneSpectrum.adicAbv K' W
local notation "Cₙ" =>
  finitePlaceNormCompletion K v
local notation "Dₙ" =>
  finitePlaceNormCompletion K' W
local notation "Eₙ" =>
  finitePlaceNormLocalizedCompletion K L v w
local notation "Eₙ'" =>
  finitePlaceNormLocalizedCompletion K' L' W w'

open scoped Classical in
/-- The lower extended completion is an algebra over the lower global base field. -/
local instance finitePlaceNormLowerExtensionAlgebra :
    Algebra K w.1.Completion :=
  AbsoluteValue.extensionCompletionAlgebra
    (K := K) w.1

attribute [local instance] finitePlaceNormLowerExtensionAlgebra

open scoped Classical in
/-- The lower global base field acts on the lower extended completion. -/
local instance finitePlaceNormLowerExtensionSMul :
    SMul K w.1.Completion :=
  (finitePlaceNormLowerExtensionAlgebra v w).toSMul

attribute [local instance] finitePlaceNormLowerExtensionSMul

open scoped Classical in
/-- The lower extended completion is an algebra over the lower base-place completion. -/
local instance finitePlaceNormLowerCompletionAlgebra :
    Algebra Cₙ w.1.Completion :=
  AbsoluteValue.completionAlgebra vKₙ w.1 w.2

attribute [local instance] finitePlaceNormLowerCompletionAlgebra

open scoped Classical in
/-- The lower localized completion is an algebra over the lower global base field. -/
local instance finitePlaceNormLowerGlobalAlgebra :
    Algebra K Eₙ :=
  LocalClassFieldTheory.localizedCompletionGlobalAlgebra vKₙ w

attribute [local instance] finitePlaceNormLowerGlobalAlgebra

open scoped Classical in
/-- The upper extended completion is an algebra over the upper global base field. -/
local instance finitePlaceNormUpperExtensionAlgebra :
    Algebra K' w'.1.Completion :=
  AbsoluteValue.extensionCompletionAlgebra
    (K := K') w'.1

attribute [local instance] finitePlaceNormUpperExtensionAlgebra

open scoped Classical in
/-- The upper global base field acts on the upper extended completion. -/
local instance finitePlaceNormUpperExtensionSMul :
    SMul K' w'.1.Completion :=
  (finitePlaceNormUpperExtensionAlgebra W w').toSMul

attribute [local instance] finitePlaceNormUpperExtensionSMul

open scoped Classical in
/-- The upper extended completion is an algebra over the upper base-place completion. -/
local instance finitePlaceNormUpperCompletionAlgebra :
    Algebra Dₙ w'.1.Completion :=
  AbsoluteValue.completionAlgebra vKₙ' w'.1 w'.2

attribute [local instance] finitePlaceNormUpperCompletionAlgebra

open scoped Classical in
/-- The upper localized completion is an algebra over the upper global base field. -/
local instance finitePlaceNormUpperGlobalAlgebra :
    Algebra K' Eₙ' :=
  LocalClassFieldTheory.localizedCompletionGlobalAlgebra vKₙ' w'

attribute [local instance] finitePlaceNormUpperGlobalAlgebra

open scoped Classical in
/-- The lower base-place completion carries a nontrivial normed field structure. -/
local instance finitePlaceNormLowerNontriviallyNormedField :
    NontriviallyNormedField Cₙ :=
  absoluteValueExtensionCompletionNontriviallyNormedField
    vKₙ (RayClass.adicAbv_isNontrivial v)

attribute [local instance] finitePlaceNormLowerNontriviallyNormedField

open scoped Classical in
local instance finitePlaceNormLowerLocallyCompactSpace :
    LocallyCompactSpace Cₙ :=
  AbsoluteValue.Completion.locallyCompactSpace
    (finitePlaceCompletionBaseMap_isometry v)

attribute [local instance] finitePlaceNormLowerLocallyCompactSpace

open scoped Classical in
/-- The upper base-place completion carries a nontrivial normed field structure. -/
local instance finitePlaceNormUpperNontriviallyNormedField :
    NontriviallyNormedField Dₙ :=
  absoluteValueExtensionCompletionNontriviallyNormedField
    vKₙ' (RayClass.adicAbv_isNontrivial W)

attribute [local instance] finitePlaceNormUpperNontriviallyNormedField

open scoped Classical in
local instance finitePlaceNormUpperLocallyCompactSpace :
    LocallyCompactSpace Dₙ :=
  AbsoluteValue.Completion.locallyCompactSpace
    (finitePlaceCompletionBaseMap_isometry W)

attribute [local instance] finitePlaceNormUpperLocallyCompactSpace

open scoped Classical in
local instance finitePlaceNormLowerLocalizedFiniteDimensional :
    FiniteDimensional Cₙ Eₙ :=
  AlgebraicNumberTheory.Valuations.localizedCompletionModuleFinite
    vKₙ (RayClass.adicAbv_isNontrivial v) w

attribute [local instance] finitePlaceNormLowerLocalizedFiniteDimensional

open scoped Classical in
local instance finitePlaceNormLowerLocalizedAbelianGalois :
    IsAbelianGalois Cₙ Eₙ :=
  LocalClassFieldTheory.localizedCompletion_isAbelianGalois
    vKₙ (RayClass.adicAbv_isNontrivial v) w

attribute [local instance] finitePlaceNormLowerLocalizedAbelianGalois

open scoped Classical in
local instance finitePlaceNormUpperLocalizedFiniteDimensional :
    FiniteDimensional Dₙ Eₙ' :=
  AlgebraicNumberTheory.Valuations.localizedCompletionModuleFinite
    vKₙ' (RayClass.adicAbv_isNontrivial W) w'

attribute [local instance] finitePlaceNormUpperLocalizedFiniteDimensional

open scoped Classical in
local instance finitePlaceNormUpperLocalizedAbelianGalois :
    IsAbelianGalois Dₙ Eₙ' :=
  LocalClassFieldTheory.localizedCompletion_isAbelianGalois
    vKₙ' (RayClass.adicAbv_isNontrivial W) w'

attribute [local instance] finitePlaceNormUpperLocalizedAbelianGalois

open scoped Classical in
local instance finitePlaceNormLowerUltrametric :
    IsUltrametricDist Cₙ :=
  finitePlaceArtinCompletionIsUltrametricDist vKₙ
    (NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv K v)

attribute [local instance] finitePlaceNormLowerUltrametric

open scoped Classical in
/-- The lower base-place completion carries the nonnegative-real valuation used in local
reciprocity. -/
local instance finitePlaceNormLowerValued :
    Valued Cₙ ℝ≥0 :=
  finitePlaceArtinCompletionValued vKₙ
    (NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv K v)

attribute [local instance] finitePlaceNormLowerValued

open scoped Classical in
private theorem finitePlaceNormLowerValued_apply (x : Cₙ) :
    (Valued.v : Valuation Cₙ ℝ≥0) x = ‖x‖₊ := rfl

open scoped Classical in
local instance finitePlaceNormLowerValuationNontrivial :
    (Valued.v : Valuation Cₙ ℝ≥0).IsNontrivial :=
  (inferInstance :
    (NormedField.valuation (K := Cₙ)).IsNontrivial)

attribute [local instance] finitePlaceNormLowerValuationNontrivial

open scoped Classical in
/-- The lower base-place completion carries the valuative relation used in local reciprocity. -/
local instance finitePlaceNormLowerValuativeRel :
    ValuativeRel Cₙ :=
  finitePlaceArtinCompletionValuativeRel vKₙ
    (NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv K v)

attribute [local instance] finitePlaceNormLowerValuativeRel

open scoped Classical in
local instance finitePlaceNormLowerValuationCompatible :
    (Valued.v : Valuation Cₙ ℝ≥0).Compatible :=
  Valuation.Compatible.ofValuation
    (Valued.v : Valuation Cₙ ℝ≥0)

attribute [local instance] finitePlaceNormLowerValuationCompatible

open scoped Classical in
local instance finitePlaceNormLowerValuativeRelNontrivial :
    ValuativeRel.IsNontrivial Cₙ :=
  (ValuativeRel.isNontrivial_iff_isNontrivial
    (Valued.v : Valuation Cₙ ℝ≥0)).2 inferInstance

attribute [local instance] finitePlaceNormLowerValuativeRelNontrivial

open scoped Classical in
local instance finitePlaceNormLowerLocalField :
    IsNonarchimedeanLocalField Cₙ :=
  finitePlaceArtinCompletionIsNonarchimedeanLocalField vKₙ
    (NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv K v)

attribute [local instance] finitePlaceNormLowerLocalField

open scoped Classical in
local instance finitePlaceNormUpperUltrametric :
    IsUltrametricDist Dₙ :=
  finitePlaceArtinCompletionIsUltrametricDist vKₙ'
    (NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv K' W)

attribute [local instance] finitePlaceNormUpperUltrametric

open scoped Classical in
/-- The upper base-place completion carries the nonnegative-real valuation used in local
reciprocity. -/
local instance finitePlaceNormUpperValued :
    Valued Dₙ ℝ≥0 :=
  finitePlaceArtinCompletionValued vKₙ'
    (NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv K' W)

attribute [local instance] finitePlaceNormUpperValued

open scoped Classical in
local instance finitePlaceNormUpperValuationNontrivial :
    (Valued.v : Valuation Dₙ ℝ≥0).IsNontrivial :=
  (inferInstance :
    (NormedField.valuation (K := Dₙ)).IsNontrivial)

attribute [local instance] finitePlaceNormUpperValuationNontrivial

open scoped Classical in
/-- The upper base-place completion carries the valuative relation used in local reciprocity. -/
local instance finitePlaceNormUpperValuativeRel :
    ValuativeRel Dₙ :=
  finitePlaceArtinCompletionValuativeRel vKₙ'
    (NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv K' W)

attribute [local instance] finitePlaceNormUpperValuativeRel

open scoped Classical in
local instance finitePlaceNormUpperValuationCompatible :
    (Valued.v : Valuation Dₙ ℝ≥0).Compatible :=
  Valuation.Compatible.ofValuation
    (Valued.v : Valuation Dₙ ℝ≥0)

attribute [local instance] finitePlaceNormUpperValuationCompatible

open scoped Classical in
local instance finitePlaceNormUpperValuativeRelNontrivial :
    ValuativeRel.IsNontrivial Dₙ :=
  (ValuativeRel.isNontrivial_iff_isNontrivial
    (Valued.v : Valuation Dₙ ℝ≥0)).2 inferInstance

attribute [local instance] finitePlaceNormUpperValuativeRelNontrivial

open scoped Classical in
local instance finitePlaceNormUpperLocalField :
    IsNonarchimedeanLocalField Dₙ :=
  finitePlaceArtinCompletionIsNonarchimedeanLocalField vKₙ'
    (NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv K' W)

attribute [local instance] finitePlaceNormUpperLocalField

open scoped Classical in
private noncomputable def finitePlaceNormRestrictedArtin
    [NumberField L]
    (hW : finitePlaceBelow (K := K) W = v)
    (hcentres :
      finitePlaceBelow (K := L)
          (finitePlaceExtensionCentre
            (K := K') (L := L') W w') =
        finitePlaceExtensionCentre
          (K := K) (L := L) v w)
    (y : Dₙˣ) :
    finitePlaceNormLocalizedAut K L v w := by
  exact
    finitePlaceCrossLocalRestrictionMonoidHom
      (K := K) (L := L) (K' := K') (L' := L')
      v W hW w w' hcentres
      (finitePlaceLocalArtinMonoidHom
        (K := K') (L := L') W w'
        (finitePlaceCompletionUnitsContinuousMulEquiv W y))

open scoped Classical in
private noncomputable def finitePlaceNormLowerArtin
    (hW : finitePlaceBelow (K := K) W = v)
    (y : Dₙˣ) :
    finitePlaceNormLocalizedAut K L v w := by
  exact
    finitePlaceLocalArtinMonoidHom
      (K := K) (L := L) v w
      (finitePlaceCompletionUnitsContinuousMulEquiv v
      (finitePlaceRelativeNormUnits
          (K := K) (K' := K') v W hW y))

open scoped Classical in
private noncomputable def finitePlaceNormUpperRawArtin
    (y : Dₙˣ) :
    finitePlaceNormLocalizedAut K' L' W w' :=
  LocalClassFieldTheory.abelianLocalArtinMonoidHom
    Dₙ Eₙ' y

open scoped Classical in
private noncomputable def finitePlaceNormLowerRawArtin
    (hW : finitePlaceBelow (K := K) W = v)
    (y : Dₙˣ) :
    finitePlaceNormLocalizedAut K L v w :=
  LocalClassFieldTheory.abelianLocalArtinMonoidHom
    Cₙ Eₙ
    (finitePlaceRelativeNormUnits
      (K := K) (K' := K') v W hW y)

open scoped Classical in
private theorem finitePlaceNormUpperArtin_eq_raw
    (y : Dₙˣ) :
    finitePlaceLocalArtinMonoidHom
        (K := K') (L := L') W w'
        (finitePlaceCompletionUnitsContinuousMulEquiv W y) =
      finitePlaceNormUpperRawArtin
        (K' := K') (L' := L') W w' y := by
  rw [
    finitePlaceLocalArtinMonoidHom_apply
      (K := K') (L := L') W w'
        (finitePlaceCompletionUnitsContinuousMulEquiv W y)]
  have hy :
      (↑(finitePlaceCompletionUnitsContinuousMulEquiv W) :
          Dₙˣ ≃* (W.adicCompletion K')ˣ).symm
          (finitePlaceCompletionUnitsContinuousMulEquiv W y) =
        y :=
    (finitePlaceCompletionUnitsContinuousMulEquiv W).symm_apply_apply y
  rw [hy]
  rfl

open scoped Classical in
private theorem finitePlaceNormLowerArtin_eq_raw
    (hW : finitePlaceBelow (K := K) W = v)
    (y : Dₙˣ) :
    finitePlaceNormLowerArtin
        (K := K) (L := L) (K' := K')
        v W w hW y =
      finitePlaceNormLowerRawArtin
        (K := K) (L := L) (K' := K')
        v W w hW y := by
  unfold finitePlaceNormLowerArtin
  rw [
    finitePlaceLocalArtinMonoidHom_apply
      (K := K) (L := L) v w
        (finitePlaceCompletionUnitsContinuousMulEquiv v
          (finitePlaceRelativeNormUnits
            (K := K) (K' := K') v W hW y))]
  have hy :
      (↑(finitePlaceCompletionUnitsContinuousMulEquiv v) :
          Cₙˣ ≃* (v.adicCompletion K)ˣ).symm
          (finitePlaceCompletionUnitsContinuousMulEquiv v
            (finitePlaceRelativeNormUnits
              (K := K) (K' := K') v W hW y)) =
        finitePlaceRelativeNormUnits
          (K := K) (K' := K') v W hW y :=
    (finitePlaceCompletionUnitsContinuousMulEquiv v).symm_apply_apply _
  rw [hy]
  rfl

open scoped Classical in
private theorem finitePlaceNormRawArtin_naturality
    [NumberField L]
    (hW : finitePlaceBelow (K := K) W = v)
    (hcentres :
      finitePlaceBelow (K := L)
          (finitePlaceExtensionCentre
            (K := K') (L := L') W w') =
        finitePlaceExtensionCentre
          (K := K) (L := L) v w)
    (y : Dₙˣ) :
    finitePlaceCrossLocalRestrictionMonoidHom
        (K := K) (L := L) (K' := K') (L' := L')
        v W hW w w' hcentres
        (finitePlaceNormUpperRawArtin
          (K' := K') (L' := L') W w' y) =
      finitePlaceNormLowerRawArtin
        (K := K) (L := L) (K' := K')
        v W w hW y := by
  let C := finitePlaceNormCompletion K v
  let D := finitePlaceNormCompletion K' W
  let E := finitePlaceNormLocalizedCompletion K L v w
  let E' := finitePlaceNormLocalizedCompletion K' L' W w'
  let : Algebra C D :=
    (finitePlaceArtinRelativeCompletionRingHom
      (K := K) (K' := K') v W hW).toAlgebra
  let : ContinuousSMul C D :=
    continuousSMul_of_algebraMap C D <|
      finitePlaceArtinRelativeCompletionRingHom_continuous
        (K := K) (K' := K') v W hW
  let : FiniteDimensional C D :=
    FiniteDimensional.of_locallyCompactSpace C
  let : CharZero C :=
    charZero_of_injective_algebraMap
      (algebraMap K C).injective
  let : Algebra.IsIntegral C D :=
    Algebra.IsIntegral.of_finite C D
  let : Algebra.IsSeparable C D :=
    Algebra.IsSeparable.of_integral C D
  let : Algebra E E' :=
    (finitePlaceArtinLocalizedCompletionRingHom
      (K := K) (L := L) (K' := K') (L' := L')
      v W w w' hcentres).toAlgebra
  let : Algebra C E' :=
    ((algebraMap D E').comp (algebraMap C D)).toAlgebra
  let : IsScalarTower C D E' :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower C E E' :=
    IsScalarTower.of_algebraMap_eq' <| by
      apply RingHom.ext
      intro x
      exact
        finitePlaceArtinLocalizedCompletion_towerPoint
          (K := K) (L := L) (K' := K') (L' := L')
          v W hW w w' hcentres x
  let :
      (ValuativeRel.valuation C).HasExtension
        (ValuativeRel.valuation D) :=
    finitePlaceArtinCompletionHasExtension
      (K := K) (K' := K') v W hW
  let hGaloisE : IsGalois C E :=
    (inferInstance : IsAbelianGalois C E).toIsGalois
  let : Normal C E := hGaloisE.to_normal
  unfold finitePlaceNormUpperRawArtin
  unfold finitePlaceNormLowerRawArtin
  change
    AlgEquiv.restrictNormalHom E
        ((AlgEquiv.restrictScalarsHom C)
          (LocalClassFieldTheory.abelianLocalArtinMonoidHom
            D E' y)) =
      LocalClassFieldTheory.abelianLocalArtinMonoidHom C E
        (LocalFieldTheory.normUnits C D y)
  exact finitePlaceLocalArtin_norm_restriction_apply y

open scoped Classical in
private theorem finitePlaceNormLocalizedArtin_naturality
    [NumberField L]
    (hW : finitePlaceBelow (K := K) W = v)
    (hcentres :
      finitePlaceBelow (K := L)
          (finitePlaceExtensionCentre
            (K := K') (L := L') W w') =
        finitePlaceExtensionCentre
          (K := K) (L := L) v w)
    (y : Dₙˣ) :
    finitePlaceNormRestrictedArtin
        (K := K) (L := L) (K' := K') (L' := L')
        v W w w' hW hcentres y =
      finitePlaceNormLowerArtin
        (K := K) (L := L) (K' := K')
        v W w hW y := by
  calc
    _ =
        finitePlaceCrossLocalRestrictionMonoidHom
          (K := K) (L := L) (K' := K') (L' := L')
          v W hW w w' hcentres
          (finitePlaceNormUpperRawArtin
            (K' := K') (L' := L') W w' y) := by
      unfold finitePlaceNormRestrictedArtin
      exact congrArg
        (finitePlaceCrossLocalRestrictionMonoidHom
          (K := K) (L := L) (K' := K') (L' := L')
          v W hW w w' hcentres)
        (finitePlaceNormUpperArtin_eq_raw
          (K' := K') (L' := L') W w' y)
    _ =
        finitePlaceNormLowerRawArtin
          (K := K) (L := L) (K' := K')
          v W w hW y :=
      finitePlaceNormRawArtin_naturality
        (K := K) (L := L) (K' := K') (L' := L')
        v W w w' hW hcentres y
    _ =
        finitePlaceNormLowerArtin
          (K := K) (L := L) (K' := K')
          v W w hW y :=
      (finitePlaceNormLowerArtin_eq_raw
        (K := K) (L := L) (K' := K')
        v W w hW y).symm

open scoped Classical in
private theorem
    finitePlaceLocalArtinMonoidHom_norm_restriction_localized
    {K' L' : Type}
    [Field K'] [NumberField K']
    [Field L'] [NumberField L']
    [NumberField L]
    [Algebra K K'] [Algebra K' L'] [Algebra K L']
    [IsScalarTower K K' L']
    [Algebra L L'] [IsScalarTower K L L']
    [IsAbelianGalois K' L']
    (v : HeightOneSpectrum (𝓞 K))
    (W : HeightOneSpectrum (𝓞 K'))
    (hW : finitePlaceBelow (K := K) W = v)
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L)
    (w' : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K' W) L')
    (hcentres :
      finitePlaceBelow (K := L)
          (finitePlaceExtensionCentre
            (K := K') (L := L') W w') =
        finitePlaceExtensionCentre
          (K := K) (L := L) v w)
    (y : (finitePlaceNormCompletion K' W)ˣ) :
    finitePlaceCrossLocalRestrictionMonoidHom
        (K := K) (L := L) (K' := K') (L' := L')
        v W hW w w' hcentres
        (finitePlaceLocalArtinMonoidHom
          (K := K') (L := L') W w'
          (finitePlaceCompletionUnitsContinuousMulEquiv W y)) =
      finitePlaceLocalArtinMonoidHom
        (K := K) (L := L) v w
        (finitePlaceCompletionUnitsContinuousMulEquiv v
          (finitePlaceRelativeNormUnits
            (K := K) (K' := K') v W hW y)) := by
  calc
    _ =
        finitePlaceNormRestrictedArtin
          (K := K) (L := L) (K' := K') (L' := L')
          v W w w' hW hcentres y :=
      rfl
    _ =
        finitePlaceNormLowerArtin
          (K := K) (L := L) (K' := K')
          v W w hW y :=
      finitePlaceNormLocalizedArtin_naturality
        (K := K) (L := L) (K' := K') (L' := L')
        v W w w' hW hcentres y
    _ = _ :=
      rfl

open scoped Classical in
/-- The local Artin maps attached to specified finite places commute
with the norm between their concrete adic completions. -/
theorem finitePlaceLocalArtinMonoidHom_norm_restriction
    {K' L' : Type}
    [Field K'] [NumberField K']
    [Field L'] [NumberField L']
    [NumberField L]
    [Algebra K K'] [Algebra K' L'] [Algebra K L']
    [IsScalarTower K K' L']
    [Algebra L L'] [IsScalarTower K L L']
    [IsAbelianGalois K' L']
    (v : HeightOneSpectrum (𝓞 K))
    (W : HeightOneSpectrum (𝓞 K'))
    (hW : finitePlaceBelow (K := K) W = v)
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L)
    (w' : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K' W) L')
    (hcentres :
      finitePlaceBelow (K := L)
          (finitePlaceExtensionCentre
            (K := K') (L := L') W w') =
        finitePlaceExtensionCentre
          (K := K) (L := L) v w)
    (x : (W.adicCompletion K')ˣ) :
    letI : Algebra (v.adicCompletion K) (W.adicCompletion K') :=
      (finitePlaceAdicCompletionMap
        K K' v ⟨W, hW⟩).toAlgebra
    finitePlaceCrossLocalRestrictionMonoidHom
        (K := K) (L := L) (K' := K') (L' := L')
        v W hW w w' hcentres
        (finitePlaceLocalArtinMonoidHom
          (K := K') (L := L') W w' x) =
      finitePlaceLocalArtinMonoidHom
        (K := K) (L := L) v w
        (LocalFieldTheory.normUnits
          (v.adicCompletion K) (W.adicCompletion K') x) := by
  let vK := NumberField.HeightOneSpectrum.adicAbv K v
  let vK' := NumberField.HeightOneSpectrum.adicAbv K' W
  let C := vK.Completion
  let D := vK'.Completion
  let eCUnits :
      Cˣ ≃* (v.adicCompletion K)ˣ :=
    finitePlaceCompletionUnitsContinuousMulEquiv v
  let eDUnits :
      Dˣ ≃* (W.adicCompletion K')ˣ :=
    finitePlaceCompletionUnitsContinuousMulEquiv W
  let : Algebra (v.adicCompletion K) (W.adicCompletion K') :=
    (finitePlaceAdicCompletionMap
      K K' v ⟨W, hW⟩).toAlgebra
  let : Algebra C D :=
    (finitePlaceArtinRelativeCompletionRingHom
      (K := K) (K' := K') v W hW).toAlgebra
  calc
    finitePlaceCrossLocalRestrictionMonoidHom
        (K := K) (L := L) (K' := K') (L' := L')
        v W hW w w' hcentres
        (finitePlaceLocalArtinMonoidHom
          (K := K') (L := L') W w' x) =
      finitePlaceLocalArtinMonoidHom
        (K := K) (L := L) v w
        (eCUnits
          (finitePlaceRelativeNormUnits
            (K := K) (K' := K') v W hW
            (eDUnits.symm x))) :=
      by
        have h :=
          finitePlaceLocalArtinMonoidHom_norm_restriction_localized
            (K := K) (L := L) (K' := K') (L' := L')
            v W hW w w' hcentres (eDUnits.symm x)
        change
          finitePlaceCrossLocalRestrictionMonoidHom
              (K := K) (L := L) (K' := K') (L' := L')
              v W hW w w' hcentres
              (finitePlaceLocalArtinMonoidHom
                (K := K') (L := L') W w'
                (eDUnits (eDUnits.symm x))) =
            finitePlaceLocalArtinMonoidHom
              (K := K) (L := L) v w
              (eCUnits
                (finitePlaceRelativeNormUnits
                  (K := K) (K' := K') v W hW
                  (eDUnits.symm x))) at h
        rw [eDUnits.apply_symm_apply] at h
        exact h
    _ =
      finitePlaceLocalArtinMonoidHom
        (K := K) (L := L) v w
        (LocalFieldTheory.normUnits
          (v.adicCompletion K) (W.adicCompletion K') x) :=
      congrArg
        (finitePlaceLocalArtinMonoidHom
          (K := K) (L := L) v w)
        (finitePlaceArtinConcreteNormUnits
          (K := K) (K' := K') v W hW x)

end FinitePlaceNormRestrictionInstances

open scoped Classical in
/-- The local Artin map attached to specified finite places carries a
local norm to the restriction of the upper Artin element. -/
theorem
    finitePlaceArtinMonoidHomOfExtension_norm_restriction
    {K' L' : Type}
    [Field K'] [NumberField K']
    [Field L'] [NumberField L']
    [Algebra K K'] [Algebra K' L'] [Algebra K L']
    [IsScalarTower K K' L']
    [Algebra L L'] [IsScalarTower K L L']
    [IsAbelianGalois K' L']
    (v : HeightOneSpectrum (𝓞 K))
    (W : HeightOneSpectrum (𝓞 K'))
    (hW : finitePlaceBelow (K := K) W = v)
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L)
    (w' : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K' W) L')
    (hcentres :
      letI : NumberField L :=
        NumberField.of_module_finite K L
      finitePlaceBelow (K := L)
          (finitePlaceExtensionCentre
            (K := K') (L := L') W w') =
        finitePlaceExtensionCentre
          (K := K) (L := L) v w) :
    letI : Algebra (v.adicCompletion K) (W.adicCompletion K') :=
      (finitePlaceAdicCompletionMap
        K K' v ⟨W, hW⟩).toAlgebra
    ((AlgEquiv.restrictNormalHom L).comp
        (AlgEquiv.restrictScalarsHom K)).comp
        (finitePlaceArtinMonoidHomOfExtension
          (K := K') (L := L') W w') =
      (finitePlaceArtinMonoidHomOfExtension
        (K := K) (L := L) v w).comp
        (LocalFieldTheory.normUnits
          (v.adicCompletion K) (W.adicCompletion K')) := by
  let : NumberField L := NumberField.of_module_finite K L
  let : Algebra (v.adicCompletion K) (W.adicCompletion K') :=
    (finitePlaceAdicCompletionMap
      K K' v ⟨W, hW⟩).toAlgebra
  let globalRestriction :
      (L' ≃ₐ[K'] L') →* (L ≃ₐ[K] L) :=
    (AlgEquiv.restrictNormalHom L).comp
      (AlgEquiv.restrictScalarsHom K)
  let localUpper :=
    finitePlaceLocalArtinMonoidHom
      (K := K') (L := L') W w'
  let localLower :=
    finitePlaceLocalArtinMonoidHom
      (K := K) (L := L) v w
  let localRestriction :=
    finitePlaceCrossLocalRestrictionMonoidHom
      (K := K) (L := L) (K' := K') (L' := L')
      v W hW w w' hcentres
  let norm :=
    LocalFieldTheory.normUnits
      (v.adicCompletion K) (W.adicCompletion K')
  calc
    globalRestriction.comp
        (finitePlaceArtinMonoidHomOfExtension
          (K := K') (L := L') W w') =
      globalRestriction.comp
        ((finitePlaceLocalToGlobalMonoidHom
          (K := K') (L := L') W w').comp localUpper) :=
      congrArg
        (fun f => globalRestriction.comp f)
        (finitePlaceArtinMonoidHomOfExtension_factor
          (K := K') (L := L') W w')
    _ =
        (globalRestriction.comp
          (finitePlaceLocalToGlobalMonoidHom
            (K := K') (L := L') W w')).comp localUpper := by
      rfl
    _ =
        ((finitePlaceLocalToGlobalMonoidHom
          (K := K) (L := L) v w).comp
          localRestriction).comp localUpper :=
      congrArg
        (fun f :
            finitePlaceNormLocalizedAut K' L' W w' →*
              (L ≃ₐ[K] L) =>
          f.comp localUpper)
        (by
          apply MonoidHom.ext
          intro tau
          exact
            finitePlaceCrossDecompositionTransport
              (K := K) (L := L) (K' := K') (L' := L')
              v W hW w w' hcentres tau)
    _ =
        (finitePlaceLocalToGlobalMonoidHom
          (K := K) (L := L) v w).comp
          (localRestriction.comp localUpper) := by
      rfl
    _ =
        (finitePlaceLocalToGlobalMonoidHom
          (K := K) (L := L) v w).comp
          (localLower.comp norm) :=
      congrArg
        (fun f => (finitePlaceLocalToGlobalMonoidHom
          (K := K) (L := L) v w).comp f)
        (by
          apply MonoidHom.ext
          intro x
          exact
            finitePlaceLocalArtinMonoidHom_norm_restriction
              (K := K) (L := L) (K' := K') (L' := L')
              v W hW w w' hcentres x)
    _ =
        ((finitePlaceLocalToGlobalMonoidHom
          (K := K) (L := L) v w).comp localLower).comp norm := by
      rfl
    _ =
        (finitePlaceArtinMonoidHomOfExtension
          (K := K) (L := L) v w).comp norm :=
      congrArg
        (fun f => f.comp norm)
        (finitePlaceArtinMonoidHomOfExtension_factor
          (K := K) (L := L) v w).symm

open scoped Classical in
/-- Finite-place norm--restriction compatibility.  Restriction of the upper
local Artin
factor is the lower local Artin factor after the norm between the
corresponding concrete adic completions. -/
theorem chosenFinitePlaceArtinMonoidHom_norm_restriction
    {K' L' : Type}
    [Field K'] [NumberField K']
    [Field L'] [NumberField L']
    [Algebra K K'] [Algebra K' L'] [Algebra K L']
    [IsScalarTower K K' L']
    [Algebra L L'] [IsScalarTower K L L']
    [IsAbelianGalois K' L']
    (W : HeightOneSpectrum (𝓞 K')) :
    let v := finitePlaceBelow (K := K) W
    letI : Algebra (v.adicCompletion K) (W.adicCompletion K') :=
      (finitePlaceAdicCompletionMap
        K K' v ⟨W, rfl⟩).toAlgebra
    ((AlgEquiv.restrictNormalHom L).comp
        (AlgEquiv.restrictScalarsHom K)).comp
        (chosenFinitePlaceArtinMonoidHom
          (K := K') (L := L') W) =
      (chosenFinitePlaceArtinMonoidHom
        (K := K) (L := L) v).comp
        (LocalFieldTheory.normUnits
          (v.adicCompletion K) (W.adicCompletion K')) := by
  let : NumberField L := NumberField.of_module_finite K L
  dsimp only
  let v :=
    finitePlaceBelow (K := K) W
  let w' :=
    chosenFinitePlaceExtension
      (L := L') W
  let U' :=
    finitePlaceExtensionCentre
      (K := K') (L := L') W w'
  let U :=
    finitePlaceBelow (K := L) U'
  have hUK : finitePlaceBelow (K := K) U = v := by
    calc
      finitePlaceBelow (K := K) U =
          finitePlaceBelow (K := K) U' := by
        exact
          finitePlaceBelow_finitePlaceBelow
            (K := K) (M := L) (L := L') U'
      _ =
          finitePlaceBelow (K := K)
            (finitePlaceBelow (K := K') U') := by
        symm
        exact
          finitePlaceBelow_finitePlaceBelow
            (K := K) (M := K') (L := L') U'
      _ = finitePlaceBelow (K := K) W := by
        rw [
          finitePlaceBelow_finitePlaceExtensionCentre
            (K := K') (L := L') W w']
      _ = v := rfl
  let Uv :
      {Q : HeightOneSpectrum (𝓞 L) //
        finitePlaceBelow (K := K) Q = v} :=
    ⟨U, hUK⟩
  let w :
      AbsoluteValueExtension
        (NumberField.HeightOneSpectrum.adicAbv K v) L :=
    (finitePlaceExtensionEquivAbove
      (K := K) (L := L) v).symm Uv
  have hwCentre :
      finitePlaceExtensionCentre
          (K := K) (L := L) v w = U := by
    have h :=
      congrArg Subtype.val
        ((finitePlaceExtensionEquivAbove
          (K := K) (L := L) v).apply_symm_apply Uv)
    simpa only [
      finitePlaceExtensionEquivAbove_coe
    ] using h
  let : Algebra (v.adicCompletion K) (W.adicCompletion K') :=
    (finitePlaceAdicCompletionMap
      K K' v ⟨W, rfl⟩).toAlgebra
  calc
    ((AlgEquiv.restrictNormalHom L).comp
        (AlgEquiv.restrictScalarsHom K)).comp
        (chosenFinitePlaceArtinMonoidHom
          (K := K') (L := L') W) =
      (finitePlaceArtinMonoidHomOfExtension
        (K := K) (L := L) v w).comp
        (LocalFieldTheory.normUnits
          (v.adicCompletion K) (W.adicCompletion K')) := by
      exact
        finitePlaceArtinMonoidHomOfExtension_norm_restriction
          (K := K) (L := L) v W rfl w w'
          (by
            change
              finitePlaceBelow (K := L) U' =
                finitePlaceExtensionCentre
                  (K := K) (L := L) v w
            rw [hwCentre])
    _ =
      (chosenFinitePlaceArtinMonoidHom
        (K := K) (L := L) v).comp
        (LocalFieldTheory.normUnits
          (v.adicCompletion K) (W.adicCompletion K')) := by
      change
        (finitePlaceArtinMonoidHomOfExtension
          (K := K) (L := L) v w).comp
            (LocalFieldTheory.normUnits
              (v.adicCompletion K) (W.adicCompletion K')) =
          (finitePlaceArtinMonoidHomOfExtension
            (K := K) (L := L) v
              (chosenFinitePlaceExtension
                (L := L) v)).comp
            (LocalFieldTheory.normUnits
              (v.adicCompletion K) (W.adicCompletion K'))
      exact congrArg
        (fun f : (v.adicCompletion K)ˣ →* (L ≃ₐ[K] L) =>
          f.comp
            (LocalFieldTheory.normUnits
              (v.adicCompletion K) (W.adicCompletion K')))
        (finitePlaceArtinMonoidHomOfExtension_eq
          (K := K) (L := L) v w
          (chosenFinitePlaceExtension
            (L := L) v))

open scoped Classical in
/-- Finite-place norm--restriction with the lower place supplied
explicitly.  This form keeps the equality proof in the completion
algebra and avoids dependent elimination through adic-completion
types. -/
theorem chosenFinitePlaceArtinMonoidHom_norm_restriction_of_below_eq
    {K' L' : Type}
    [Field K'] [NumberField K']
    [Field L'] [NumberField L']
    [Algebra K K'] [Algebra K' L'] [Algebra K L']
    [IsScalarTower K K' L']
    [Algebra L L'] [IsScalarTower K L L']
    [IsAbelianGalois K' L']
    (v : HeightOneSpectrum (𝓞 K))
    (W : HeightOneSpectrum (𝓞 K'))
    (hW : finitePlaceBelow (K := K) W = v) :
    letI : Algebra (v.adicCompletion K) (W.adicCompletion K') :=
      (finitePlaceAdicCompletionMap
        K K' v ⟨W, hW⟩).toAlgebra
    ((AlgEquiv.restrictNormalHom L).comp
        (AlgEquiv.restrictScalarsHom K)).comp
        (chosenFinitePlaceArtinMonoidHom
          (K := K') (L := L') W) =
      (chosenFinitePlaceArtinMonoidHom
        (K := K) (L := L) v).comp
        (LocalFieldTheory.normUnits
          (v.adicCompletion K) (W.adicCompletion K')) := by
  subst v
  exact
    chosenFinitePlaceArtinMonoidHom_norm_restriction
      (K := K) (L := L) (K' := K') (L' := L') W

end Reciprocity
end GlobalClassFieldTheory
