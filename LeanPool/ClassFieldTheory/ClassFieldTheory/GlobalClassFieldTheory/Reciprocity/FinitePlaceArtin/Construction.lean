/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Completion.Comparison
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.IdealMap
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.NormApproximation.FinitePlaces
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalizedCompletionCohomology.CompMulEquiv
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalizedCompletionCohomology.Algebra
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalizedCompletionCohomology.Generator
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalizedCompletionCohomology.HerbrandEquiv
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalizedCompletionCohomology.Finite
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalizedCompletionCohomology.Cardinality.H0
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalizedCompletionCohomology.Cardinality.HMinusOne
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalizedCompletionCohomology.Cardinality.Trivial
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalizedCompletionCohomology.Cardinality.Quotient
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.NormResidue
/-!
# Construction of finite-place Artin homomorphisms

This module constructs the local Artin map for a chosen extension of a finite place and
  transports it through the actual decomposition group into the global Galois group.
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
    [hKLfinite : FiniteDimensional K L] [IsAbelianGalois K L]

open scoped Classical in
/-- A completion attached to a nonarchimedean absolute value has an ultrametric distance. -/
theorem finitePlaceArtinCompletionIsUltrametricDist
    {F : Type} [Field F]
    (vF : AbsoluteValue F ℝ)
    (hvF : IsNonarchimedean (vF : F → ℝ)) :
    IsUltrametricDist vF.Completion :=
  IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
    (AbsoluteValue.completionAbsoluteValue_isNonarchimedean
      vF hvF)

open scoped Classical in
/-- The valued-field structure on a finite-place completion induced by its nonarchimedean norm. -/
@[reducible]
noncomputable def finitePlaceArtinCompletionValued
    {F : Type} [Field F]
    (vF : AbsoluteValue F ℝ)
    (hvF : IsNonarchimedean (vF : F → ℝ)) :
    Valued vF.Completion ℝ≥0 :=
  letI : IsUltrametricDist vF.Completion :=
    finitePlaceArtinCompletionIsUltrametricDist vF hvF
  NormedField.toValued

open scoped Classical in
/-- The valuation relation on a finite-place completion induced by its canonical valuation. -/
@[reducible]
noncomputable def finitePlaceArtinCompletionValuativeRel
    {F : Type} [Field F]
    (vF : AbsoluteValue F ℝ)
    (hvF : IsNonarchimedean (vF : F → ℝ)) :
    ValuativeRel vF.Completion := by
  letI : Valued vF.Completion ℝ≥0 :=
    finitePlaceArtinCompletionValued vF hvF
  exact ValuativeRel.ofValuation
    (Valued.v : Valuation vF.Completion ℝ≥0)

open scoped Classical in
/-- The canonical valued structure makes a locally compact finite-place completion a
nonarchimedean local field. -/
theorem
    finitePlaceArtinCompletionIsNonarchimedeanLocalField
    {F : Type} [Field F]
    (vF : AbsoluteValue F ℝ)
    (hvF : IsNonarchimedean (vF : F → ℝ))
    [IsUltrametricDist vF.Completion]
    [(NormedField.valuation
      (K := vF.Completion)).IsNontrivial]
    [LocallyCompactSpace vF.Completion] :
    letI : Valued vF.Completion ℝ≥0 :=
      finitePlaceArtinCompletionValued vF hvF
    letI : ValuativeRel vF.Completion :=
      finitePlaceArtinCompletionValuativeRel vF hvF
    IsNonarchimedeanLocalField vF.Completion := by
  let : Valued vF.Completion ℝ≥0 :=
    finitePlaceArtinCompletionValued vF hvF
  let vC : Valuation vF.Completion ℝ≥0 := Valued.v
  let : vC.IsNontrivial :=
    (inferInstance :
      (NormedField.valuation
        (K := vF.Completion)).IsNontrivial)
  let : ValuativeRel vF.Completion :=
    finitePlaceArtinCompletionValuativeRel vF hvF
  let : vC.Compatible :=
    Valuation.Compatible.ofValuation vC
  let : ValuativeRel.IsNontrivial vF.Completion :=
    (ValuativeRel.isNontrivial_iff_isNontrivial vC).2
      inferInstance
  let : IsValuativeTopology vF.Completion :=
    isValuativeTopology_of_valued_ofValuation
      vF.Completion ℝ≥0
  exact
    { toIsValuativeTopology := inferInstance
      toLocallyCompactSpace := inferInstance
      toIsNontrivial := inferInstance }

open scoped Classical in
/-- The concrete finite-completion ring equivalence agrees with the
relative-completion algebra equivalence on underlying rings. -/
theorem finitePlaceCompletionRingEquiv_eq_relative
    {F : Type} [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) :
    finitePlaceCompletionRingEquiv v =
      (relativeFinitePlaceCompletionAlgEquiv v).toRingEquiv := by
  apply RingEquiv.ext
  intro x
  change
    finitePlaceCompletionRingHom v x =
      relativeFinitePlaceCompletionRingHom v x
  refine UniformSpace.Completion.induction_on
    (α := WithAbs
      (NumberField.HeightOneSpectrum.adicAbv F v)) x ?_ ?_
  · exact isClosed_eq
      (finitePlaceCompletionRingHom_isometry v).continuous
      (relativeFinitePlaceCompletionRingHom_isometry v).continuous
  · intro a
    rw [finitePlaceCompletionRingHom_coe,
      relativeFinitePlaceCompletionRingHom_coe]
    rfl

open scoped Classical in
/-- The finite-place Artin homomorphism associated with a specified
extension of the base adic absolute value to the global extension. -/
noncomputable def finitePlaceArtinMonoidHomOfExtension
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L) :
    (v.adicCompletion K)ˣ →* (L ≃ₐ[K] L) := by
  let vK :=
    NumberField.HeightOneSpectrum.adicAbv K v
  let hvK : vK.IsNontrivial :=
    RayClass.adicAbv_isNontrivial v
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
  let E :=
    AlgebraicNumberTheory.Valuations.LocalizedCompletion vK w
  letI : FiniteDimensional vK.Completion E :=
    AlgebraicNumberTheory.Valuations.localizedCompletionModuleFinite vK hvK w
  letI : IsAbelianGalois vK.Completion E :=
    LocalClassFieldTheory.localizedCompletion_isAbelianGalois
      vK hvK w
  letI : NontriviallyNormedField vK.Completion :=
    absoluteValueExtensionCompletionNontriviallyNormedField
      vK hvK
  letI : LocallyCompactSpace vK.Completion :=
    AbsoluteValue.Completion.locallyCompactSpace
      (finitePlaceCompletionBaseMap_isometry v)
  let hvKna : IsNonarchimedean (vK : K → ℝ) :=
    NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv K v
  letI : IsUltrametricDist vK.Completion :=
    finitePlaceArtinCompletionIsUltrametricDist vK hvKna
  letI : Valued vK.Completion ℝ≥0 :=
    finitePlaceArtinCompletionValued vK hvKna
  let vC : Valuation vK.Completion ℝ≥0 :=
    Valued.v
  letI : vC.IsNontrivial :=
    (inferInstance :
      (NormedField.valuation
        (K := vK.Completion)).IsNontrivial)
  letI : ValuativeRel vK.Completion :=
    finitePlaceArtinCompletionValuativeRel vK hvKna
  letI : vC.Compatible :=
    Valuation.Compatible.ofValuation vC
  letI : ValuativeRel.IsNontrivial vK.Completion :=
    (ValuativeRel.isNontrivial_iff_isNontrivial vC).2
      inferInstance
  letI : IsValuativeTopology vK.Completion :=
    isValuativeTopology_of_valued_ofValuation
      vK.Completion ℝ≥0
  letI : IsNonarchimedeanLocalField vK.Completion :=
    { toIsValuativeTopology := inferInstance
      toLocallyCompactSpace := inferInstance
      toIsNontrivial := inferInstance }
  let eD :
      absoluteValueDecompositionGroup K w.1 ≃*
        (E ≃ₐ[vK.Completion] E) :=
    decompositionGroupEquivAlgebraicLocalizationAut
      vK hvK w
  let eK :
      vK.Completionˣ ≃* (v.adicCompletion K)ˣ :=
    finitePlaceCompletionUnitsContinuousMulEquiv v
  exact
    (absoluteValueDecompositionGroup K w.1).subtype.comp
      (eD.symm.toMonoidHom.comp
        ((LocalClassFieldTheory.abelianLocalArtinMonoidHom
          vK.Completion E).comp eK.symm.toMonoidHom))

open scoped Classical in
/-- Pointwise formula for the finite-place Artin homomorphism attached
to a specified extension of the base absolute value. -/
theorem finitePlaceArtinMonoidHomOfExtension_apply
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L)
    (x : (v.adicCompletion K)ˣ) :
    let vK :=
      NumberField.HeightOneSpectrum.adicAbv K v
    let hvK : vK.IsNontrivial :=
      RayClass.adicAbv_isNontrivial v
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
    let E :=
      AlgebraicNumberTheory.Valuations.LocalizedCompletion vK w
    letI : FiniteDimensional vK.Completion E :=
      AlgebraicNumberTheory.Valuations.localizedCompletionModuleFinite vK hvK w
    letI : IsAbelianGalois vK.Completion E :=
      LocalClassFieldTheory.localizedCompletion_isAbelianGalois
        vK hvK w
    letI : NontriviallyNormedField vK.Completion :=
      absoluteValueExtensionCompletionNontriviallyNormedField
        vK hvK
    letI : LocallyCompactSpace vK.Completion :=
      AbsoluteValue.Completion.locallyCompactSpace
        (finitePlaceCompletionBaseMap_isometry v)
    letI : IsUltrametricDist vK.Completion :=
      IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
        (AbsoluteValue.completionAbsoluteValue_isNonarchimedean
          vK
          (NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv
            K v))
    letI : Valued vK.Completion ℝ≥0 :=
      NormedField.toValued
    let vC : Valuation vK.Completion ℝ≥0 :=
      Valued.v
    letI : vC.IsNontrivial :=
      (inferInstance :
        (NormedField.valuation
          (K := vK.Completion)).IsNontrivial)
    letI : ValuativeRel vK.Completion :=
      ValuativeRel.ofValuation vC
    letI : vC.Compatible :=
      Valuation.Compatible.ofValuation vC
    letI : ValuativeRel.IsNontrivial vK.Completion :=
      (ValuativeRel.isNontrivial_iff_isNontrivial vC).2
        inferInstance
    letI : IsValuativeTopology vK.Completion :=
      isValuativeTopology_of_valued_ofValuation
        vK.Completion ℝ≥0
    letI : IsNonarchimedeanLocalField vK.Completion :=
      { toIsValuativeTopology := inferInstance
        toLocallyCompactSpace := inferInstance
        toIsNontrivial := inferInstance }
    let eD :
        absoluteValueDecompositionGroup K w.1 ≃*
          (E ≃ₐ[vK.Completion] E) :=
      decompositionGroupEquivAlgebraicLocalizationAut
        vK hvK w
    let eK :
        vK.Completionˣ ≃* (v.adicCompletion K)ˣ :=
      finitePlaceCompletionUnitsContinuousMulEquiv v
    finitePlaceArtinMonoidHomOfExtension
        (K := K) (L := L) v w x =
      (absoluteValueDecompositionGroup K w.1).subtype
        (eD.symm
          (LocalClassFieldTheory.abelianLocalArtinMonoidHom
            vK.Completion E (eK.symm x))) := by
  rfl

open scoped Classical in
/-- The canonical completion input used by the finite-place local Artin map. -/
noncomputable def finitePlaceLocalArtinInputMonoidHom
    (v : HeightOneSpectrum (𝓞 K)) :
    (v.adicCompletion K)ˣ →*
      (NumberField.HeightOneSpectrum.adicAbv K v).Completionˣ :=
  (finitePlaceCompletionUnitsContinuousMulEquiv v).symm.toMonoidHom

open scoped Classical in
/-- Evaluation of the canonical completion input for the finite-place local
Artin map. -/
noncomputable def finitePlaceLocalArtinInput
    (v : HeightOneSpectrum (𝓞 K))
    (x : (v.adicCompletion K)ˣ) :
    (NumberField.HeightOneSpectrum.adicAbv K v).Completionˣ :=
  finitePlaceLocalArtinInputMonoidHom v x

open scoped Classical in
/-- The canonical valuation relation used on a finite-place completion by
the local Artin construction. -/
@[reducible]
noncomputable def finitePlaceLocalArtinCompletionValuativeRel
    (v : HeightOneSpectrum (𝓞 K)) :
    ValuativeRel
      (NumberField.HeightOneSpectrum.adicAbv K v).Completion :=
  finitePlaceArtinCompletionValuativeRel
    (NumberField.HeightOneSpectrum.adicAbv K v)
    (NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv K v)

open scoped Classical in
/-- The canonical nonarchimedean-local-field certificate used on a
finite-place completion by the local Artin construction. -/
theorem
    finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField
    (v : HeightOneSpectrum (𝓞 K)) :
    @IsNonarchimedeanLocalField
      (NumberField.HeightOneSpectrum.adicAbv K v).Completion
      (inferInstance : Field
        (NumberField.HeightOneSpectrum.adicAbv K v).Completion)
      (finitePlaceLocalArtinCompletionValuativeRel v)
      (inferInstance : TopologicalSpace
        (NumberField.HeightOneSpectrum.adicAbv K v).Completion) := by
  let vK := NumberField.HeightOneSpectrum.adicAbv K v
  let hvK : vK.IsNontrivial :=
    RayClass.adicAbv_isNontrivial v
  let : NontriviallyNormedField vK.Completion :=
    absoluteValueExtensionCompletionNontriviallyNormedField
      vK hvK
  let : LocallyCompactSpace vK.Completion :=
    AbsoluteValue.Completion.locallyCompactSpace
      (finitePlaceCompletionBaseMap_isometry v)
  let hvKna : IsNonarchimedean (vK : K → ℝ) :=
    NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv K v
  let : IsUltrametricDist vK.Completion :=
    finitePlaceArtinCompletionIsUltrametricDist vK hvKna
  let : Valued vK.Completion ℝ≥0 :=
    finitePlaceArtinCompletionValued vK hvKna
  let : ValuativeRel vK.Completion :=
    finitePlaceLocalArtinCompletionValuativeRel v
  exact
    finitePlaceArtinCompletionIsNonarchimedeanLocalField
      vK hvKna

open scoped Classical in
/-- The local Artin input of a chosen order-one prime element has the
inverse-standard normalized local valuation. -/
theorem finitePlaceLocalArtinInput_chosenLocalOrderSection_valuationMap
    (v : HeightOneSpectrum (𝓞 K)) :
    let C := (NumberField.HeightOneSpectrum.adicAbv K v).Completion
    letI : ValuativeRel C := finitePlaceLocalArtinCompletionValuativeRel v
    letI : IsNonarchimedeanLocalField C :=
      finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
    IsNonarchimedeanLocalField.valuationMap C
      (Additive.ofMul
        (finitePlaceLocalArtinInput v
          (FiniteIdeleGroup.chosenLocalOrderSection v 1))) = -1 := by
  let C := (NumberField.HeightOneSpectrum.adicAbv K v).Completion
  let a : (v.adicCompletion K)ˣ :=
    FiniteIdeleGroup.chosenLocalOrderSection v 1
  let x : Cˣ := finitePlaceLocalArtinInput v a
  let : IsUltrametricDist C :=
    finitePlaceArtinCompletionIsUltrametricDist
      (NumberField.HeightOneSpectrum.adicAbv K v)
      (NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv K v)
  let : ValuativeRel C := finitePlaceLocalArtinCompletionValuativeRel v
  let : IsNonarchimedeanLocalField C :=
    finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
  let f := finitePlaceCompletionRingHom v
  have hfx : f (x : C) = (a : v.adicCompletion K) := by
    exact congrArg Units.val
      ((finitePlaceCompletionUnitsContinuousMulEquiv v).apply_symm_apply a)
  have hva : Valued.v (a : v.adicCompletion K) =
      WithZero.exp (-1 : ℤ) := by
    change Valued.v (Classical.choose
      (HeightOneSpectrum.valuedAdicCompletion_surjective K v
        (WithZero.exp (-1 : ℤ)))) = _
    exact Classical.choose_spec
      (HeightOneSpectrum.valuedAdicCompletion_surjective K v
        (WithZero.exp (-1 : ℤ)))
  have horder (y z : C) :
      ValuativeRel.valuation C y ≤ ValuativeRel.valuation C z ↔
        ‖y‖ ≤ ‖z‖ := by
    change ValuativeRel.ValueGroupWithZero.mk y 1 ≤
      ValuativeRel.ValueGroupWithZero.mk z 1 ↔ _
    rw [ValuativeRel.ValueGroupWithZero.mk_le_mk]
    simp only [Submonoid.coe_one, mul_one]
    change NormedField.valuation y ≤ NormedField.valuation z ↔ _
    simp only [NormedField.valuation_apply, ← NNReal.coe_le_coe, coe_nnnorm]
  have hlt (y z : C) :
      ValuativeRel.valuation C y < ValuativeRel.valuation C z ↔
        ‖y‖ < ‖z‖ := by
    rw [lt_iff_le_not_ge, lt_iff_le_not_ge]
    exact and_congr (horder y z) (not_congr (horder z y))
  have hIntegerBound (η : WithZero (Multiplicative ℤ)) (hη : η < 1) :
      η ≤ WithZero.exp (-1 : ℤ) := by
    cases η using WithZero.recZeroCoe with
    | zero => exact bot_le
    | coe d =>
        change (d : WithZero (Multiplicative ℤ)) ≤
          ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) :
            WithZero (Multiplicative ℤ))
        rw [WithZero.coe_le_coe]
        rw [← Multiplicative.toAdd_le]
        change Multiplicative.toAdd d ≤ (-1 : ℤ)
        have hd : Multiplicative.toAdd d < 0 := by
          have hd' : d < (1 : Multiplicative ℤ) := by
            simpa using hη
          exact Multiplicative.toAdd_lt.mp hd'
        omega
  have hNormInput : ‖(x : C)‖ = ‖(a : v.adicCompletion K)‖ := by
    rw [← hfx]
    exact ((finitePlaceCompletionRingHom_isometry v).norm_map_of_map_zero
      (map_zero f) (x : C)).symm
  have hMax : ∀ δ : ValuativeRel.ValueGroupWithZero C,
      δ < 1 → δ ≤ ValuativeRel.valuation C (x : C) := by
    intro δ hδ
    obtain ⟨y, rfl⟩ := ValuativeRel.valuation_surjective δ
    have hyNorm : ‖y‖ < 1 := by
      simpa only [norm_one] using (hlt y 1).mp (by simpa using hδ)
    have hyConcrete : ‖f y‖ < 1 := by
      rw [(finitePlaceCompletionRingHom_isometry v).norm_map_of_map_zero
        (map_zero f) y]
      exact hyNorm
    let q : ℝ≥0 := v.asIdeal.absNorm
    have hq : 1 < q := HeightOneSpectrum.one_lt_absNorm_nnreal v
    have hyVal : Valued.v (f y) <
        (1 : WithZero (Multiplicative ℤ)) := by
      apply (WithZeroMulInt.toNNReal_lt_one_iff hq).mp
      exact NNReal.coe_lt_coe.mp (by
        simpa only [FinitePlace.norm_def, NNReal.coe_one] using hyConcrete)
    have hyLe := hIntegerBound (Valued.v (f y)) hyVal
    have hyNormLe : ‖f y‖ ≤ ‖(a : v.adicCompletion K)‖ := by
      rw [FinitePlace.norm_def, FinitePlace.norm_def, hva]
      exact NNReal.coe_le_coe.mpr
        ((WithZeroMulInt.toNNReal_strictMono hq).monotone hyLe)
    apply (horder y (x : C)).mpr
    rw [hNormInput]
    rw [← (finitePlaceCompletionRingHom_isometry v).norm_map_of_map_zero
      (map_zero f) y]
    exact hyNormLe
  let φ := _root_.IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt C
  have hφlt : φ (ValuativeRel.valuation C (x : C)) < 1 := by
    have hval : WithZero.exp (-1 : ℤ) <
        (1 : WithZero (Multiplicative ℤ)) := by
      rw [WithZero.exp_eq_coe_ofAdd, ← WithZero.coe_one,
        WithZero.coe_lt_coe]
      change (Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) < 1
      change (-1 : ℤ) < 0
      omega
    have hnorm : ‖(x : C)‖ < 1 := by
      rw [hNormInput, FinitePlace.norm_def, hva]
      exact_mod_cast
        (WithZeroMulInt.toNNReal_lt_one_iff
          (HeightOneSpectrum.one_lt_absNorm_nnreal v)).mpr hval
    have hv : ValuativeRel.valuation C (x : C) < 1 := by
      exact (hlt (x : C) 1).mpr (by simpa only [norm_one] using hnorm)
    simpa only [map_one] using φ.strictMono hv
  have hφmax : ∀ η : WithZero (Multiplicative ℤ),
      η < 1 → η ≤ φ (ValuativeRel.valuation C (x : C)) := by
    intro η hη
    let δ := φ.symm η
    have hδ : δ < 1 := by
      simpa only [map_one] using φ.symm.strictMono hη
    have h := φ.strictMono.monotone (hMax δ hδ)
    change φ (φ.symm η) ≤ _ at h
    simpa only [φ.apply_symm_apply] using h
  have hφeq : φ (ValuativeRel.valuation C (x : C)) =
      WithZero.exp (-1 : ℤ) := by
    apply le_antisymm
    · exact hIntegerBound _ hφlt
    · apply hφmax
      rw [WithZero.exp_eq_coe_ofAdd, ← WithZero.coe_one,
        WithZero.coe_lt_coe]
      change (Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) < 1
      change (-1 : ℤ) < 0
      omega
  change IsNonarchimedeanLocalField.valuationMap C (Additive.ofMul x) = -1
  rw [IsNonarchimedeanLocalField.valuationMap_apply,
    IsNonarchimedeanLocalField.v_apply]
  change Multiplicative.toAdd
    (WithZero.unzero
      (x := φ (ValuativeRel.valuation C (x : C))) (by simp)) = -1
  rw [WithZero.toAdd_unzero_eq_log, hφeq, WithZero.log_exp]

open scoped Classical in
/-- The canonical algebra structure on the localized completion used by the
finite-place local Artin map. -/
@[reducible]
noncomputable def finitePlaceLocalArtinLocalizedAlgebra
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L) :
    let vK := NumberField.HeightOneSpectrum.adicAbv K v
    Algebra vK.Completion
      (AlgebraicNumberTheory.Valuations.LocalizedCompletion vK w) := by
  let vK := NumberField.HeightOneSpectrum.adicAbv K v
  letI hK :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K) w.1
  letI : SMul K w.1.Completion := hK.toSMul
  letI : Algebra vK.Completion w.1.Completion :=
    AbsoluteValue.completionAlgebra vK w.1 w.2
  exact inferInstance

omit [IsAbelianGalois K L] in
open scoped Classical in
/-- The canonical finite-dimensional certificate for the localized
completion used by the finite-place local Artin map. -/
theorem finitePlaceLocalArtinFiniteDimensional
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L) :
    let vK := NumberField.HeightOneSpectrum.adicAbv K v
    let E := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK w
    letI : Algebra vK.Completion E :=
      finitePlaceLocalArtinLocalizedAlgebra v w
    FiniteDimensional vK.Completion E := by
  let vK := NumberField.HeightOneSpectrum.adicAbv K v
  let hvK : vK.IsNontrivial :=
    RayClass.adicAbv_isNontrivial v
  let hK :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K) w.1
  let : SMul K w.1.Completion := hK.toSMul
  let : Algebra vK.Completion w.1.Completion :=
    AbsoluteValue.completionAlgebra vK w.1 w.2
  let E := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK w
  let : Algebra vK.Completion E :=
    finitePlaceLocalArtinLocalizedAlgebra v w
  exact
    AlgebraicNumberTheory.Valuations.localizedCompletionModuleFinite
      vK hvK w

omit hKLfinite in
open scoped Classical in
/-- The canonical abelian-Galois certificate for the localized completion
used by the finite-place local Artin map. -/
theorem finitePlaceLocalArtinIsAbelianGalois
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L)
    (_hKLfinite : FiniteDimensional K L) :
    let vK := NumberField.HeightOneSpectrum.adicAbv K v
    let E := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK w
    letI : Algebra vK.Completion E :=
      finitePlaceLocalArtinLocalizedAlgebra v w
    IsAbelianGalois vK.Completion E := by
  let : FiniteDimensional K L := _hKLfinite
  let vK := NumberField.HeightOneSpectrum.adicAbv K v
  let hvK : vK.IsNontrivial :=
    RayClass.adicAbv_isNontrivial v
  let hK :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K) w.1
  let : SMul K w.1.Completion := hK.toSMul
  let : Algebra vK.Completion w.1.Completion :=
    AbsoluteValue.completionAlgebra vK w.1 w.2
  let E :=
    AlgebraicNumberTheory.Valuations.LocalizedCompletion vK w
  let : Algebra vK.Completion E :=
    finitePlaceLocalArtinLocalizedAlgebra v w
  let : FiniteDimensional vK.Completion E :=
    finitePlaceLocalArtinFiniteDimensional
      (hKLfinite := _hKLfinite) v w
  exact
    LocalClassFieldTheory.localizedCompletion_isAbelianGalois
      vK hvK w

open scoped Classical in
/-- The local Artin homomorphism on the algebraic localization attached to a chosen extension of
a finite place. -/
noncomputable def finitePlaceLocalArtinMonoidHom
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L) :
    let vK := NumberField.HeightOneSpectrum.adicAbv K v
    let E := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK w
    letI : Algebra vK.Completion E :=
      finitePlaceLocalArtinLocalizedAlgebra v w
    (v.adicCompletion K)ˣ →* (E ≃ₐ[vK.Completion] E) := by
  let vK := NumberField.HeightOneSpectrum.adicAbv K v
  let E := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK w
  letI : Algebra vK.Completion E :=
    finitePlaceLocalArtinLocalizedAlgebra v w
  letI : FiniteDimensional vK.Completion E :=
    finitePlaceLocalArtinFiniteDimensional v w
  letI : IsAbelianGalois vK.Completion E :=
    finitePlaceLocalArtinIsAbelianGalois v w hKLfinite
  letI : ValuativeRel vK.Completion :=
    finitePlaceLocalArtinCompletionValuativeRel v
  letI : IsNonarchimedeanLocalField vK.Completion :=
    finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
  exact
    (LocalClassFieldTheory.abelianLocalArtinMonoidHom
      vK.Completion E).comp
        (finitePlaceLocalArtinInputMonoidHom v)

open scoped Classical in
/-- Evaluation of the localized finite-place Artin homomorphism through the canonical completion
equivalence. -/
theorem finitePlaceLocalArtinMonoidHom_apply
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L)
    (x : (v.adicCompletion K)ˣ) :
    let vK := NumberField.HeightOneSpectrum.adicAbv K v
    let hvK : vK.IsNontrivial :=
      RayClass.adicAbv_isNontrivial v
    letI hK :=
      AbsoluteValue.extensionCompletionAlgebra
        (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI : Algebra vK.Completion w.1.Completion :=
      AbsoluteValue.completionAlgebra vK w.1 w.2
    let E := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK w
    letI : FiniteDimensional vK.Completion E :=
      AlgebraicNumberTheory.Valuations.localizedCompletionModuleFinite vK hvK w
    letI : IsAbelianGalois vK.Completion E :=
      LocalClassFieldTheory.localizedCompletion_isAbelianGalois
        vK hvK w
    letI : NontriviallyNormedField vK.Completion :=
      absoluteValueExtensionCompletionNontriviallyNormedField
        vK hvK
    letI : LocallyCompactSpace vK.Completion :=
      AbsoluteValue.Completion.locallyCompactSpace
        (finitePlaceCompletionBaseMap_isometry v)
    let hvKna : IsNonarchimedean (vK : K → ℝ) :=
      NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv K v
    letI : IsUltrametricDist vK.Completion :=
      finitePlaceArtinCompletionIsUltrametricDist vK hvKna
    letI : Valued vK.Completion ℝ≥0 :=
      finitePlaceArtinCompletionValued vK hvKna
    letI : ValuativeRel vK.Completion :=
      finitePlaceArtinCompletionValuativeRel vK hvKna
    letI : IsNonarchimedeanLocalField vK.Completion :=
      finitePlaceArtinCompletionIsNonarchimedeanLocalField
        vK hvKna
    let eK :
        vK.Completionˣ ≃* (v.adicCompletion K)ˣ :=
      finitePlaceCompletionUnitsContinuousMulEquiv v
    finitePlaceLocalArtinMonoidHom
        (K := K) (L := L) v w x =
      LocalClassFieldTheory.abelianLocalArtinMonoidHom
        vK.Completion E (eK.symm x) := by
  rfl

open scoped Classical in
/-- Evaluation of the localized finite-place Artin homomorphism with all
canonical completion data hidden behind named opaque terms.  This is the
normalization API for clients that must not unfold the construction's
dependent instance tower. -/
theorem finitePlaceLocalArtinMonoidHom_apply_normalized
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L)
    (x : (v.adicCompletion K)ˣ) :
    finitePlaceLocalArtinMonoidHom
        (K := K) (L := L) v w x =
      @LocalClassFieldTheory.abelianLocalArtinMonoidHom
        (NumberField.HeightOneSpectrum.adicAbv K v).Completion
        (AlgebraicNumberTheory.Valuations.LocalizedCompletion
          (NumberField.HeightOneSpectrum.adicAbv K v) w)
        (inferInstance : Field
          (NumberField.HeightOneSpectrum.adicAbv K v).Completion)
        (inferInstance : Field
          (AlgebraicNumberTheory.Valuations.LocalizedCompletion
            (NumberField.HeightOneSpectrum.adicAbv K v) w))
        (finitePlaceLocalArtinLocalizedAlgebra v w)
        (finitePlaceLocalArtinCompletionValuativeRel v)
        (inferInstance : TopologicalSpace
          (NumberField.HeightOneSpectrum.adicAbv K v).Completion)
        (finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v)
        (finitePlaceLocalArtinFiniteDimensional v w)
        (finitePlaceLocalArtinIsAbelianGalois v w hKLfinite)
        (finitePlaceLocalArtinInput v x) := by
  rfl

open scoped Classical in
/-- Elementwise evaluation of the normalized localized finite-place Artin
map.  This form lets clients transport an action without asking the
elaborator to rewrite an equality of automorphisms carrying a dependent
instance tower. -/
theorem finitePlaceLocalArtinMonoidHom_apply_normalized_at
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L)
    (x : (v.adicCompletion K)ˣ)
    (z : AlgebraicNumberTheory.Valuations.LocalizedCompletion
      (NumberField.HeightOneSpectrum.adicAbv K v) w) :
    finitePlaceLocalArtinMonoidHom
        (K := K) (L := L) v w x z =
      (@LocalClassFieldTheory.abelianLocalArtinMonoidHom
        (NumberField.HeightOneSpectrum.adicAbv K v).Completion
        (AlgebraicNumberTheory.Valuations.LocalizedCompletion
          (NumberField.HeightOneSpectrum.adicAbv K v) w)
        (inferInstance : Field
          (NumberField.HeightOneSpectrum.adicAbv K v).Completion)
        (inferInstance : Field
          (AlgebraicNumberTheory.Valuations.LocalizedCompletion
            (NumberField.HeightOneSpectrum.adicAbv K v) w))
        (finitePlaceLocalArtinLocalizedAlgebra v w)
        (finitePlaceLocalArtinCompletionValuativeRel v)
        (inferInstance : TopologicalSpace
          (NumberField.HeightOneSpectrum.adicAbv K v).Completion)
        (finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v)
        (finitePlaceLocalArtinFiniteDimensional v w)
        (finitePlaceLocalArtinIsAbelianGalois v w hKLfinite)
        (finitePlaceLocalArtinInput v x)) z := by
  exact
    congrArg (fun sigma => sigma z)
      (finitePlaceLocalArtinMonoidHom_apply_normalized
        (K := K) (L := L) v w x)

open scoped Classical in
/-- The decomposition-group inclusion transporting localized automorphisms to the global Galois
group. -/
noncomputable def finitePlaceLocalToGlobalMonoidHom
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L) :
    let vK := NumberField.HeightOneSpectrum.adicAbv K v
    let E := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK w
    letI : Algebra vK.Completion E :=
      finitePlaceLocalArtinLocalizedAlgebra v w
    (E ≃ₐ[vK.Completion] E) →* (L ≃ₐ[K] L) := by
  let vK := NumberField.HeightOneSpectrum.adicAbv K v
  let hvK : vK.IsNontrivial :=
    RayClass.adicAbv_isNontrivial v
  let E := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK w
  letI : Algebra vK.Completion E :=
    finitePlaceLocalArtinLocalizedAlgebra v w
  let eD :
      absoluteValueDecompositionGroup K w.1 ≃*
        (E ≃ₐ[vK.Completion] E) :=
    decompositionGroupEquivAlgebraicLocalizationAut
      vK hvK w
  exact
    (absoluteValueDecompositionGroup K w.1).subtype.comp
      eD.symm.toMonoidHom

open scoped Classical in
/-- The finite-place Artin map factors through the localized Artin map and the
decomposition-group inclusion. -/
theorem finitePlaceArtinMonoidHomOfExtension_factor
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L) :
    finitePlaceArtinMonoidHomOfExtension
        (K := K) (L := L) v w =
      (finitePlaceLocalToGlobalMonoidHom
        (K := K) (L := L) v w).comp
        (finitePlaceLocalArtinMonoidHom
          (K := K) (L := L) v w) := by
  rfl

open scoped Classical in
/-- Evaluation of the global finite-place Artin homomorphism with the
localized Artin map and its decomposition-group transport expressed through
the canonical named data. -/
theorem finitePlaceArtinMonoidHomOfExtension_apply_normalized
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L)
    (x : (v.adicCompletion K)ˣ) :
    let vK := NumberField.HeightOneSpectrum.adicAbv K v
    let hvK : vK.IsNontrivial :=
      RayClass.adicAbv_isNontrivial v
    let E := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK w
    letI : Algebra vK.Completion E :=
      finitePlaceLocalArtinLocalizedAlgebra v w
    let eD :
        absoluteValueDecompositionGroup K w.1 ≃*
          (E ≃ₐ[vK.Completion] E) :=
      decompositionGroupEquivAlgebraicLocalizationAut vK hvK w
    finitePlaceArtinMonoidHomOfExtension
        (K := K) (L := L) v w x =
      (absoluteValueDecompositionGroup K w.1).subtype
        (eD.symm
          (@LocalClassFieldTheory.abelianLocalArtinMonoidHom
            vK.Completion E
            (inferInstance : Field vK.Completion)
            (inferInstance : Field E)
            (finitePlaceLocalArtinLocalizedAlgebra v w)
            (finitePlaceLocalArtinCompletionValuativeRel v)
            (inferInstance : TopologicalSpace vK.Completion)
            (finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v)
            (finitePlaceLocalArtinFiniteDimensional v w)
            (finitePlaceLocalArtinIsAbelianGalois v w hKLfinite)
            (finitePlaceLocalArtinInput v x))) := by
  rw [finitePlaceArtinMonoidHomOfExtension_factor,
    MonoidHom.comp_apply,
    finitePlaceLocalArtinMonoidHom_apply_normalized]
  rfl

open scoped Classical in
/-- The finite-place Artin homomorphism from the concrete adic
completion into the actual global Galois group.  Its image is contained
in the decomposition group at the chosen extension above `v`. -/
noncomputable def chosenFinitePlaceArtinMonoidHom
    (v : HeightOneSpectrum (𝓞 K)) :
    (v.adicCompletion K)ˣ →* (L ≃ₐ[K] L) :=
  finitePlaceArtinMonoidHomOfExtension
    (K := K) (L := L) v
    (chosenFinitePlaceExtension (L := L) v)

end Reciprocity
end GlobalClassFieldTheory
