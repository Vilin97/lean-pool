/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.NormResidue
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.NormRestriction
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.UnramifiedNormalization
import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.FieldUnitDecomposition
import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.PadicField
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FiniteLevel.HigherUnitLevelEquiv
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.Padic.CompletedChangedStandardFrobenius
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.Padic.MultiplicativeEvaluation.Core
/-!
# The local Artin map on multiplicative p-adic Lubin--Tate levels

This file compares the actual finite local Artin map with the explicit
multiplicative Lubin--Tate action.  The first source-produced comparison is
on the deepest invisible principal-unit group: a unit in `U^(n + 1)` is an
actual norm from level `n`, while its finite Lubin--Tate parameter class is
trivial.  Consequently the two automorphisms agree there, and the resulting
action on the chosen primitive root is the explicit cyclotomic action.
-/

noncomputable section

open scoped ValuativeRel

namespace LocalClassFieldTheory

open LubinTate
open LocalFieldTheory
open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.Examples.Qp
open LocalFieldTheory.DiscreteValuationField.ValuedExtension
open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension

/-- The negative changed-uniformizer prime element as an actual unit of its
completed fixed field.  Its norm is the changed base uniformizer `u p`. -/
noncomputable def padicCompletedChangedUniformizerNegativePrimeUnit
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (u : (padicLocalField p).valuationSubringˣ) :
    (padicCompletedChangedUniformizerFixedField p u n)ˣ :=
  Units.mk0
    (-padicCompletedChangedUniformizerPrimeElement p u n)
    (by
      let D := padicCompletedChangedUniformizerFixedField p u n
      let M := padicCompletedStandardChangedCompositum p u n
      let : NontriviallyNormedField D :=
        finiteExtensionSpectralNormedField ℚ_[p] D
      let : ValuativeRel D :=
        finiteExtensionSpectralValuativeRel ℚ_[p] D
      let : IsNonarchimedeanLocalField D :=
        finiteExtensionSpectralIsNonarchimedeanLocalField ℚ_[p] D
      let : NontriviallyNormedField M :=
        finiteExtensionSpectralNormedField ℚ_[p] M
      let : ValuativeRel M :=
        finiteExtensionSpectralValuativeRel ℚ_[p] M
      let : IsNonarchimedeanLocalField M :=
        finiteExtensionSpectralIsNonarchimedeanLocalField ℚ_[p] M
      apply neg_ne_zero.mpr
      exact
        (padicCompletedChangedUniformizerPrimeElement_isUniformizer_in_changedField_and_compositum
          p u n).1.ne_zero)

/-- The underlying field element of the negative changed prime unit is
`-theta`. -/
@[simp]
theorem padicCompletedChangedUniformizerNegativePrimeUnit_coe
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (u : (padicLocalField p).valuationSubringˣ) :
    (padicCompletedChangedUniformizerNegativePrimeUnit p n u :
      padicCompletedChangedUniformizerFixedField p u n) =
      -padicCompletedChangedUniformizerPrimeElement p u n :=
  rfl

/-- The field-unit norm of the negative changed prime is the actual
changed base uniformizer. -/
theorem padicCompletedChangedUniformizerNegativePrimeUnit_norm
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (u : (padicLocalField p).valuationSubringˣ) :
    normUnits ℚ_[p]
        (padicCompletedChangedUniformizerFixedField p u n)
        (padicCompletedChangedUniformizerNegativePrimeUnit p n u) =
      standardLubinTateChangedUniformizerUnit
        (padicMultiplicativeLubinTateSeries_isUniformizer p) u := by
  apply Units.ext
  simpa only [normUnits_apply_coe,
    padicCompletedChangedUniformizerNegativePrimeUnit_coe] using
    (padicCompletedChangedUniformizer_norm_neg_primeElement p u n).trans
      (standardLubinTateChangedUniformizerUnit_coe
        (padicMultiplicativeLubinTateSeries_isUniformizer p) u).symm

/-- The negative changed prime has normalized additive value `-1` in its
completed fixed field. -/
theorem padicCompletedChangedUniformizerNegativePrimeUnit_valuationMap
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (u : (padicLocalField p).valuationSubringˣ) :
    let D := padicCompletedChangedUniformizerFixedField p u n
    letI : NontriviallyNormedField D :=
      finiteExtensionSpectralNormedField ℚ_[p] D
    letI : ValuativeRel D :=
      finiteExtensionSpectralValuativeRel ℚ_[p] D
    letI : IsNonarchimedeanLocalField D :=
      finiteExtensionSpectralIsNonarchimedeanLocalField ℚ_[p] D
    IsNonarchimedeanLocalField.valuationMap D
        (Additive.ofMul
          (padicCompletedChangedUniformizerNegativePrimeUnit p n u)) =
      -1 := by
  let D := padicCompletedChangedUniformizerFixedField p u n
  let M := padicCompletedStandardChangedCompositum p u n
  let : NontriviallyNormedField D :=
    finiteExtensionSpectralNormedField ℚ_[p] D
  let : ValuativeRel D :=
    finiteExtensionSpectralValuativeRel ℚ_[p] D
  let : IsNonarchimedeanLocalField D :=
    finiteExtensionSpectralIsNonarchimedeanLocalField ℚ_[p] D
  let : NontriviallyNormedField M :=
    finiteExtensionSpectralNormedField ℚ_[p] M
  let : ValuativeRel M :=
    finiteExtensionSpectralValuativeRel ℚ_[p] M
  let : IsNonarchimedeanLocalField M :=
    finiteExtensionSpectralIsNonarchimedeanLocalField ℚ_[p] M
  obtain ⟨htheta, _⟩ :=
    padicCompletedChangedUniformizerPrimeElement_isUniformizer_in_changedField_and_compositum
      p u n
  have hnegative :
      (localCompleteDVF D).valuation.IsUniformizer
        (-padicCompletedChangedUniformizerPrimeElement p u n : D) := by
    simpa only [Valuation.IsUniformizer.iff,
      (localCompleteDVF D).valuation.map_neg] using htheta
  let negativeInteger : (localCompleteDVF D).valuationSubring :=
    ⟨-padicCompletedChangedUniformizerPrimeElement p u n,
      hnegative.val_lt_one.le⟩
  have hunit :
      padicCompletedChangedUniformizerNegativePrimeUnit p n u =
        IsNonarchimedeanLocalField.uniformizerFieldUnit
          D negativeInteger hnegative := by
    apply Units.ext
    rfl
  rw [hunit]
  exact
    IsNonarchimedeanLocalField.valuationMap_uniformizerFieldUnit
      D negativeInteger hnegative

/-- The actual relative local Artin image of the negative changed prime is
the explicit inverse-coefficient-Frobenius candidate. -/
theorem
    padicCompletedChangedUniformizerRelativeArtin_negativePrime
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (u : (padicLocalField p).valuationSubringˣ) :
    let D := padicCompletedChangedUniformizerFixedField p u n
    let M := padicCompletedStandardChangedCompositum p u n
    letI : NontriviallyNormedField D :=
      finiteExtensionSpectralNormedField ℚ_[p] D
    letI : ValuativeRel D :=
      finiteExtensionSpectralValuativeRel ℚ_[p] D
    letI : IsNonarchimedeanLocalField D :=
      finiteExtensionSpectralIsNonarchimedeanLocalField ℚ_[p] D
    letI : NontriviallyNormedField M :=
      finiteExtensionSpectralNormedField ℚ_[p] M
    letI : ValuativeRel M :=
      finiteExtensionSpectralValuativeRel ℚ_[p] M
    letI : IsNonarchimedeanLocalField M :=
      finiteExtensionSpectralIsNonarchimedeanLocalField ℚ_[p] M
    letI :
        Valuation.HasExtension (ValuativeRel.valuation D)
          (ValuativeRel.valuation M) :=
      finiteExtensionSpectralValuation_hasExtension_of_tower ℚ_[p] D M
    letI :
        IsNonarchimedeanLocalField.IsUnramifiedValuedExtension D M :=
      padicCompletedStandardChangedCompositum_isUnramifiedValuedExtension
        p u n
    abelianLocalArtinMonoidHom D M
        (padicCompletedChangedUniformizerNegativePrimeUnit p n u) =
      padicCompletedChangedUniformizerRelativeArtinCandidate p u n := by
  let D := padicCompletedChangedUniformizerFixedField p u n
  let M := padicCompletedStandardChangedCompositum p u n
  let : NontriviallyNormedField D :=
    finiteExtensionSpectralNormedField ℚ_[p] D
  let : ValuativeRel D :=
    finiteExtensionSpectralValuativeRel ℚ_[p] D
  let : IsNonarchimedeanLocalField D :=
    finiteExtensionSpectralIsNonarchimedeanLocalField ℚ_[p] D
  let : NontriviallyNormedField M :=
    finiteExtensionSpectralNormedField ℚ_[p] M
  let : ValuativeRel M :=
    finiteExtensionSpectralValuativeRel ℚ_[p] M
  let : IsNonarchimedeanLocalField M :=
    finiteExtensionSpectralIsNonarchimedeanLocalField ℚ_[p] M
  let :
      Valuation.HasExtension (ValuativeRel.valuation D)
        (ValuativeRel.valuation M) :=
    finiteExtensionSpectralValuation_hasExtension_of_tower ℚ_[p] D M
  let :
      IsNonarchimedeanLocalField.IsUnramifiedValuedExtension D M :=
    padicCompletedStandardChangedCompositum_isUnramifiedValuedExtension
      p u n
  calc
    abelianLocalArtinMonoidHom D M
        (padicCompletedChangedUniformizerNegativePrimeUnit p n u) =
        (arithmeticFrobeniusOfUnramifiedValuation D M) ^
          IsNonarchimedeanLocalField.valuationMap D
            (Additive.ofMul
              (padicCompletedChangedUniformizerNegativePrimeUnit p n u)) :=
      abelianLocalArtinMonoidHom_eq_frobenius_zpow D M _
    _ = (arithmeticFrobeniusOfUnramifiedValuation D M) ^ (-1 : ℤ) := by
      rw [padicCompletedChangedUniformizerNegativePrimeUnit_valuationMap]
    _ = (arithmeticFrobeniusOfUnramifiedValuation D M)⁻¹ := by
      rw [zpow_neg_one]
    _ = padicCompletedChangedUniformizerRelativeArtinCandidate p u n :=
      (padicCompletedChangedUniformizerRelativeArtinCandidate_eq_inverseArithmeticFrobenius
        p u n).symm

section PadicStandardLevelRestriction

private theorem padicArtinStandardLevel_normal
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    Normal ℚ_[p]
      (standardLubinTateLevelField
        (padicMultiplicativeLubinTateSeries_isUniformizer p) n) :=
  (standardLubinTateLevelField_isGalois (F := padicLocalField p)
    (padicMultiplicativeLubinTateSeries_isUniformizer p) n).to_normal

attribute [local instance] padicArtinStandardLevel_normal

/-- Restricting the relative changed-prime Artin candidate to the standard
multiplicative level gives the direct finite unit-parameter automorphism. -/
theorem
    padicCompletedChangedUniformizerRelativeArtinCandidate_restrict_standardLevel
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (u : (padicLocalField p).valuationSubringˣ) :
    let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
    let T := standardLubinTateLevelField hπ n
    let M := padicCompletedStandardChangedCompositum p u n
    letI : Algebra T M :=
      (padicStandardLevelToCompletedChangedCompositum
        p u n).toRingHom.toAlgebra
    letI : IsScalarTower ℚ_[p] T M :=
      IsScalarTower.of_algebraMap_eq'
        (padicStandardLevelToCompletedChangedCompositum p u n).comp_algebraMap.symm
    ((AlgEquiv.restrictNormalHom T).comp
        (AlgEquiv.restrictScalarsHom ℚ_[p]))
        (padicCompletedChangedUniformizerRelativeArtinCandidate
          p u n) =
      standardLubinTateUnitParameterEquivGal
        (padicLocalField p) hπ n
        (standardLubinTateUnitParameterClass
          (padicLocalField p) n u) := by
  let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
  let T := standardLubinTateLevelField hπ n
  let M := padicCompletedStandardChangedCompositum p u n
  let : Algebra T M :=
    (padicStandardLevelToCompletedChangedCompositum
      p u n).toRingHom.toAlgebra
  let : IsScalarTower ℚ_[p] T M :=
    IsScalarTower.of_algebraMap_eq'
      (padicStandardLevelToCompletedChangedCompositum p u n).comp_algebraMap.symm
  apply AlgEquiv.ext
  intro x
  apply (algebraMap T M).injective
  rw [MonoidHom.comp_apply, AlgEquiv.restrictScalarsHom_apply]
  change
    algebraMap T M
        (AlgEquiv.restrictNormal
          ((AlgEquiv.restrictScalarsHom ℚ_[p])
            (padicCompletedChangedUniformizerRelativeArtinCandidate p u n)) T x) =
      algebraMap T M
        (standardLubinTateUnitParameterEquivGal
          (padicLocalField p) hπ n
          (standardLubinTateUnitParameterClass
            (padicLocalField p) n u) x)
  rw [AlgEquiv.restrictNormal_commutes]
  change
    padicCompletedChangedUniformizerRelativeArtinCandidate p u n
        (padicStandardLevelToCompletedChangedCompositum p u n x) =
      padicStandardLevelToCompletedChangedCompositum p u n
        (standardLubinTateUnitParameterEquivGal
          (padicLocalField p) hπ n
          (standardLubinTateUnitParameterClass
            (padicLocalField p) n u) x)
  rw [
    padicCompletedChangedUniformizerRelativeArtinCandidate_apply,
    padicCompletedChangedUniformizerArtinCandidate_standardLevel]
  exact congrArg
    (fun σ : Gal(T / ℚ_[p]) =>
      padicStandardLevelToCompletedChangedCompositum p u n (σ x))
    (standardLubinTateUnitParameterEquivGal_apply (padicLocalField p) hπ n
      (standardLubinTateUnitParameterClass (padicLocalField p) n u)).symm

end PadicStandardLevelRestriction

/-- The chosen p-adic Lubin--Tate uniformizer is an actual norm from every
finite multiplicative level, hence its actual local Artin image is trivial. -/
theorem padicMultiplicativeAbelianLocalArtin_baseUniformizer
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
    let L := standardLubinTateLevelField hπ n
    letI : FiniteDimensional ℚ_[p] L :=
      standardLubinTateLevelField_finiteDimensional hπ n
    letI : IsAbelianGalois ℚ_[p] L :=
      standardLubinTateLevelField_isAbelianGalois
        (padicLocalField p) hπ n
    abelianLocalArtinMonoidHom ℚ_[p] L
        (standardLubinTateBaseUniformizerUnit hπ) =
      1 := by
  let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
  let L := standardLubinTateLevelField hπ n
  let : FiniteDimensional ℚ_[p] L :=
    standardLubinTateLevelField_finiteDimensional hπ n
  let : IsAbelianGalois ℚ_[p] L :=
    standardLubinTateLevelField_isAbelianGalois
      (padicLocalField p) hπ n
  have hnorm :=
    standardLubinTateBaseUniformizerUnit_mem_normSubgroup hπ n
  change
    standardLubinTateBaseUniformizerUnit hπ ∈
      localNormSubgroup ℚ_[p] L at hnorm
  rw [← abelianLocalArtinMonoidHom_ker, MonoidHom.mem_ker] at hnorm
  exact hnorm

/-- The actual Artin value of an arbitrary p-adic field unit is already
determined by its valuation-zero part.  This is an equality of the actual
maps: the discarded uniformizer power is an explicit norm from the standard
Lubin--Tate level. -/
theorem padicMultiplicativeAbelianLocalArtin_eq_uniformizerUnitPart
    (p : ℕ) [Fact p.Prime] (n : ℕ) (x : ℚ_[p]ˣ) :
    let F := padicLocalField p
    let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
    let L := standardLubinTateLevelField hπ n
    letI : FiniteDimensional ℚ_[p] L :=
      standardLubinTateLevelField_finiteDimensional hπ n
    letI : IsAbelianGalois ℚ_[p] L :=
      standardLubinTateLevelField_isAbelianGalois F hπ n
    abelianLocalArtinMonoidHom ℚ_[p] L x =
      abelianLocalArtinMonoidHom ℚ_[p] L
        (standardLubinTateUnitFactorFieldUnit F
          (CompleteDVF.higherPrincipalUnitGroup.fieldUnitUniformizerUnitPart
            F.toCompleteDVF hπ x)) := by
  let F := padicLocalField p
  let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
  let L := standardLubinTateLevelField hπ n
  let : FiniteDimensional ℚ_[p] L :=
    standardLubinTateLevelField_finiteDimensional hπ n
  let : IsAbelianGalois ℚ_[p] L :=
    standardLubinTateLevelField_isAbelianGalois F hπ n
  let φ := abelianLocalArtinMonoidHom ℚ_[p] L
  let ϖ : ℚ_[p]ˣ := standardLubinTateBaseUniformizerUnit hπ
  let u : F.valuationSubringˣ :=
    CompleteDVF.higherPrincipalUnitGroup.fieldUnitUniformizerUnitPart
      F.toCompleteDVF hπ x
  let e : ℤ :=
    CompleteDVF.uniformizerValueExponent F.toCompleteDVF hπ x
  have hϖone : φ ϖ = 1 := by
    simpa only [φ, ϖ] using
      padicMultiplicativeAbelianLocalArtin_baseUniformizer p n
  have huField :
      standardLubinTateUnitFactorFieldUnit F u =
        x * ϖ ^ (-e) := by
    apply Units.ext
    simpa only [
      u, e, ϖ,
      standardLubinTateUnitFactorFieldUnit_coe,
      CompleteDVF.coe_valuationSubringUnitsToFieldUnits_apply,
      CompleteDVF.higherPrincipalUnitGroup.coe_valuationSubringUnitFieldUnitHom_apply,
      standardLubinTateBaseUniformizerUnit] using
      congrArg (fun z : ℚ_[p]ˣ => (z : ℚ_[p]))
        (CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom_fieldUnitUniformizerUnitPart
          F.toCompleteDVF hπ x)
  calc
    φ x = φ x * φ ϖ ^ (-e) := by
      rw [hϖone, one_zpow, mul_one]
    _ = φ (x * ϖ ^ (-e)) := by
      rw [map_mul, map_zpow]
    _ = φ (standardLubinTateUnitFactorFieldUnit F u) := by
      rw [huField]

/-- Multiplying the chosen uniformizer by a p-adic valuation-ring unit does
not change the actual local Artin value of the unit factor. -/
theorem padicMultiplicativeAbelianLocalArtin_changedUniformizer
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (u : (padicLocalField p).valuationSubringˣ) :
    let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
    let L := standardLubinTateLevelField hπ n
    letI : FiniteDimensional ℚ_[p] L :=
      standardLubinTateLevelField_finiteDimensional hπ n
    letI : IsAbelianGalois ℚ_[p] L :=
      standardLubinTateLevelField_isAbelianGalois
        (padicLocalField p) hπ n
    abelianLocalArtinMonoidHom ℚ_[p] L
        (standardLubinTateChangedUniformizerUnit hπ u) =
      abelianLocalArtinMonoidHom ℚ_[p] L
        (standardLubinTateUnitFactorFieldUnit (padicLocalField p) u) := by
  let F := padicLocalField p
  let π : F.valuationSubring :=
    padicIntEquivValuationSubring p (p : ℤ_[p])
  let hπ : F.toCompleteDVF.valuation.IsUniformizer (π : ℚ_[p]) :=
    padicMultiplicativeLubinTateSeries_isUniformizer p
  let L := standardLubinTateLevelField (F := F) (π := π) hπ n
  let : FiniteDimensional ℚ_[p] L :=
    standardLubinTateLevelField_finiteDimensional hπ n
  let : IsAbelianGalois ℚ_[p] L :=
    standardLubinTateLevelField_isAbelianGalois
      F hπ n
  have hchanged :
      standardLubinTateChangedUniformizerUnit hπ u =
        standardLubinTateUnitFactorFieldUnit F u *
          standardLubinTateBaseUniformizerUnit hπ :=
    standardLubinTateChangedUniformizerUnit_eq_unit_mul (F := F) hπ u
  calc
    abelianLocalArtinMonoidHom ℚ_[p] L
        (standardLubinTateChangedUniformizerUnit hπ u) =
        abelianLocalArtinMonoidHom ℚ_[p] L
          (standardLubinTateUnitFactorFieldUnit F u *
            standardLubinTateBaseUniformizerUnit hπ) :=
      congrArg (abelianLocalArtinMonoidHom ℚ_[p] L) hchanged
    _ = abelianLocalArtinMonoidHom ℚ_[p] L
          (standardLubinTateUnitFactorFieldUnit F u) := by
      rw [map_mul, padicMultiplicativeAbelianLocalArtin_baseUniformizer p n,
        mul_one]

/-- On every finite multiplicative Lubin--Tate level, the actual local
Artin image of a p-adic valuation-ring unit is the direct finite
unit-parameter automorphism.

This is obtained from the genuine changed-uniformizer extension: the
negative changed prime has norm `u p`, its relative Artin image is the
inverse arithmetic Frobenius, and norm--restriction carries that image to
the direct `u`-action on the standard level. -/
theorem padicMultiplicativeAbelianLocalArtin_eq_unitParameter
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (u : (padicLocalField p).valuationSubringˣ) :
    let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
    let T := standardLubinTateLevelField hπ n
    letI : FiniteDimensional ℚ_[p] T :=
      standardLubinTateLevelField_finiteDimensional hπ n
    letI : IsAbelianGalois ℚ_[p] T :=
      standardLubinTateLevelField_isAbelianGalois
        (padicLocalField p) hπ n
    abelianLocalArtinMonoidHom ℚ_[p] T
        (standardLubinTateUnitFactorFieldUnit (padicLocalField p) u) =
      standardLubinTateUnitParameterEquivGal
        (padicLocalField p) hπ n
        (standardLubinTateUnitParameterClass
          (padicLocalField p) n u) := by
  let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
  let T := standardLubinTateLevelField hπ n
  let D := padicCompletedChangedUniformizerFixedField p u n
  let M := padicCompletedStandardChangedCompositum p u n
  let : FiniteDimensional ℚ_[p] T :=
    standardLubinTateLevelField_finiteDimensional hπ n
  let : IsAbelianGalois ℚ_[p] T :=
    standardLubinTateLevelField_isAbelianGalois
      (padicLocalField p) hπ n
  let : Algebra T M :=
    (padicStandardLevelToCompletedChangedCompositum
      p u n).toRingHom.toAlgebra
  let : IsScalarTower ℚ_[p] T M :=
    IsScalarTower.of_algebraMap_eq'
      (padicStandardLevelToCompletedChangedCompositum p u n).comp_algebraMap.symm
  let : FiniteDimensional D M :=
    FiniteDimensional.right ℚ_[p] D M
  let : NontriviallyNormedField D :=
    finiteExtensionSpectralNormedField ℚ_[p] D
  let : ValuativeRel D :=
    finiteExtensionSpectralValuativeRel ℚ_[p] D
  let : IsNonarchimedeanLocalField D :=
    finiteExtensionSpectralIsNonarchimedeanLocalField ℚ_[p] D
  let : NontriviallyNormedField M :=
    finiteExtensionSpectralNormedField ℚ_[p] M
  let : ValuativeRel M :=
    finiteExtensionSpectralValuativeRel ℚ_[p] M
  let : IsNonarchimedeanLocalField M :=
    finiteExtensionSpectralIsNonarchimedeanLocalField ℚ_[p] M
  let :
      Valuation.HasExtension (ValuativeRel.valuation ℚ_[p])
        (ValuativeRel.valuation D) :=
    finiteExtensionSpectralValuation_hasExtension ℚ_[p] D
  let :
      Valuation.HasExtension (ValuativeRel.valuation D)
        (ValuativeRel.valuation M) :=
    finiteExtensionSpectralValuation_hasExtension_of_tower
      ℚ_[p] D M
  let :
      IsNonarchimedeanLocalField.IsUnramifiedValuedExtension D M :=
    padicCompletedStandardChangedCompositum_isUnramifiedValuedExtension
      p u n
  have hnormRestriction :=
    DFunLike.congr_fun
      (abelianLocalArtinMonoidHom_norm_restriction
        ℚ_[p] D T M)
      (padicCompletedChangedUniformizerNegativePrimeUnit p n u)
  have hrelative :
      abelianLocalArtinMonoidHom D M
          (padicCompletedChangedUniformizerNegativePrimeUnit p n u) =
        padicCompletedChangedUniformizerRelativeArtinCandidate p u n :=
    padicCompletedChangedUniformizerRelativeArtin_negativePrime p n u
  have hrestrict :
      ((AlgEquiv.restrictNormalHom T).comp
          (AlgEquiv.restrictScalarsHom ℚ_[p]))
          (padicCompletedChangedUniformizerRelativeArtinCandidate p u n) =
        standardLubinTateUnitParameterEquivGal
          (padicLocalField p) hπ n
          (standardLubinTateUnitParameterClass
            (padicLocalField p) n u) :=
    padicCompletedChangedUniformizerRelativeArtinCandidate_restrict_standardLevel
      p n u
  have hnorm :
      normUnits ℚ_[p] D
          (padicCompletedChangedUniformizerNegativePrimeUnit p n u) =
        standardLubinTateChangedUniformizerUnit hπ u :=
    padicCompletedChangedUniformizerNegativePrimeUnit_norm p n u
  have hchanged :
      abelianLocalArtinMonoidHom ℚ_[p] T
          (standardLubinTateChangedUniformizerUnit hπ u) =
        abelianLocalArtinMonoidHom ℚ_[p] T
          (standardLubinTateUnitFactorFieldUnit (padicLocalField p) u) :=
    padicMultiplicativeAbelianLocalArtin_changedUniformizer p n u
  have h :
      standardLubinTateUnitParameterEquivGal
          (padicLocalField p) hπ n
          (standardLubinTateUnitParameterClass
            (padicLocalField p) n u) =
        abelianLocalArtinMonoidHom ℚ_[p] T
          (standardLubinTateUnitFactorFieldUnit (padicLocalField p) u) := by
    simpa only [MonoidHom.comp_apply, hrelative, hrestrict, hnorm, hchanged] using
      hnormRestriction
  exact h.symm

/-- The actual local Artin action of a p-adic valuation-ring unit on the
genuine multiplicative primitive point is exponentiation by the direct
unit parameter. -/
theorem padicMultiplicativeAbelianLocalArtin_primitiveRoot
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (u : (padicLocalField p).valuationSubringˣ) :
    let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
    let T := standardLubinTateLevelField hπ n
    letI : FiniteDimensional ℚ_[p] T :=
      standardLubinTateLevelField_finiteDimensional hπ n
    letI : IsAbelianGalois ℚ_[p] T :=
      standardLubinTateLevelField_isAbelianGalois
        (padicLocalField p) hπ n
    abelianLocalArtinMonoidHom ℚ_[p] T
        (standardLubinTateUnitFactorFieldUnit (padicLocalField p) u)
        (padicMultiplicativePrimitiveRoot p n) =
      (padicMultiplicativePrimitiveRoot p n) ^
        (PadicInt.toZModPow (n + 1)
          ((padicIntEquivValuationSubring p).symm
            (u : (padicLocalField p).valuationSubring))).val := by
  let F := padicLocalField p
  let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
  let T := standardLubinTateLevelField hπ n
  let : FiniteDimensional ℚ_[p] T :=
    standardLubinTateLevelField_finiteDimensional hπ n
  let : IsAbelianGalois ℚ_[p] T :=
    standardLubinTateLevelField_isAbelianGalois F hπ n
  have hArtin :
      abelianLocalArtinMonoidHom ℚ_[p] T
          (standardLubinTateUnitFactorFieldUnit F u) =
        standardLubinTateUnitParameterEquivGal F hπ n
          (standardLubinTateUnitParameterClass F n u) :=
    padicMultiplicativeAbelianLocalArtin_eq_unitParameter p n u
  exact
    (congrArg (fun σ : Gal(T / ℚ_[p]) =>
      σ (padicMultiplicativePrimitiveRoot p n)) hArtin).trans
      (padicMultiplicativePrimitiveRoot_unitParameterGaloisAction p n u)

/-- A p-adic valuation-ring unit invisible at level `n` has trivial image
under the actual abelian local Artin map of the multiplicative Lubin--Tate
level.

The source is the changed-uniformizer equivalence: it proves that the field
unit is an actual norm, rather than merely postulating membership in the
Artin kernel. -/
theorem
    padicMultiplicativeAbelianLocalArtin_eq_one_of_mem_higherPrincipalUnitGroup
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (u : (padicLocalField p).valuationSubringˣ)
    (hu : u ∈
      CompleteDVF.higherPrincipalUnitGroup
        (padicLocalField p).toCompleteDVF (n + 1)) :
    let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
    let L := standardLubinTateLevelField hπ n
    letI : FiniteDimensional ℚ_[p] L :=
      standardLubinTateLevelField_finiteDimensional hπ n
    letI : IsAbelianGalois ℚ_[p] L :=
      standardLubinTateLevelField_isAbelianGalois
        (padicLocalField p) hπ n
    abelianLocalArtinMonoidHom ℚ_[p] L
        (standardLubinTateUnitFactorFieldUnit (padicLocalField p) u) =
      1 := by
  let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
  let L := standardLubinTateLevelField hπ n
  let : FiniteDimensional ℚ_[p] L :=
    standardLubinTateLevelField_finiteDimensional hπ n
  let : IsAbelianGalois ℚ_[p] L :=
    standardLubinTateLevelField_isAbelianGalois
      (padicLocalField p) hπ n
  have hnorm :=
    standardLubinTateUnitFactorFieldUnit_mem_standardNormSubgroup_of_mem_higher
      hπ u n hu
  change
    standardLubinTateUnitFactorFieldUnit (padicLocalField p) u ∈
      localNormSubgroup ℚ_[p] L at hnorm
  rw [← abelianLocalArtinMonoidHom_ker, MonoidHom.mem_ker] at hnorm
  exact hnorm

/-- The actual local Artin homomorphism on p-adic valuation-ring units,
descended through the finite parameter quotient
`O_pˣ / U_p^(n + 1)`. -/
noncomputable def padicMultiplicativeArtinUnitParameterHom
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    standardLubinTateUnitParameter (padicLocalField p) n →*
      Gal((standardLubinTateLevelField
        (padicMultiplicativeLubinTateSeries_isUniformizer p) n) / ℚ_[p]) := by
  let F := padicLocalField p
  let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
  let L := standardLubinTateLevelField hπ n
  letI : FiniteDimensional ℚ_[p] L :=
    standardLubinTateLevelField_finiteDimensional hπ n
  letI : IsAbelianGalois ℚ_[p] L :=
    standardLubinTateLevelField_isAbelianGalois F hπ n
  exact
    QuotientGroup.lift
      (CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF (n + 1))
      ((abelianLocalArtinMonoidHom ℚ_[p] L).comp
        (CompleteDVF.valuationSubringUnitsToFieldUnits F.toCompleteDVF))
      (fun u hu => by
        change
          abelianLocalArtinMonoidHom ℚ_[p] L
              (standardLubinTateUnitFactorFieldUnit F u) =
            1
        exact
          padicMultiplicativeAbelianLocalArtin_eq_one_of_mem_higherPrincipalUnitGroup
            p n u hu)

/-- Evaluating the descended actual Artin homomorphism on a parameter class
recovers the actual Artin value of its valuation-ring-unit representative. -/
@[simp]
theorem padicMultiplicativeArtinUnitParameterHom_apply_class
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (u : (padicLocalField p).valuationSubringˣ) :
    let F := padicLocalField p
    let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
    let L := standardLubinTateLevelField hπ n
    letI : FiniteDimensional ℚ_[p] L :=
      standardLubinTateLevelField_finiteDimensional hπ n
    letI : IsAbelianGalois ℚ_[p] L :=
      standardLubinTateLevelField_isAbelianGalois F hπ n
    padicMultiplicativeArtinUnitParameterHom p n
        (standardLubinTateUnitParameterClass F n u) =
      abelianLocalArtinMonoidHom ℚ_[p] L
        (standardLubinTateUnitFactorFieldUnit F u) := by
  dsimp only
  rfl

/-- The actual Artin homomorphism on finite p-adic unit parameters is
surjective.  Given an Artin preimage in `ℚ_pˣ`, remove its uniformizer power;
that power has trivial Artin image because the chosen uniformizer is an
actual norm from the Lubin--Tate level. -/
theorem padicMultiplicativeArtinUnitParameterHom_surjective
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    Function.Surjective (padicMultiplicativeArtinUnitParameterHom p n) := by
  let F := padicLocalField p
  let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
  let L := standardLubinTateLevelField hπ n
  let : FiniteDimensional ℚ_[p] L :=
    standardLubinTateLevelField_finiteDimensional hπ n
  let : IsAbelianGalois ℚ_[p] L :=
    standardLubinTateLevelField_isAbelianGalois F hπ n
  let φ := abelianLocalArtinMonoidHom ℚ_[p] L
  intro σ
  obtain ⟨x, hx⟩ :=
    abelianLocalArtinMonoidHom_surjective ℚ_[p] L σ
  let u : F.valuationSubringˣ :=
    CompleteDVF.higherPrincipalUnitGroup.fieldUnitUniformizerUnitPart
      F.toCompleteDVF hπ x
  refine
    ⟨standardLubinTateUnitParameterClass F n u, ?_⟩
  rw [padicMultiplicativeArtinUnitParameterHom_apply_class]
  calc
    φ (standardLubinTateUnitFactorFieldUnit F u) =
        φ x := by
      simpa only [φ, u] using
        (padicMultiplicativeAbelianLocalArtin_eq_uniformizerUnitPart
          p n x).symm
    _ = σ := hx

/-- The finite unit-parameter quotient is multiplicatively equivalent to the
actual Galois group through the actual local Artin map.

This equivalence is constructed from the descended Artin map itself.  It
does not identify its orientation with the independently constructed
explicit Lubin--Tate equivalence. -/
noncomputable def padicMultiplicativeArtinUnitParameterEquiv
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    standardLubinTateUnitParameter (padicLocalField p) n ≃*
      Gal((standardLubinTateLevelField
        (padicMultiplicativeLubinTateSeries_isUniformizer p) n) / ℚ_[p]) := by
  let F := padicLocalField p
  let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
  let L := standardLubinTateLevelField hπ n
  letI : FiniteDimensional ℚ_[p] L :=
    standardLubinTateLevelField_finiteDimensional hπ n
  letI : IsAbelianGalois ℚ_[p] L :=
    standardLubinTateLevelField_isAbelianGalois F hπ n
  refine
    MulEquiv.ofBijective
      (padicMultiplicativeArtinUnitParameterHom p n) ?_
  apply
    (Nat.bijective_iff_surjective_and_card
      (padicMultiplicativeArtinUnitParameterHom p n)).2
  refine
    ⟨padicMultiplicativeArtinUnitParameterHom_surjective p n, ?_⟩
  rw [
    standardLubinTateUnitParameter_natCard F n,
    ← standardLubinTateLevelField_finrank hπ n,
    ← standardLubinTateLevelField_natCard_gal hπ n]

/-- The actual Artin equivalence evaluates on a finite unit-parameter class
as the actual local Artin automorphism of its representative. -/
@[simp]
theorem padicMultiplicativeArtinUnitParameterEquiv_apply_class
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (u : (padicLocalField p).valuationSubringˣ) :
    let F := padicLocalField p
    let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
    let L := standardLubinTateLevelField hπ n
    letI : FiniteDimensional ℚ_[p] L :=
      standardLubinTateLevelField_finiteDimensional hπ n
    letI : IsAbelianGalois ℚ_[p] L :=
      standardLubinTateLevelField_isAbelianGalois F hπ n
    padicMultiplicativeArtinUnitParameterEquiv p n
        (standardLubinTateUnitParameterClass F n u) =
      abelianLocalArtinMonoidHom ℚ_[p] L
        (standardLubinTateUnitFactorFieldUnit F u) := by
  dsimp only
  rfl

/-- The subgroup of `ℚ_pˣ` generated by the chosen uniformizer and the
valuation-ring units in `U^(n + 1)`. -/
noncomputable def
    padicMultiplicativeUniformizerHigherPrincipalUnitSubgroup
    (p : ℕ) [Fact p.Prime] (n : ℕ) : Subgroup ℚ_[p]ˣ :=
  let F := padicLocalField p
  let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
  Subgroup.zpowers (standardLubinTateBaseUniformizerUnit hπ) ⊔
    (CompleteDVF.higherPrincipalUnitGroup
      F.toCompleteDVF (n + 1)).map
        (CompleteDVF.valuationSubringUnitsToFieldUnits F.toCompleteDVF)

/-- The kernel of the actual local Artin map for the multiplicative p-adic
level is exactly the subgroup generated by the chosen uniformizer and
`U^(n + 1)`.

The reverse containment uses the actual-Artin equivalence on finite unit
parameters, not a postulated norm-subgroup formula. -/
theorem padicMultiplicativeAbelianLocalArtin_ker
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    let F := padicLocalField p
    let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
    let L := standardLubinTateLevelField hπ n
    letI : FiniteDimensional ℚ_[p] L :=
      standardLubinTateLevelField_finiteDimensional hπ n
    letI : IsAbelianGalois ℚ_[p] L :=
      standardLubinTateLevelField_isAbelianGalois F hπ n
    (abelianLocalArtinMonoidHom ℚ_[p] L).ker =
      padicMultiplicativeUniformizerHigherPrincipalUnitSubgroup p n := by
  let F := padicLocalField p
  let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
  let L := standardLubinTateLevelField hπ n
  let : FiniteDimensional ℚ_[p] L :=
    standardLubinTateLevelField_finiteDimensional hπ n
  let : IsAbelianGalois ℚ_[p] L :=
    standardLubinTateLevelField_isAbelianGalois F hπ n
  let φ := abelianLocalArtinMonoidHom ℚ_[p] L
  let ϖ : ℚ_[p]ˣ := standardLubinTateBaseUniformizerUnit hπ
  let H : Subgroup F.valuationSubringˣ :=
    CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF (n + 1)
  let j : F.valuationSubringˣ →* ℚ_[p]ˣ :=
    CompleteDVF.valuationSubringUnitsToFieldUnits F.toCompleteDVF
  change φ.ker = Subgroup.zpowers ϖ ⊔ H.map j
  apply le_antisymm
  · intro x hx
    let u : F.valuationSubringˣ :=
      CompleteDVF.higherPrincipalUnitGroup.fieldUnitUniformizerUnitPart
        F.toCompleteDVF hπ x
    let e : ℤ :=
      CompleteDVF.uniformizerValueExponent F.toCompleteDVF hπ x
    have hxArtin : φ x = 1 :=
      MonoidHom.mem_ker.mp hx
    have hreduce :
        φ x = φ (standardLubinTateUnitFactorFieldUnit F u) := by
      simpa only [φ, u] using
        padicMultiplicativeAbelianLocalArtin_eq_uniformizerUnitPart
          p n x
    have huArtin :
        φ (standardLubinTateUnitFactorFieldUnit F u) = 1 :=
      hreduce.symm.trans hxArtin
    have huClass :
        standardLubinTateUnitParameterClass F n u = 1 := by
      apply (padicMultiplicativeArtinUnitParameterEquiv p n).injective
      rw [
        padicMultiplicativeArtinUnitParameterEquiv_apply_class,
        map_one]
      exact huArtin
    have hu : u ∈ H := by
      exact
        (QuotientGroup.eq_one_iff (N := H) u).1 huClass
    have huMap : j u ∈ H.map j :=
      ⟨u, hu, rfl⟩
    have hunit :
        j u ∈ Subgroup.zpowers ϖ ⊔ H.map j :=
      (show H.map j ≤ Subgroup.zpowers ϖ ⊔ H.map j from le_sup_right)
        huMap
    have hpow :
        ϖ ^ e ∈ Subgroup.zpowers ϖ ⊔ H.map j :=
      (show Subgroup.zpowers ϖ ≤
          Subgroup.zpowers ϖ ⊔ H.map j from le_sup_left)
        (Subgroup.zpow_mem_zpowers ϖ e)
    have huField :
        j u = x * ϖ ^ (-e) := by
      apply Units.ext
      simpa only [
        j, u, e, ϖ,
        CompleteDVF.coe_valuationSubringUnitsToFieldUnits_apply,
        CompleteDVF.higherPrincipalUnitGroup.coe_valuationSubringUnitFieldUnitHom_apply,
        standardLubinTateBaseUniformizerUnit] using
        congrArg (fun z : ℚ_[p]ˣ => (z : ℚ_[p]))
          (CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom_fieldUnitUniformizerUnitPart
            F.toCompleteDVF hπ x)
    have hxDecomposition :
        x = j u * ϖ ^ e := by
      rw [huField]
      simp [mul_assoc]
    rw [hxDecomposition]
    exact
      (Subgroup.zpowers ϖ ⊔ H.map j).mul_mem hunit hpow
  · apply sup_le
    · apply Subgroup.zpowers_le_of_mem
      rw [MonoidHom.mem_ker]
      simpa only [φ, ϖ] using
        padicMultiplicativeAbelianLocalArtin_baseUniformizer p n
    · rintro _ ⟨u, hu, rfl⟩
      rw [MonoidHom.mem_ker]
      change
        abelianLocalArtinMonoidHom ℚ_[p] L
            (standardLubinTateUnitFactorFieldUnit F u) =
          1
      exact
        padicMultiplicativeAbelianLocalArtin_eq_one_of_mem_higherPrincipalUnitGroup
          p n u hu

/-- The actual norm subgroup of the multiplicative p-adic level is the
uniformizer subgroup times `U^(n + 1)`. -/
theorem
    padicMultiplicativeLocalNormSubgroup_eq_uniformizerHigherPrincipalUnitSubgroup
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    let F := padicLocalField p
    let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
    let L := standardLubinTateLevelField hπ n
    letI : FiniteDimensional ℚ_[p] L :=
      standardLubinTateLevelField_finiteDimensional hπ n
    letI : IsAbelianGalois ℚ_[p] L :=
      standardLubinTateLevelField_isAbelianGalois F hπ n
    localNormSubgroup ℚ_[p] L =
      padicMultiplicativeUniformizerHigherPrincipalUnitSubgroup p n := by
  let F := padicLocalField p
  let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
  let L := standardLubinTateLevelField hπ n
  let : FiniteDimensional ℚ_[p] L :=
    standardLubinTateLevelField_finiteDimensional hπ n
  let : IsAbelianGalois ℚ_[p] L :=
    standardLubinTateLevelField_isAbelianGalois F hπ n
  calc
    localNormSubgroup ℚ_[p] L =
        (abelianLocalArtinMonoidHom ℚ_[p] L).ker :=
      (abelianLocalArtinMonoidHom_ker ℚ_[p] L).symm
    _ = padicMultiplicativeUniformizerHigherPrincipalUnitSubgroup p n :=
      padicMultiplicativeAbelianLocalArtin_ker p n

/-- On `U^(n + 1)`, the actual local Artin map agrees with the inverse
finite Lubin--Tate unit-parameter automorphism. -/
theorem
    padicMultiplicativeAbelianLocalArtin_eq_unitParameter_of_mem_higherPrincipalUnitGroup
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (u : (padicLocalField p).valuationSubringˣ)
    (hu : u ∈
      CompleteDVF.higherPrincipalUnitGroup
        (padicLocalField p).toCompleteDVF (n + 1)) :
    let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
    let L := standardLubinTateLevelField hπ n
    letI : FiniteDimensional ℚ_[p] L :=
      standardLubinTateLevelField_finiteDimensional hπ n
    letI : IsAbelianGalois ℚ_[p] L :=
      standardLubinTateLevelField_isAbelianGalois
        (padicLocalField p) hπ n
    abelianLocalArtinMonoidHom ℚ_[p] L
        (standardLubinTateUnitFactorFieldUnit (padicLocalField p) u) =
      (standardLubinTateUnitParameterEquivGal
        (padicLocalField p) hπ n
        (standardLubinTateUnitParameterClass
          (padicLocalField p) n u))⁻¹ := by
  let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
  let L := standardLubinTateLevelField hπ n
  let : FiniteDimensional ℚ_[p] L :=
    standardLubinTateLevelField_finiteDimensional hπ n
  let : IsAbelianGalois ℚ_[p] L :=
    standardLubinTateLevelField_isAbelianGalois
      (padicLocalField p) hπ n
  have hArtin :
      abelianLocalArtinMonoidHom ℚ_[p] L
          (standardLubinTateUnitFactorFieldUnit (padicLocalField p) u) =
        1 :=
    padicMultiplicativeAbelianLocalArtin_eq_one_of_mem_higherPrincipalUnitGroup
      p n u hu
  have hParameter :
      standardLubinTateUnitParameterClass (padicLocalField p) n u = 1 := by
    exact
      (QuotientGroup.eq_one_iff
        (N :=
          CompleteDVF.higherPrincipalUnitGroup
            (padicLocalField p).toCompleteDVF (n + 1)) u).2 hu
  calc
    abelianLocalArtinMonoidHom ℚ_[p] L
        (standardLubinTateUnitFactorFieldUnit (padicLocalField p) u) = 1 :=
      hArtin
    _ = (standardLubinTateUnitParameterEquivGal
        (padicLocalField p) hπ n
        (standardLubinTateUnitParameterClass
          (padicLocalField p) n u))⁻¹ := by
      rw [hParameter, map_one, inv_one]

/-- On an invisible principal unit, the actual local Artin automorphism acts
on the chosen primitive `p ^ (n + 1)`-st root by the explicit inverse-unit
exponent. -/
theorem
    padicMultiplicativeAbelianLocalArtin_primitiveRoot_of_mem_higherPrincipalUnitGroup
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (u : (padicLocalField p).valuationSubringˣ)
    (hu : u ∈
      CompleteDVF.higherPrincipalUnitGroup
        (padicLocalField p).toCompleteDVF (n + 1)) :
    let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
    let L := standardLubinTateLevelField hπ n
    letI : FiniteDimensional ℚ_[p] L :=
      standardLubinTateLevelField_finiteDimensional hπ n
    letI : IsAbelianGalois ℚ_[p] L :=
      standardLubinTateLevelField_isAbelianGalois
        (padicLocalField p) hπ n
    (abelianLocalArtinMonoidHom ℚ_[p] L
        (standardLubinTateUnitFactorFieldUnit (padicLocalField p) u))
        (padicMultiplicativePrimitiveRoot p n) =
      padicMultiplicativePrimitiveRoot p n ^
        (PadicInt.toZModPow (p := p) (n + 1)
          ((padicIntEquivValuationSubring p).symm
            ((u⁻¹ : (padicLocalField p).valuationSubringˣ) :
              (padicLocalField p).valuationSubring))).val := by
  let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
  let L := standardLubinTateLevelField hπ n
  let : FiniteDimensional ℚ_[p] L :=
    standardLubinTateLevelField_finiteDimensional hπ n
  let : IsAbelianGalois ℚ_[p] L :=
    standardLubinTateLevelField_isAbelianGalois
      (padicLocalField p) hπ n
  let F := padicLocalField p
  let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
  let L := standardLubinTateLevelField hπ n
  let : FiniteDimensional ℚ_[p] L :=
    standardLubinTateLevelField_finiteDimensional hπ n
  let : IsAbelianGalois ℚ_[p] L :=
    standardLubinTateLevelField_isAbelianGalois F hπ n
  have hArtin :
      abelianLocalArtinMonoidHom ℚ_[p] L
          (standardLubinTateUnitFactorFieldUnit F u) =
        (standardLubinTateUnitParameterEquivGal F hπ n
          (standardLubinTateUnitParameterClass F n u))⁻¹ :=
    padicMultiplicativeAbelianLocalArtin_eq_unitParameter_of_mem_higherPrincipalUnitGroup
      p n u hu
  exact
    (congrArg (fun σ : Gal(L / ℚ_[p]) =>
      σ (padicMultiplicativePrimitiveRoot p n)) hArtin).trans
      (padicMultiplicativePrimitiveRoot_galoisAction p n u)

end LocalClassFieldTheory

end
