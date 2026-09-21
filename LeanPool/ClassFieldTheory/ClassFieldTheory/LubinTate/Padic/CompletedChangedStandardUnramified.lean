/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.PadicValuationComparison
import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.RamificationAddVal
import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteUnramified
import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteExtensionTopology
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.Padic.CompletedChangedStandardFixedField
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.Padic.CompletedPrimitiveUniformizer
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.DiscreteValuationField.AmbientUniformizer
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.DiscreteValuationField.ChevalleyExtension
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteExtension.Uniqueness
/-!
# The completed standard/changed compositum is unramified over the changed field

The genuine changed-uniformizer theta point is a uniformizer of the ambient
completed Lubin--Tate level.  Uniqueness of finite separable extensions of
the p-adic valuation transports this fact to both the changed fixed field and
the finite standard/changed compositum.  Since the same element is a
uniformizer on both sides, their relative ramification index is one.
-/

noncomputable section

namespace LubinTate

open scoped ValuativeRel

open LocalFieldTheory
open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.Examples.Qp
open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension

/-- The changed prime element is a uniformizer both in the changed fixed
field and in the finite standard/changed compositum, when both finite fields
carry their canonical p-adic spectral valuations. -/
theorem
    padicCompletedChangedUniformizerPrimeElement_isUniformizer_in_changedField_and_compositum
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    let D := padicCompletedChangedUniformizerFixedField p u n
    let M := padicCompletedStandardChangedCompositum p u n
    letI : NontriviallyNormedField D :=
      finiteExtensionSpectralNormedField ℚ_[p] D
    letI : ValuativeRel D :=
      finiteExtensionSpectralValuativeRel ℚ_[p] D
    let : IsNonarchimedeanLocalField D :=
      finiteExtensionSpectralIsNonarchimedeanLocalField ℚ_[p] D
    letI : NontriviallyNormedField M :=
      finiteExtensionSpectralNormedField ℚ_[p] M
    letI : ValuativeRel M :=
      finiteExtensionSpectralValuativeRel ℚ_[p] M
    let : IsNonarchimedeanLocalField M :=
      finiteExtensionSpectralIsNonarchimedeanLocalField ℚ_[p] M
    (localCompleteDVF D).valuation.IsUniformizer
        (padicCompletedChangedUniformizerPrimeElement p u n : D) ∧
      (localCompleteDVF M).valuation.IsUniformizer
        (algebraMap D M
          (padicCompletedChangedUniformizerPrimeElement p u n)) := by
  let D := padicCompletedChangedUniformizerFixedField p u n
  let M := padicCompletedStandardChangedCompositum p u n
  let A := padicCompletedUnramifiedField p
  let E := padicCompletedLevelField p n
  let padicBase := (padicLocalField p).toCompleteDVF
  let canonicalBase := localCompleteDVF ℚ_[p]
  let coefficient := padicCompletedUnramifiedCompleteDVF p
  let ambient := padicCompletedLevelCompleteDVF p n
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
      Valuation.HasExtension (ValuativeRel.valuation ℚ_[p])
        (ValuativeRel.valuation M) :=
    finiteExtensionSpectralValuation_hasExtension ℚ_[p] M
  let :
      canonicalBase.valuation.HasExtension
        (localCompleteDVF D).valuation :=
    localCompleteDVFValuation_hasExtension ℚ_[p] D
  let :
      canonicalBase.valuation.HasExtension
        (localCompleteDVF M).valuation :=
    localCompleteDVFValuation_hasExtension ℚ_[p] M
  let : padicBase.valuation.HasExtension coefficient.valuation :=
    padicCompletedUnramifiedValuation_hasExtension p
  let : coefficient.valuation.HasExtension ambient.valuation :=
    padicCompletedLevelCompleteDVF_hasExtension p n
  let : padicBase.valuation.HasExtension ambient.valuation :=
    ValuationTheory.DiscreteValuationField.Valuation.hasExtension_trans
      padicBase.valuation coefficient.valuation
      ambient.valuation
  let : canonicalBase.valuation.HasExtension ambient.valuation :=
    localCompleteDVFValuation_hasExtension_of_padicLocalField
      p ambient.valuation
  let inclusionD : D →+* E := D.val.toRingHom
  have inclusionD_comp :
      inclusionD.comp (algebraMap ℚ_[p] D) =
        algebraMap ℚ_[p] E := by
    ext x
    exact D.val.commutes x
  let :
      canonicalBase.valuation.HasExtension
        (ambient.valuation.comap inclusionD) :=
    hasExtension_comap_of_algebraMap_compatible
      inclusionD inclusionD_comp
  let inclusionM : M →+* E := M.val.toRingHom
  have inclusionM_comp :
      inclusionM.comp (algebraMap ℚ_[p] M) =
        algebraMap ℚ_[p] E := by
    ext x
    exact M.val.commutes x
  let :
      canonicalBase.valuation.HasExtension
        (ambient.valuation.comap inclusionM) :=
    hasExtension_comap_of_algebraMap_compatible
      inclusionM inclusionM_comp
  have hthetaAmbient :
      ambient.valuation.IsUniformizer
        (((padicChangedUniformizerThetaValue p u n :
          ambient.valuationSubring) : E)) :=
    padicChangedUniformizerThetaValue_isUniformizer p u n
  have hthetaD :
      (localCompleteDVF D).valuation.IsUniformizer
        (padicCompletedChangedUniformizerPrimeElement p u n : D) := by
    apply
      isUniformizer_of_ambient_image_isUniformizer
        canonicalBase (localCompleteDVF D) ambient inclusionD
    change
      ambient.valuation.IsUniformizer
        (((padicChangedUniformizerThetaValue p u n :
          ambient.valuationSubring) : E))
    exact hthetaAmbient
  have hthetaM :
      (localCompleteDVF M).valuation.IsUniformizer
        (algebraMap D M
          (padicCompletedChangedUniformizerPrimeElement p u n)) := by
    apply
      isUniformizer_of_ambient_image_isUniformizer
        canonicalBase (localCompleteDVF M) ambient inclusionM
    change
      ambient.valuation.IsUniformizer
        (((padicChangedUniformizerThetaValue p u n :
          ambient.valuationSubring) : E))
    exact hthetaAmbient
  exact ⟨hthetaD, hthetaM⟩

/-- The finite standard/changed compositum has relative ramification index
one over the changed fixed field. -/
theorem
    padicCompletedStandardChangedCompositum_ramificationIndex_eq_one
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    let D := padicCompletedChangedUniformizerFixedField p u n
    let M := padicCompletedStandardChangedCompositum p u n
    letI : NontriviallyNormedField D :=
      finiteExtensionSpectralNormedField ℚ_[p] D
    letI : ValuativeRel D :=
      finiteExtensionSpectralValuativeRel ℚ_[p] D
    let : IsNonarchimedeanLocalField D :=
      finiteExtensionSpectralIsNonarchimedeanLocalField ℚ_[p] D
    letI : NontriviallyNormedField M :=
      finiteExtensionSpectralNormedField ℚ_[p] M
    letI : ValuativeRel M :=
      finiteExtensionSpectralValuativeRel ℚ_[p] M
    let : IsNonarchimedeanLocalField M :=
      finiteExtensionSpectralIsNonarchimedeanLocalField ℚ_[p] M
    let :
        Valuation.HasExtension (ValuativeRel.valuation D)
          (ValuativeRel.valuation M) :=
      finiteExtensionSpectralValuation_hasExtension_of_tower ℚ_[p] D M
    let :
        (localCompleteDVF D).valuation.HasExtension
          (localCompleteDVF M).valuation :=
      localCompleteDVFValuation_hasExtension D M
    ramificationIndex (localCompleteDVF D).toDVF
      (localCompleteDVF M).toDVF = 1 := by
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
      (localCompleteDVF D).valuation.HasExtension
        (localCompleteDVF M).valuation :=
    localCompleteDVFValuation_hasExtension D M
  let base := localCompleteDVF D
  let target := localCompleteDVF M
  obtain ⟨hthetaD, hthetaM⟩ :=
    padicCompletedChangedUniformizerPrimeElement_isUniformizer_in_changedField_and_compositum
      p u n
  let thetaInteger : base.valuationSubring :=
    ⟨padicCompletedChangedUniformizerPrimeElement p u n,
      hthetaD.val_lt_one.le⟩
  have hthetaMap :
      target.valuation.IsUniformizer
        (((integerMap base.toDVF target.toDVF thetaInteger :
          target.valuationSubring) : M)) := by
    rw [integerMap_apply]
    exact hthetaM
  exact
    LocalFieldTheory.DiscreteValuationField.ValuedExtension.ramificationIndex_eq_one_of_integerMap_uniformizer
      base target thetaInteger
      (by simpa only [thetaInteger] using hthetaD)
      hthetaMap

/-- With the canonical p-adic spectral valuations, the finite
standard/changed compositum is an unramified valued extension of the changed
fixed field. -/
theorem
    padicCompletedStandardChangedCompositum_isUnramifiedValuedExtension
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    let D := padicCompletedChangedUniformizerFixedField p u n
    let M := padicCompletedStandardChangedCompositum p u n
    let : FiniteDimensional D M :=
      FiniteDimensional.right ℚ_[p] D M
    let : Algebra.IsSeparable D M :=
      Algebra.isSeparable_tower_top_of_isSeparable
        (F := ℚ_[p]) (L := D) (E := M)
    letI : NontriviallyNormedField D :=
      finiteExtensionSpectralNormedField ℚ_[p] D
    letI : ValuativeRel D :=
      finiteExtensionSpectralValuativeRel ℚ_[p] D
    let : IsNonarchimedeanLocalField D :=
      finiteExtensionSpectralIsNonarchimedeanLocalField ℚ_[p] D
    letI : NontriviallyNormedField M :=
      finiteExtensionSpectralNormedField ℚ_[p] M
    letI : ValuativeRel M :=
      finiteExtensionSpectralValuativeRel ℚ_[p] M
    let : IsNonarchimedeanLocalField M :=
      finiteExtensionSpectralIsNonarchimedeanLocalField ℚ_[p] M
    let :
        Valuation.HasExtension (ValuativeRel.valuation D)
          (ValuativeRel.valuation M) :=
      finiteExtensionSpectralValuation_hasExtension_of_tower ℚ_[p] D M
    let :
        (localCompleteDVF D).valuation.HasExtension
          (localCompleteDVF M).valuation :=
      localCompleteDVFValuation_hasExtension D M
    let :
        IsScalarTower (localCompleteDVF D).valuationSubring
          (localCompleteDVF M).valuationSubring M :=
      IsScalarTower.of_algebraMap_eq' rfl
    let :
        Module.Finite (ValuativeRel.valuation D).integer
          (ValuativeRel.valuation M).integer := by
      change
        Module.Finite (localCompleteDVF D).valuationSubring
          (localCompleteDVF M).valuationSubring
      exact
        ValuationTheory.DiscreteValuationField.ValuedExtension.moduleFinite_target_valuationSubring_of_finite_separable
          (localCompleteDVF D) (localCompleteDVF M)
    LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension
      D M := by
  let D := padicCompletedChangedUniformizerFixedField p u n
  let M := padicCompletedStandardChangedCompositum p u n
  let : FiniteDimensional D M :=
    FiniteDimensional.right ℚ_[p] D M
  let : Algebra.IsSeparable D M :=
    Algebra.isSeparable_tower_top_of_isSeparable
      (F := ℚ_[p]) (L := D) (E := M)
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
      (localCompleteDVF D).valuation.HasExtension
        (localCompleteDVF M).valuation :=
    localCompleteDVFValuation_hasExtension D M
  let :
      IsScalarTower (localCompleteDVF D).valuationSubring
        (localCompleteDVF M).valuationSubring M :=
    IsScalarTower.of_algebraMap_eq' rfl
  let :
      Module.Finite (ValuativeRel.valuation D).integer
        (ValuativeRel.valuation M).integer := by
    change
      Module.Finite (localCompleteDVF D).valuationSubring
        (localCompleteDVF M).valuationSubring
    exact
      ValuationTheory.DiscreteValuationField.ValuedExtension.moduleFinite_target_valuationSubring_of_finite_separable
        (localCompleteDVF D) (localCompleteDVF M)
  let base := localCompleteDVF D
  let target := localCompleteDVF M
  let :
      Module.IsTorsionFree base.valuationSubring target.valuationSubring :=
    ValuationTheory.DiscreteValuationField.ValuedExtension.moduleIsTorsionFree_target_valuationSubring_of_finite_separable
      base target
  have hramification :
      ramificationIndex base.toDVF target.toDVF = 1 :=
    padicCompletedStandardChangedCompositum_ramificationIndex_eq_one
      p u n
  exact {
    maximalIdeal_ramificationIdx_eq_one := by
      change target.maximalIdeal.ramificationIdx base.valuationSubring = 1
      have hbaseMaximal_ne :
          (base.maximalIdeal : Ideal base.valuationSubring) ≠ ⊥ :=
        Ring.ne_bot_of_isMaximal_of_not_isField
          (IsLocalRing.maximalIdeal.isMaximal base.valuationSubring)
          (IsDiscreteValuationRing.not_isField base.valuationSubring)
      rw [← Ideal.ramificationIdx'_eq_ramificationIdx
        base.maximalIdeal target.maximalIdeal hbaseMaximal_ne]
      exact hramification
  }

end LubinTate

end
