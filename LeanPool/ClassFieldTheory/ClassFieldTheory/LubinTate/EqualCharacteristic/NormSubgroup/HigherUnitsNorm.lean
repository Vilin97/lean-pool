/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormSubgroupFunctoriality
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.UnitTransport
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.HigherUnitFixedFieldEquiv
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedFrobeniusFixedNorm
/-!
# LubinTate the explicit norm-subgroup computation: higher units are norms from the standard level

The fixed-field norm `N(-pi_delta) = aT` from the completed theta-intertwining theorem is
  transported through
the standard-level equivalence.  Cancelling the already known norm `T`
then puts every level-`n+1` higher unit in the standard norm subgroup.
-/

@[expose] public section

noncomputable
section


open scoped LaurentSeries PowerSeries

namespace LubinTate
namespace EqualCharacteristic

open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory
open LocalFieldTheory

variable {K : Type} [Field K]

attribute [local instance]
  equalCharacteristicCompletedFrobeniusFixedBaseAlgebra
  equalCharacteristicLubinTateLevelFieldAlgebra
  equalCharacteristicLubinTateLevelFieldSMul
  equalCharacteristicLubinTateLevelFieldModule
  equalCharacteristicCompletedFrobeniusFixedFieldAlgebra
  equalCharacteristicCompletedFrobeniusFixedFieldSMul
  equalCharacteristicCompletedFrobeniusFixedFieldModule

/-- The sharp higher-unit inclusion in LubinTate the explicit norm-subgroup computation. -/
theorem
    equalCharacteristicPowerSeriesUnitToLaurentFieldUnit_mem_normSubgroup_of_mem_higherUnit
    (F : LocalField K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) (a : F.residueField⟦X⟧ˣ)
    (ha : a ∈ equalCharacteristicLubinTateHigherUnitSubgroup F n) :
    equalCharacteristicPowerSeriesUnitToLaurentFieldUnit F a ∈
      equalCharacteristicLubinTateNormSubgroup F n := by
  let : FiniteDimensional F.residueField⸨X⸩
      (equalCharacteristicLubinTateLevelField F n) :=
    equalCharacteristicLubinTateLevelField_finiteDimensional F n
  let : FiniteDimensional F.residueField⸨X⸩
      (equalCharacteristicCompletedFrobeniusFixedField F a n) :=
    FiniteDimensional.of_finrank_pos (by
      rw [equalCharacteristicCompletedFrobeniusFixedField_finrank]
      exact Nat.mul_pos
        (Nat.sub_pos_of_lt
          (Finite.one_lt_card : 1 < Nat.card F.residueField))
        (Nat.pow_pos Nat.card_pos))
  have hprime : -equalCharacteristicCompletedFrobeniusPrimeElement F a n ≠ 0 := by
    intro hzero
    have hnorm := equalCharacteristicCompletedFrobenius_norm_neg_primeElement F a n
    rw [hzero, Algebra.norm_zero] at hnorm
    exact equalCharacteristicChangedLaurentUniformizer_ne_zero F a hnorm.symm
  let y : (equalCharacteristicCompletedFrobeniusFixedField F a n)ˣ :=
    Units.mk0 (-equalCharacteristicCompletedFrobeniusPrimeElement F a n) hprime
  have hyNorm : normUnits F.residueField⸨X⸩
      (equalCharacteristicCompletedFrobeniusFixedField F a n) y =
      equalCharacteristicChangedLaurentUniformizerUnit F a := by
    apply Units.ext
    exact equalCharacteristicCompletedFrobenius_norm_neg_primeElement F a n
  have hyMem :
      normUnits F.residueField⸨X⸩
          (equalCharacteristicCompletedFrobeniusFixedField F a n) y ∈
        localNormSubgroup F.residueField⸨X⸩
          (equalCharacteristicCompletedFrobeniusFixedField F a n) :=
    ⟨y, rfl⟩
  rw [hyNorm] at hyMem
  let e := equalCharacteristicLubinTateLevelFieldEquivFixedFieldOfHigherUnit
    F a n ha
  have hchanged : equalCharacteristicChangedLaurentUniformizerUnit F a ∈
      equalCharacteristicLubinTateNormSubgroup F n := by
    change equalCharacteristicChangedLaurentUniformizerUnit F a ∈
      localNormSubgroup F.residueField⸨X⸩
        (equalCharacteristicLubinTateLevelField F n)
    rw [← LocalFieldTheory.normSubgroup_algEquiv F.residueField⸨X⸩
      (equalCharacteristicLubinTateLevelField F n)
      (equalCharacteristicCompletedFrobeniusFixedField F a n) e]
    exact hyMem
  have hunit : equalCharacteristicChangedLaurentUnit F a ∈
      equalCharacteristicLubinTateNormSubgroup F n :=
    (equalCharacteristicChangedLaurentUniformizerUnit_mem_normSubgroup_iff
      F n a).1 hchanged
  simpa only [equalCharacteristicPowerSeriesUnitToLaurentFieldUnit_apply]
    using hunit

end EqualCharacteristic
end LubinTate
