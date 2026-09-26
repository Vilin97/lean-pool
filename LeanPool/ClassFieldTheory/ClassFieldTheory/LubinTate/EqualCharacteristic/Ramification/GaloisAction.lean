/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.LevelAbelian
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.Basic
/-!
# Galois action at an equal-characteristic Lubin--Tate level

This module identifies the action of every finite-level Galois automorphism on
the chosen primitive division point with the corresponding truncated
Lubin--Tate bracket.
-/

@[expose] public section

noncomputable
section

open scoped LaurentSeries

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField
open LubinTate.EqualCharacteristic

universe u v

variable {K : Type u} [Field K]

/-- Equal-characteristic Lubin--Tate action frontier: every automorphism of
the explicit level-`n+1` field acts on
the primitive generator through a unique visible unit-parameter bracket. -/
theorem equalCharacteristicLubinTate_galoisAction_eq_bracket_unique
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ)
    (σ : Gal((equalCharacteristicLubinTateLevelField F n)/F.residueField⸨X⸩)) :
    ∃! a : equalCharacteristicLubinTateUnitParameter F n,
      σ (equalCharacteristicLubinTateLevelPowerBasis F n).gen =
        equalCharacteristicLubinTateLevelBracket F n (n + 1)
          (equalCharacteristicLubinTateUnitParameterSeries F n a)
          (equalCharacteristicLubinTateLevelPowerBasis F n).gen := by
  obtain ⟨a, hσ⟩ :=
    equalCharacteristicLubinTateLevelField_exists_unitParameter F n σ
  have ha :
      σ (equalCharacteristicLubinTateLevelPowerBasis F n).gen =
        equalCharacteristicLubinTateLevelBracket F n (n + 1)
          (equalCharacteristicLubinTateUnitParameterSeries F n a)
          (equalCharacteristicLubinTateLevelPowerBasis F n).gen := by
    calc
      σ (equalCharacteristicLubinTateLevelPowerBasis F n).gen =
          equalCharacteristicLubinTateUnitParameterAlgEquiv F n a
            (equalCharacteristicLubinTateLevelPowerBasis F n).gen := by
              rw [hσ]
      _ = equalCharacteristicLubinTateUnitParameterLevelRoot F n a :=
        equalCharacteristicLubinTateUnitParameterAlgEquiv_apply_gen F n a
      _ = equalCharacteristicLubinTateLevelBracket F n (n + 1)
          (equalCharacteristicLubinTateUnitParameterSeries F n a)
          (equalCharacteristicLubinTateLevelPowerBasis F n).gen :=
        (equalCharacteristicLubinTateLevelBracket_gen F n a).symm
  refine ⟨a, ha, ?_⟩
  intro b hb
  apply equalCharacteristicLubinTateUnitParameterLevelRoot_injective F n
  rw [← equalCharacteristicLubinTateLevelBracket_gen F n b,
    ← equalCharacteristicLubinTateLevelBracket_gen F n a]
  exact hb.symm.trans ha

end LubinTate

end
