/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.LevelAlgebra
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.Existence.LaurentUniformizerNormalization
/-!
# LubinTate the explicit norm-subgroup computation: the uniformizer factor is a norm

The normalized Laurent uniformizer `T⁻¹` is the inverse of the norm of the
negative primitive Lubin--Tate division point.  This light leaf isolates the
valuation factor of the norm-subgroup calculation from the later openness
and index arguments.
-/

@[expose] public section

noncomputable
section


open scoped LaurentSeries ValuativeRel

namespace LubinTate
namespace EqualCharacteristic

open LocalFieldTheory.DiscreteValuationField

variable {K : Type} [Field K]

universe u

private theorem inverse_mem_normSubgroup_of_normUnits_eq
    {B E : Type u} [Field B] [Field E] [Algebra B E]
    (y : Eˣ) (pi : Bˣ)
    (hyNorm : LocalFieldTheory.normUnits B E y = pi) :
    pi⁻¹ ∈ LocalFieldTheory.localNormSubgroup B E := by
  have hyMem :
      LocalFieldTheory.normUnits B E y ∈
        LocalFieldTheory.localNormSubgroup B E :=
    ⟨y, rfl⟩
  rw [hyNorm] at hyMem
  exact (LocalFieldTheory.localNormSubgroup B E).inv_mem hyMem

/-- The normalized Laurent uniformizer `T⁻¹` is an actual norm from every
explicit Lubin--Tate level field. -/
theorem equalCharacteristicLubinTate_normalizedUniformizer_mem_normSubgroup
    (F : LocalField K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) :
    (equalCharacteristicLaurentUniformizerUnit F)⁻¹ ∈
      equalCharacteristicLubinTateNormSubgroup F n := by
  let : FiniteDimensional F.residueField⸨X⸩
      (equalCharacteristicLubinTateLevelField F n) :=
    equalCharacteristicLubinTateLevelField_finiteDimensional F n
  let y : (equalCharacteristicLubinTateLevelField F n)ˣ :=
    Units.mk0 (-equalCharacteristicLubinTateLevelGenerator F n)
      (neg_ne_zero.mpr (by
        intro hzero
        apply chosenEqualCharacteristicLubinTatePrimitiveRoot_ne_zero F n
        simpa [equalCharacteristicLubinTateLevelGenerator] using
          congrArg Subtype.val hzero))
  apply inverse_mem_normSubgroup_of_normUnits_eq
    y (equalCharacteristicLaurentUniformizerUnit F)
  apply Units.ext
  exact equalCharacteristicLubinTate_norm_neg_levelGenerator F n

/-- Every integral power of the normalized Laurent uniformizer is a norm. -/
theorem equalCharacteristicLubinTate_normalizedUniformizer_zpowers_le_normSubgroup
    (F : LocalField K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) :
    Subgroup.zpowers ((equalCharacteristicLaurentUniformizerUnit F)⁻¹) ≤
      equalCharacteristicLubinTateNormSubgroup F n := by
  rw [Subgroup.zpowers_le]
  exact equalCharacteristicLubinTate_normalizedUniformizer_mem_normSubgroup F n

end EqualCharacteristic
end LubinTate
