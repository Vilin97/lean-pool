/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.HigherUnitLevelMapFixed
/-!
# LubinTate the explicit norm-subgroup computation: the standard level lies in the higher-unit
  fixed field
-/

@[expose] public section

noncomputable
section


open scoped LaurentSeries PowerSeries

namespace LubinTate
namespace EqualCharacteristic

open LocalFieldTheory.DiscreteValuationField

variable {K : Type} [Field K]

/-- The Laurent-series base acts on the completed unramified field through the coefficient
embedding. -/
noncomputable local instance equalCharacteristicHigherUnitMembershipBaseAlgebra
    (F : LocalField K) :
    Algebra F.residueField⸨X⸩
      (equalCharacteristicCompletedUnramifiedField F.residueField) :=
  equalCharacteristicCompletedFrobeniusFixedBaseAlgebra F

/-- The completed level field is a Laurent-series algebra through the completed unramified base. -/
noncomputable local instance equalCharacteristicHigherUnitMembershipLevelAlgebra
    (F : LocalField K) (n : ℕ) :
    Algebra F.residueField⸨X⸩
      (equalCharacteristicCompletedLevelField F n) :=
  equalCharacteristicCompletedFrobeniusFixedLevelAlgebra F n

local instance equalCharacteristicHigherUnitMembershipScalarTower
    (F : LocalField K) (n : ℕ) :
    IsScalarTower F.residueField⸨X⸩
      (equalCharacteristicCompletedUnramifiedField F.residueField)
      (equalCharacteristicCompletedLevelField F n) :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- States the theorem
`equalCharacteristicLubinTateLevelFieldToCompleted_mem_fixedField_of_mem_higherUnit`. -/
theorem
    equalCharacteristicLubinTateLevelFieldToCompleted_mem_fixedField_of_mem_higherUnit
    (F : LocalField K)
    [CharP K F.residueCharacteristic]
    (a : F.residueField⟦X⟧ˣ) (n : ℕ)
    (ha : a ∈ equalCharacteristicLubinTateHigherUnitSubgroup F n)
    (x : equalCharacteristicLubinTateLevelField F n) :
    equalCharacteristicLubinTateLevelFieldToCompleted F n x ∈
      equalCharacteristicCompletedFrobeniusFixedField F a n := by
  rw [equalCharacteristicCompletedFrobeniusFixedField,
    IntermediateField.mem_fixedField_iff]
  intro sigma hsigma
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hsigma
  have hfixed :
      equalCharacteristicLubinTateLevelFieldToCompleted F n x ∈
        MulAction.fixedBy (equalCharacteristicCompletedLevelField F n)
          (equalCharacteristicCompletedFrobeniusAlgEquiv F a n) := by
    rw [MulAction.mem_fixedBy]
    exact
      equalCharacteristicCompletedFrobeniusAlgEquiv_comp_levelFieldToCompleted_of_mem_higherUnit
        F a n ha x
  exact MulAction.mem_fixedBy_zpow hfixed j

end EqualCharacteristic
end LubinTate
