/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.HigherUnitFixedFieldMembership
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedFrobeniusFixedFieldAlgebra
/-!
# LubinTate the explicit norm-subgroup computation: the standard level embedded in the
  higher-unit fixed field

For a coefficient unit in `U^(n+1)`, the standard completed-level embedding
lands in the completed theta-intertwining theorem fixed field.  This leaf packages its canonical
codomain restriction for the finite-dimensional comparison.
-/

@[expose] public section

noncomputable section


open scoped LaurentSeries PowerSeries

namespace LubinTate
namespace EqualCharacteristic

open LocalFieldTheory.DiscreteValuationField

variable {K : Type} [Field K]

attribute [local instance]
  equalCharacteristicCompletedFrobeniusFixedBaseAlgebra
  equalCharacteristicLubinTateLevelFieldAlgebra
  equalCharacteristicLubinTateLevelFieldSMul
  equalCharacteristicLubinTateLevelFieldModule
  equalCharacteristicCompletedFrobeniusFixedFieldAlgebra
  equalCharacteristicCompletedFrobeniusFixedFieldSMul
  equalCharacteristicCompletedFrobeniusFixedFieldModule

/-- The canonical standard-level embedding into the fixed field attached to
a higher unit, regarded as a ring homomorphism.  This lightweight helper
keeps the codomain restriction independent of algebra-instance search. -/
noncomputable def
    equalCharacteristicLubinTateLevelFieldToFixedFieldOfHigherUnitRingHom
    (F : LocalField K)
    [CharP K F.residueCharacteristic]
    (a : F.residueField⟦X⟧ˣ) (n : ℕ)
    (ha : a ∈ equalCharacteristicLubinTateHigherUnitSubgroup F n) :
    equalCharacteristicLubinTateLevelField F n →+*
      equalCharacteristicCompletedFrobeniusFixedField F a n :=
  (equalCharacteristicLubinTateLevelFieldToCompletedRingHom F n).codRestrict
    (equalCharacteristicCompletedFrobeniusFixedFieldSubring F a n)
    (equalCharacteristicLubinTateLevelFieldToCompleted_mem_fixedField_of_mem_higherUnit
      F a n ha)

/-- The canonical standard-level algebra embedding into the fixed field
attached to a higher unit. -/
noncomputable def equalCharacteristicLubinTateLevelFieldToFixedFieldOfHigherUnit
    (F : LocalField K)
    [CharP K F.residueCharacteristic]
    (a : F.residueField⟦X⟧ˣ) (n : ℕ)
    (ha : a ∈ equalCharacteristicLubinTateHigherUnitSubgroup F n) :
    @AlgHom
      F.residueField⸨X⸩
      ↥(equalCharacteristicLubinTateLevelField F n)
      ↥(equalCharacteristicCompletedFrobeniusFixedField F a n)
      inferInstance
      inferInstance
      inferInstance
      (equalCharacteristicLubinTateLevelFieldAlgebra F n)
      (equalCharacteristicCompletedFrobeniusFixedFieldAlgebra F a n) :=
  AlgHom.mk
    (equalCharacteristicLubinTateLevelFieldToFixedFieldOfHigherUnitRingHom
      F a n ha)
    (fun b => Subtype.ext
      (equalCharacteristicLubinTateLevelFieldToCompletedRingHom_algebraMap F n b))

end EqualCharacteristic
end LubinTate
