/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.HigherUnitsNorm
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.StandardOpenSubgroups
/-!
# LubinTate the explicit norm-subgroup computation: the sharp standard subgroup consists of norms

The higher-unit norm calculation and the uniformizer norm combine to give
the division-level inclusion `(T⁻¹) × U^(n+1) ≤ N(L_n/K)`.
-/

@[expose] public section

noncomputable section


open scoped LaurentSeries PowerSeries ValuativeRel

namespace LubinTate
namespace EqualCharacteristic

open LocalFieldTheory

open LocalFieldTheory.DiscreteValuationField

variable {K : Type} [Field K]

/-- The canonical field principal-unit subgroup `U^(n+1)` consists of
norms from the standard level. -/
theorem equalCharacteristicLubinTate_fieldPrincipalUnits_le_normSubgroup
    (F : LocalField K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) :
    letI : ValuativeRel F.residueField⸨X⸩ :=
      equalCharacteristicLaurentValuativeRel F
    LocalFieldTheory.fieldPrincipalUnits F.residueField⸨X⸩ (n + 1) ≤
      equalCharacteristicLubinTateNormSubgroup F n := by
  let : ValuativeRel F.residueField⸨X⸩ :=
    equalCharacteristicLaurentValuativeRel F
  rw [← equalCharacteristicLubinTateHigherUnitSubgroup_map_toLaurentField_eq]
  rintro x ⟨a, ha, rfl⟩
  exact
    equalCharacteristicPowerSeriesUnitToLaurentFieldUnit_mem_normSubgroup_of_mem_higherUnit
      F n a ha

/-- The sharp standard subgroup `(T⁻¹) × U^(n+1)` is contained in the norm
subgroup. -/
theorem
    equalCharacteristicLubinTate_uniformizerPrincipalSubgroup_le_normSubgroup
    (F : LocalField K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) :
    letI : ValuativeRel F.residueField⸨X⸩ :=
      equalCharacteristicLaurentValuativeRel F
    LocalFieldTheory.uniformizerPrincipalSubgroup F.residueField⸨X⸩
        ((equalCharacteristicLaurentUniformizerUnit F)⁻¹) 1 (n + 1) ≤
      equalCharacteristicLubinTateNormSubgroup F n := by
  let : ValuativeRel F.residueField⸨X⸩ :=
    equalCharacteristicLaurentValuativeRel F
  rw [LocalFieldTheory.uniformizerPrincipalSubgroup]
  apply sup_le
  · simpa using
      equalCharacteristicLubinTate_normalizedUniformizer_zpowers_le_normSubgroup
        F n
  · exact
      equalCharacteristicLubinTate_fieldPrincipalUnits_le_normSubgroup F n

end EqualCharacteristic
end LubinTate
