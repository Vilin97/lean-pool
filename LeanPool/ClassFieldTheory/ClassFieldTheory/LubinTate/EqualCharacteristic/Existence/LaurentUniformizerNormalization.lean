/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.Existence.LaurentLocalField
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.IdealQuotients
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuationExactSequence
/-!
# normalization of the equal-characteristic parameter

The Laurent-series valuation sends `T` to `exp (-1)`.  The power-series
description of its integer ring makes `T` a genuine prime element, so the
canonical normalized additive valuation sends `T⁻¹` to `1`.
-/

@[expose] public section

noncomputable
section

open scoped PowerSeries LaurentSeries ValuativeRel WithZero

namespace LubinTate
namespace EqualCharacteristic

open LocalFieldTheory.DiscreteValuationField

universe u v

variable {K : Type u} [Field K]

/-- The explicit Laurent parameter has Laurent-series value `exp (-1)`. -/
theorem equalCharacteristicLaurentUniformizer_laurentValuation
    (F : LocalField.{u, v} K) :
    (Valued.v : Valuation F.residueField⸨X⸩ ℤᵐ⁰)
        (equalCharacteristicLaurentUniformizer F) =
      WithZero.exp (-1 : ℤ) := by
  change (Valued.v : Valuation F.residueField⸨X⸩ ℤᵐ⁰)
      (((PowerSeries.X : F.residueField⟦X⟧) :
        F.residueField⸨X⸩)) = _
  simpa using LaurentSeries.valuation_X_pow F.residueField 1

/-- The Laurent parameter in the canonical integer ring determined by the
native Laurent valuation. -/
noncomputable def equalCharacteristicLaurentUniformizerInteger
    (F : LocalField.{u, v} K) :
    letI := equalCharacteristicLaurentValuativeRel F
    (ValuativeRel.valuation F.residueField⸨X⸩).integer := by
  letI : ValuativeRel F.residueField⸨X⸩ :=
    equalCharacteristicLaurentValuativeRel F
  exact powerSeriesEquivLaurentValuativeInteger F.residueField
    (PowerSeries.X : F.residueField⟦X⟧)

/-- States the theorem `equalCharacteristicLaurentUniformizerInteger_coe`. -/
@[simp]
theorem equalCharacteristicLaurentUniformizerInteger_coe
    (F : LocalField.{u, v} K) :
    letI := equalCharacteristicLaurentValuativeRel F
    (equalCharacteristicLaurentUniformizerInteger F).1 =
      equalCharacteristicLaurentUniformizer F := by
  let : ValuativeRel F.residueField⸨X⸩ :=
    equalCharacteristicLaurentValuativeRel F
  rfl

/-- The explicit Laurent parameter is a prime element of the canonical
integer ring. -/
theorem equalCharacteristicLaurentUniformizerInteger_irreducible
    (F : LocalField.{u, v} K) :
    letI := equalCharacteristicLaurentValuativeRel F
    Irreducible (equalCharacteristicLaurentUniformizerInteger F) := by
  let : ValuativeRel F.residueField⸨X⸩ :=
    equalCharacteristicLaurentValuativeRel F
  change Irreducible
    (powerSeriesEquivLaurentValuativeInteger F.residueField
      (PowerSeries.X : F.residueField⟦X⟧))
  exact PowerSeries.X_irreducible.map
    (powerSeriesEquivLaurentValuativeInteger F.residueField)

/-- The Laurent parameter as a nonzero field unit. -/
noncomputable def equalCharacteristicLaurentUniformizerUnit
    (F : LocalField.{u, v} K) : F.residueField⸨X⸩ˣ :=
  Units.mk0 (equalCharacteristicLaurentUniformizer F) (by
    intro hzero
    have hval := equalCharacteristicLaurentUniformizer_laurentValuation F
    rw [hzero, map_zero] at hval
    exact WithZero.exp_ne_zero hval.symm)

/-- States the theorem `equalCharacteristicLaurentUniformizerUnit_coe`. -/
@[simp]
theorem equalCharacteristicLaurentUniformizerUnit_coe
    (F : LocalField.{u, v} K) :
    (equalCharacteristicLaurentUniformizerUnit F).1 =
      equalCharacteristicLaurentUniformizer F :=
  rfl

/-- In the normalized additive convention used here, the inverse Laurent
parameter has value one. -/
theorem equalCharacteristicLaurentUniformizerUnit_inv_valuationMap
    (F : LocalField.{u, v} K) :
    letI := equalCharacteristicLaurentValuativeRel F
    letI := equalCharacteristicLaurentIsNonarchimedeanLocalField F
    LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap F.residueField⸨X⸩
      (Additive.ofMul (equalCharacteristicLaurentUniformizerUnit F)⁻¹) = 1 := by
  let L := F.residueField⸨X⸩
  let : ValuativeRel L := equalCharacteristicLaurentValuativeRel F
  let : IsNonarchimedeanLocalField L :=
    equalCharacteristicLaurentIsNonarchimedeanLocalField F
  rw [LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap_apply]
  exact LocalFieldTheory.v_integerRingIrreducibleFieldUnit_inv L
    (equalCharacteristicLaurentUniformizerInteger F)
    (equalCharacteristicLaurentUniformizerInteger_irreducible F)
    (equalCharacteristicLaurentUniformizerUnit F) (by
      change equalCharacteristicLaurentUniformizer F =
        equalCharacteristicLaurentUniformizer F
      rfl)

end EqualCharacteristic
end LubinTate
