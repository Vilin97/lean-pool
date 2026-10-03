/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.ChangedUniformizer
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.Existence.LaurentUniformizerNormalization
/-!
# The completed theta-intertwining theorem: normalization of a changed Laurent uniformizer

The parameter `aT`, with `a` a power-series unit, is a prime element of the
canonical Laurent integer ring.  Consequently its inverse has normalized
additive value one.  This is the concrete prime certificate used in the
changed-level norm argument.
-/

@[expose] public section

noncomputable
section

open scoped PowerSeries LaurentSeries ValuativeRel WithZero

universe u v

namespace LubinTate
namespace EqualCharacteristic

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]

/-- The changed Laurent parameter in the canonical integer ring. -/
noncomputable def equalCharacteristicChangedLaurentUniformizerInteger
    (F : LocalField.{u, v} K) (a : F.residueField⟦X⟧ˣ) :
    letI := equalCharacteristicLaurentValuativeRel F
    (ValuativeRel.valuation F.residueField⸨X⸩).integer := by
  letI : ValuativeRel F.residueField⸨X⸩ :=
    equalCharacteristicLaurentValuativeRel F
  exact powerSeriesEquivLaurentValuativeInteger F.residueField
    (equalCharacteristicChangedIntegralUniformizer F a)

/-- States the theorem `equalCharacteristicChangedLaurentUniformizerInteger_coe`. -/
@[simp]
theorem equalCharacteristicChangedLaurentUniformizerInteger_coe
    (F : LocalField.{u, v} K) (a : F.residueField⟦X⟧ˣ) :
    letI := equalCharacteristicLaurentValuativeRel F
    (equalCharacteristicChangedLaurentUniformizerInteger F a).1 =
      equalCharacteristicChangedLaurentUniformizer F a := by
  let : ValuativeRel F.residueField⸨X⸩ :=
    equalCharacteristicLaurentValuativeRel F
  rfl

/-- Multiplying `T` by a power-series unit preserves primality in the
canonical Laurent integer ring. -/
theorem equalCharacteristicChangedLaurentUniformizerInteger_irreducible
    (F : LocalField.{u, v} K) (a : F.residueField⟦X⟧ˣ) :
    letI := equalCharacteristicLaurentValuativeRel F
    Irreducible (equalCharacteristicChangedLaurentUniformizerInteger F a) := by
  let : ValuativeRel F.residueField⸨X⸩ :=
    equalCharacteristicLaurentValuativeRel F
  change Irreducible
    (powerSeriesEquivLaurentValuativeInteger F.residueField
      ((a : F.residueField⟦X⟧) * PowerSeries.X))
  have hprime : Irreducible
      ((a : F.residueField⟦X⟧) * PowerSeries.X) :=
    (irreducible_isUnit_mul a.isUnit).2 PowerSeries.X_irreducible
  exact hprime.map
    (powerSeriesEquivLaurentValuativeInteger F.residueField)

/-- The changed Laurent parameter as a nonzero field unit. -/
noncomputable def equalCharacteristicChangedLaurentUniformizerUnit
    (F : LocalField.{u, v} K) (a : F.residueField⟦X⟧ˣ) :
    F.residueField⸨X⸩ˣ :=
  Units.mk0 (equalCharacteristicChangedLaurentUniformizer F a)
    (equalCharacteristicChangedLaurentUniformizer_ne_zero F a)

/-- States the theorem `equalCharacteristicChangedLaurentUniformizerUnit_coe`. -/
@[simp]
theorem equalCharacteristicChangedLaurentUniformizerUnit_coe
    (F : LocalField.{u, v} K) (a : F.residueField⟦X⟧ˣ) :
    (equalCharacteristicChangedLaurentUniformizerUnit F a).1 =
      equalCharacteristicChangedLaurentUniformizer F a :=
  rfl

/-- In the normalized additive convention, `(aT)⁻¹` has value one. -/
theorem equalCharacteristicChangedLaurentUniformizerUnit_inv_valuationMap
    (F : LocalField.{u, v} K) (a : F.residueField⟦X⟧ˣ) :
    letI := equalCharacteristicLaurentValuativeRel F
    letI := equalCharacteristicLaurentIsNonarchimedeanLocalField F
    LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap F.residueField⸨X⸩
      (Additive.ofMul
        (equalCharacteristicChangedLaurentUniformizerUnit F a)⁻¹) = 1 := by
  let L := F.residueField⸨X⸩
  let : ValuativeRel L := equalCharacteristicLaurentValuativeRel F
  let : IsNonarchimedeanLocalField L :=
    equalCharacteristicLaurentIsNonarchimedeanLocalField F
  rw [LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap_apply]
  exact LocalFieldTheory.v_integerRingIrreducibleFieldUnit_inv L
    (equalCharacteristicChangedLaurentUniformizerInteger F a)
    (equalCharacteristicChangedLaurentUniformizerInteger_irreducible F a)
    (equalCharacteristicChangedLaurentUniformizerUnit F a) (by
      change equalCharacteristicChangedLaurentUniformizer F a =
        equalCharacteristicChangedLaurentUniformizer F a
      rfl)

end EqualCharacteristic
end LubinTate
