/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.ValuationSubringUnitMap
import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.FieldNormBase
import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.RamificationIdeal
/-!
# Valuation-subring units in complete-DVF extensions

This file proves compatibility of valuation-ring units with scalar extension
and relates the value of an embedded base uniformizer to the ramification
index.
-/

noncomputable section

universe u v x

namespace LocalFieldTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField

namespace ValuedExtension

open ValuationTheory.DiscreteValuationField.ValuedExtension

variable {K : Type u} {L : Type u} [Field K] [Field L]
variable [Algebra K L]
variable (base : CompleteDVF.{u, v} K) (target : CompleteDVF.{u, x} L)
variable [base.valuation.HasExtension target.valuation]

/-- Embedded base field units of valuation one remain valuation-one units in
the target field. -/
theorem baseUnitsMap_mem_target_unitGroup_of_mem_base_unitGroup
    {a : Kˣ}
    (ha : a ∈ base.valuation.valuationSubring.unitGroup) :
    baseUnitsMap (K := K) (L := L) a ∈
      target.valuation.valuationSubring.unitGroup := by
  rw [_root_.Valuation.mem_unitGroup_iff] at ha ⊢
  simpa using
    (_root_.Valuation.HasExtension.val_map_eq_one_iff
      (vR := base.valuation) (vA := target.valuation) (a : K)).2 ha

/-- Subgroup form: the embedded base valuation-one unit group maps into the
target valuation-one unit group. -/
theorem baseUnitGroup_map_le_target_unitGroup
    :
    (base.valuation.valuationSubring.unitGroup).map
        (baseUnitsMap (K := K) (L := L)) ≤
      target.valuation.valuationSubring.unitGroup := by
  intro a ha
  rcases ha with ⟨b, hb, rfl⟩
  exact baseUnitsMap_mem_target_unitGroup_of_mem_base_unitGroup base target hb

/-- Compatibility between the valuation-ring unit map and the field-unit map. -/
theorem baseUnitsMap_valuationSubringUnitsToFieldUnits
    (a : base.valuationSubringˣ) :
    baseUnitsMap (K := K) (L := L)
        ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.valuationSubringUnitsToFieldUnits base) a) =
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.valuationSubringUnitsToFieldUnits target)
        (Units.map (integerMap base.toDVF target.toDVF).toMonoidHom a) := by
  ext
  simp [CompleteDVF.coe_valuationSubringUnitsToFieldUnits_apply,
    integerMap_apply base.toDVF target.toDVF]

/-- The ramification-ideal unit-multiple source gives the value of the embedded
base uniformizer.

This is the source-producing bridge from
`exists_unit_mul_target_uniformizer_pow_eq_base_uniformizer_image` to the
`hϖmap` input used by `ValuationScaling.lean`. -/
theorem base_uniformizer_image_val_eq_ramificationIndex
    (vL : MultiplicativeIntegerValuation Lˣ)
    (hunit :
      ∀ u : target.valuationSubringˣ,
        (LocalFieldTheory.DiscreteValuationField.CompleteDVF.valuationSubringUnitsToFieldUnits target) u ∈ vL.zeroSubgroup)
    {ϖ : base.valuationSubring} {π : target.valuationSubring}
    (hϖ : base.valuation.IsUniformizer (ϖ : K))
    (hπ : target.valuation.IsUniformizer (π : L))
    (hπval : vL.val (Units.mk0 (π : L) hπ.ne_zero) = 1) :
    vL.val
        (baseUnitsMap (K := K) (L := L)
          (Units.mk0 (ϖ : K) hϖ.ne_zero)) =
      (ramificationIndex base.toDVF target.toDVF : ℤ) := by
  rcases
      (exists_unit_mul_target_uniformizer_pow_eq_base_uniformizer_image
        base target hϖ hπ) with
    ⟨u, hu⟩
  let ϖK : Kˣ := Units.mk0 (ϖ : K) hϖ.ne_zero
  let πL : Lˣ := Units.mk0 (π : L) hπ.ne_zero
  have hfield :
      algebraMap K L (ϖ : K) =
        ((u : target.valuationSubring) : L) *
          (π : L) ^ ramificationIndex base.toDVF target.toDVF := by
    calc
      algebraMap K L (ϖ : K) =
          ((integerMap base.toDVF target.toDVF ϖ :
              target.valuationSubring) : L) :=
        (integerMap_apply base.toDVF target.toDVF ϖ).symm
      _ = (((u : target.valuationSubring) *
            π ^ ramificationIndex base.toDVF target.toDVF :
            target.valuationSubring) : L) := by
        rw [hu]
      _ = ((u : target.valuationSubring) : L) *
          (π : L) ^ ramificationIndex base.toDVF target.toDVF := by
        simp
  have hbase :
      baseUnitsMap (K := K) (L := L) ϖK =
        (LocalFieldTheory.DiscreteValuationField.CompleteDVF.valuationSubringUnitsToFieldUnits target) u *
          πL ^ ramificationIndex base.toDVF target.toDVF := by
    ext
    simpa [ϖK, πL,
      CompleteDVF.coe_valuationSubringUnitsToFieldUnits_apply] using hfield
  have hπLval : vL.val πL = 1 := by
    simpa [πL] using hπval
  change
    vL.val (baseUnitsMap (K := K) (L := L) ϖK) =
      (ramificationIndex base.toDVF target.toDVF : ℤ)
  rw [hbase, vL.val_mul,
    (vL.mem_zeroSubgroup_iff _).1 (hunit u), vL.val_pow, hπLval]
  ring

end ValuedExtension

end LocalFieldTheory.DiscreteValuationField

end
