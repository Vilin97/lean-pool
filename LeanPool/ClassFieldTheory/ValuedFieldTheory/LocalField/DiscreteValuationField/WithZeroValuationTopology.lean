/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.RangeRestriction
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.CyclicValueGroup
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.IntegerValuation
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.SeriesValuationEstimates
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.IntegerValuationUniformizer
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.CompleteRangeRestriction
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.UniformizerIntegerValuation
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.RangeRestrictedTopology
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.ValuationSubringUnitMap
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.LocalFieldRangeRestriction
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.ValuedExtensionUnitMap
/-!
# The direct topology of a standard multiplicative integer valuation

This file transfers completeness from the actual-range restriction of a
complete discrete valuation back to the topology obtained directly from
`Valued.mk' v`.
-/

@[expose] public section

open _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF renaming
  mrangeRestrictNontriviallyNormedField →
    mrangeRestrictNontriviallyNormedField

open _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF renaming
  mrangeRestrict_completeSpace_of_residueField_finite →
    mrangeRestrict_completeSpace_of_residueField_finite


noncomputable section

universe u

open Filter
open scoped Valued
open LocalFieldTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField

namespace LocalFieldTheory.DiscreteValuationField
namespace WithZeroValuationTopology

variable {K : Type u} [Field K]

/-- The complete-DVF package attached to a standard `ℤᵐ⁰`-valued complete
discrete valuation. -/
def completeDVF
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [Valuation.IsCompleteDiscrete v] : CompleteDVF.{u, 0} K where
  ValueGroup := WithZero (Multiplicative ℤ)
  valuation := v
  instCompleteDiscrete := inferInstance

/-- Restricting a standard `ℤᵐ⁰`-valued valuation to its actual range does not
change the uniform structure on the field. -/
theorem valuedMk_uniformSpace_eq_mrangeRestrict
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [Valuation.IsCompleteDiscrete v] :
    (Valued.mk' v).toUniformSpace =
      (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued
        (completeDVF v)).toUniformSpace := by
  let w :=
    _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict
      (completeDVF v)
  have hequiv : v.IsEquiv w := by
    intro x y
    rw [← Subtype.coe_le_coe]
    rfl
  change (Valued.mk' v).toUniformSpace = (Valued.mk' w).toUniformSpace
  apply le_antisymm
  · rw [le_iff_uniformContinuous_id]
    simpa using hequiv.symm.uniformContinuous
  · rw [le_iff_uniformContinuous_id]
    simpa using hequiv.uniformContinuous

/-- A standard complete discrete valuation with finite residue field makes the
field complete for the topology obtained directly from `Valued.mk' v`. -/
theorem completeSpace_ofWithZeroValuation
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [Valuation.IsCompleteDiscrete v]
    [Finite (IsLocalRing.ResidueField v.valuationSubring)] :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    CompleteSpace K := by
  let F : CompleteDVF.{u, 0} K := completeDVF v
  let direct : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  let restrictedNormed : NontriviallyNormedField K :=
    mrangeRestrictNontriviallyNormedField F
  have : Finite F.residueField := by
    change Finite (IsLocalRing.ResidueField v.valuationSubring)
    infer_instance
  have hcomplete : @CompleteSpace K restrictedNormed.toUniformSpace := by
    exact
      mrangeRestrict_completeSpace_of_residueField_finite F
  have huniform : direct.toUniformSpace = restrictedNormed.toUniformSpace := by
    change
      (Valued.mk' v).toUniformSpace =
        (mrangeRestrictNontriviallyNormedField
          (completeDVF v)).toUniformSpace
    calc
      (Valued.mk' v).toUniformSpace =
          (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued
            (completeDVF v)).toUniformSpace :=
        valuedMk_uniformSpace_eq_mrangeRestrict v
      _ =
          (mrangeRestrictNontriviallyNormedField
            (completeDVF v)).toUniformSpace := by
        rfl
  let : Valued K (WithZero (Multiplicative ℤ)) := direct
  change @CompleteSpace K direct.toUniformSpace
  rw [huniform]
  exact hcomplete

end WithZeroValuationTopology
end LocalFieldTheory.DiscreteValuationField
