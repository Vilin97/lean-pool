/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.Basic
/-!
# Valuation-subring units inside field units

This file defines the canonical homomorphism from units of a complete-DVF
valuation ring to units of its fraction field.
-/

@[expose] public section

noncomputable section

universe u v

namespace LocalFieldTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField

namespace CompleteDVF

variable {K : Type u} [Field K]

/-- The inclusion `O_K^* -> K^*` for the chosen valuation ring of a complete
DVF. -/
noncomputable def valuationSubringUnitsToFieldUnits
    (F : CompleteDVF.{u, v} K) : F.valuationSubringˣ →* Kˣ :=
  F.valuation.valuationSubring.unitGroup.subtype.comp
    F.valuation.valuationSubring.unitGroupMulEquiv.symm.toMonoidHom

/--
The defining evaluation formula for `coe_valuationSubringUnitsToFieldUnits` is
`(((CompleteDVF.valuationSubringUnitsToFieldUnits F) a : Kˣ) : K) = (a : F.valuationSubring)`.
-/
@[simp] theorem coe_valuationSubringUnitsToFieldUnits_apply
    (F : CompleteDVF.{u, v} K) (a : F.valuationSubringˣ) :
    (((LocalFieldTheory.DiscreteValuationField.CompleteDVF.valuationSubringUnitsToFieldUnits F)
      a : Kˣ) : K) =
      (a : F.valuationSubring) := by
  change
    ((F.valuation.valuationSubring.unitGroupMulEquiv.symm a : Kˣ) : K) =
      (a : K)
  exact _root_.ValuationSubring.coe_unitGroupMulEquiv_symm_apply
    (A := F.valuation.valuationSubring) (K := K) a

/--
Establishes the membership statement `(CompleteDVF.valuationSubringUnitsToFieldUnits F) a ∈
F.valuation.valuationSubring.unitGroup`.
-/
theorem valuationSubringUnitsToFieldUnits_mem_unitGroup
    (F : CompleteDVF.{u, v} K) (a : F.valuationSubringˣ) :
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.valuationSubringUnitsToFieldUnits F) a ∈
      F.valuation.valuationSubring.unitGroup := by
  change
    ((F.valuation.valuationSubring.unitGroupMulEquiv.symm a :
      F.valuation.valuationSubring.unitGroup) : Kˣ) ∈
      F.valuation.valuationSubring.unitGroup
  exact (F.valuation.valuationSubring.unitGroupMulEquiv.symm a).2


end CompleteDVF
end LocalFieldTheory.DiscreteValuationField

end
