/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FormalModule.Series
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FormalModule.LinearTerm
import Mathlib.RingTheory.MvPowerSeries.Substitution
/-!
# Intertwining equations for Lubin--Tate series

For two Lubin--Tate series with the same prescribed linear coefficient, this
module defines the multivariable intertwining equation and its additive defect.
-/

noncomputable section

universe u v

namespace LubinTate
namespace SameUniformizer

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]
variable {F : LocalField.{u, v} K} {π : F.valuationSubring}
variable {σ : Type*}

/-- Insert a one-variable Lubin--Tate series into the variable `X_i`. -/
noncomputable def inVariable (e : LubinTateSeries F π) (i : σ) :
    MvPowerSeries σ F.valuationSubring :=
  PowerSeries.subst (MvPowerSeries.X i) e.toPowerSeries

/-- States the theorem `constantCoeff_inVariable`. -/
@[simp]
theorem constantCoeff_inVariable (e : LubinTateSeries F π) (i : σ) :
    MvPowerSeries.constantCoeff (inVariable e i) = 0 := by
  exact PowerSeries.constantCoeff_subst_eq_zero
    (MvPowerSeries.constantCoeff_X (R := F.valuationSubring) i)
    e.toPowerSeries e.constantCoeff_eq_zero

/-- The family `i |-> e(X_i)` admits genuine multivariable
substitution. -/
theorem inVariable_hasSubst [Finite σ] (e : LubinTateSeries F π) :
    MvPowerSeries.HasSubst (fun i : σ ↦ inVariable e i) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero
    (fun i ↦ constantCoeff_inVariable e i)

/-- The literal same-uniformizer equation
`e(H(X_i)) = H(ebar(X_i))`. -/
def Intertwines (e ebar : LubinTateSeries F π)
    (H : MvPowerSeries σ F.valuationSubring) : Prop :=
  PowerSeries.subst H e.toPowerSeries =
    MvPowerSeries.subst (fun i : σ ↦ inVariable ebar i) H

/-- The coefficientwise defect whose vanishing is the intertwining
equation. -/
noncomputable def defect (e ebar : LubinTateSeries F π)
    (H : MvPowerSeries σ F.valuationSubring) :
    MvPowerSeries σ F.valuationSubring :=
  PowerSeries.subst H e.toPowerSeries -
    MvPowerSeries.subst (fun i : σ ↦ inVariable ebar i) H

/-- States the theorem `intertwines_iff_defect_eq_zero`. -/
theorem intertwines_iff_defect_eq_zero
    (e ebar : LubinTateSeries F π)
    (H : MvPowerSeries σ F.valuationSubring) :
    Intertwines e ebar H ↔ defect e ebar H = 0 := by
  simp only [Intertwines, defect, sub_eq_zero]

/-- Each variable itself intertwines a Lubin--Tate series with itself. -/
theorem intertwines_X [Finite σ]
    (e : LubinTateSeries F π) (i : σ) :
    Intertwines e e (MvPowerSeries.X i) := by
  rw [Intertwines,
    MvPowerSeries.subst_X (inVariable_hasSubst e)]
  rfl

end SameUniformizer
end LubinTate

end
