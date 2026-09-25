/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.SetTheory.Cardinal.Finite
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
/-!
# Lubin--Tate power series

A Lubin--Tate power series over a chosen valuation ring has zero constant
coefficient, prescribed linear coefficient, and reduces to the residue-field
Frobenius power series. The chosen element is not required to be a uniformizer
in the structure itself, so the coefficient package can be reused independently.
-/

@[expose] public section

noncomputable section

universe u v

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]

/-- A Lubin--Tate series with prescribed linear coefficient π.

The first two fields specify the constant and linear terms. The final field
specifies coefficientwise reduction to the residue-field Frobenius series. -/
structure LubinTateSeries
    (F : LocalField.{u, v} K) (π : F.valuationSubring) where
  /-- The underlying one-variable formal power series over `O_K`. -/
  toPowerSeries : PowerSeries F.valuationSubring
  /-- The constant coefficient of a Lubin--Tate series vanishes. -/
  constantCoeff_eq_zero :
    PowerSeries.constantCoeff toPowerSeries = 0
  /-- The linear coefficient is the chosen element `π`. -/
  coeff_one_eq_uniformizer :
    PowerSeries.coeff 1 toPowerSeries = π
  /-- Reduction to the residue field is the `q`-power Frobenius series. -/
  map_residue_eq_frobenius :
    PowerSeries.map F.residueMap toPowerSeries =
      (PowerSeries.X : PowerSeries F.residueField) ^
        Nat.card F.residueField

attribute [simp] LubinTateSeries.constantCoeff_eq_zero
  LubinTateSeries.coeff_one_eq_uniformizer
  LubinTateSeries.map_residue_eq_frobenius

namespace LubinTateSeries

variable {F : LocalField.{u, v} K} {π : F.valuationSubring}

/-- Two Lubin--Tate series are equal when their underlying power series
are equal. -/
@[ext]
theorem ext {e e' : LubinTateSeries F π}
    (h : e.toPowerSeries = e'.toPowerSeries) : e = e' := by
  cases e
  cases e'
  cases h
  rfl

end LubinTateSeries

end LubinTate

end
