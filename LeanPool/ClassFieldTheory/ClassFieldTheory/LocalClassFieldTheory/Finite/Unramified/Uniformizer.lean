/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.UnramifiedNormSubgroup
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.IdealQuotients
/-!
# Actual unramified norm quotient uniformizer

This file connects the real valuation quotient
`Kˣ / unramifiedNormSubgroup K n` from `NormSubgroup` with the chosen
inverse DVR uniformizer from `IdealQuotients`.  This is the unramified norm calculation
uniformizer side of the local reciprocity construction, kept below
`NormSubgroup` to avoid importing the chosen-uniformizer layer into the generic
valuation quotient API.
-/

@[expose] public section

noncomputable section

universe u

namespace LocalClassFieldTheory


open scoped ValuativeRel
open LocalFieldTheory

/-- the unramified norm calculation, valuation-quotient side: the chosen inverse prime
element has normalized value `1`, hence its class maps to `1 : ZMod n`.
This is the uniformizer-side source matching the normalized Frobenius model. -/
theorem unramifiedNormQuotientEquivZMod_inverseIntegerRingUniformizerFieldUnit
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : Nat) :
    unramifiedNormQuotientEquivZMod K n
        (QuotientGroup.mk (inverseIntegerRingUniformizerFieldUnit K) :
          Kˣ ⧸ unramifiedNormSubgroup K n) =
      Multiplicative.ofAdd (1 : ZMod n) := by
  rw [unramifiedNormQuotientEquivZMod_mk, valuationModDegreeMulHom_apply,
    LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap_apply,
    v_inverseIntegerRingUniformizerFieldUnit]
  simp

/-- Powers of the chosen inverse prime element in the valuation quotient. -/
theorem unramifiedNormQuotientEquivZMod_inverseIntegerRingUniformizerFieldUnit_zpow
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : Nat) (m : Int) :
    unramifiedNormQuotientEquivZMod K n
        ((QuotientGroup.mk (inverseIntegerRingUniformizerFieldUnit K) :
          Kˣ ⧸ unramifiedNormSubgroup K n) ^ m) =
      Multiplicative.ofAdd (m : ZMod n) := by
  rw [map_zpow,
    unramifiedNormQuotientEquivZMod_inverseIntegerRingUniformizerFieldUnit]
  rw [← ofAdd_zsmul]
  simp [zsmul_eq_mul]

end LocalClassFieldTheory
