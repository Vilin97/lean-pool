/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.SetTheory.Cardinal.Finite
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.PrimitiveAction
/-!
# The uniformizer norm identity: finite parameters for the Lubin--Tate action

A unit power series modulo its first `n+1` coefficients is represented by a
nonzero constant coefficient and `n` arbitrary further coefficients.  We use
the concrete finite parameter type `κˣ × (Fin n → κ)`, construct its genuine
power-series units, and prove that their bracket images of a primitive point
are pairwise distinct.  Its cardinality is `(q - 1) q^n`, exactly the degree
of the primitive polynomial.
-/

@[expose] public section

noncomputable section

open scoped PowerSeries LaurentSeries Polynomial

universe u v

namespace LubinTate
namespace EqualCharacteristic

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]

/-- The visible coefficients of a unit power series through level `n`. -/
structure equalCharacteristicLubinTateUnitParameter
    (F : LocalField.{u, v} K) (n : ℕ) where
  /-- The nonzero constant coefficient of the represented unit power series. -/
  constantUnit : F.residueFieldˣ
  /-- The coefficients in degrees `1` through `n`, indexed with degree shifted down by one. -/
  higherCoeff : Fin n → F.residueField

/-- Unit parameters agree when their constant units and higher coefficients agree. -/
@[ext]
theorem equalCharacteristicLubinTateUnitParameter_ext
    (F : LocalField.{u, v} K) (n : ℕ)
    {a b : equalCharacteristicLubinTateUnitParameter F n}
    (hconstant : a.constantUnit = b.constantUnit)
    (hhigher : a.higherCoeff = b.higherCoeff) :
    a = b := by
  cases a
  cases b
  cases hconstant
  cases hhigher
  rfl

/-- Constructor exposing the mathematical coefficient data without relying
on the implementation of the finite parameter. -/
def equalCharacteristicLubinTateUnitParameterOfCoefficients
    (F : LocalField.{u, v} K) (n : ℕ)
    (constantUnit : F.residueFieldˣ)
    (higherCoeff : Fin n → F.residueField) :
    equalCharacteristicLubinTateUnitParameter F n :=
  ⟨constantUnit, higherCoeff⟩

/-- Comparison with the elementary product of visible coefficients. -/
def equalCharacteristicLubinTateUnitParameterEquiv
    (F : LocalField.{u, v} K) (n : ℕ) :
    equalCharacteristicLubinTateUnitParameter F n ≃
      F.residueFieldˣ × (Fin n → F.residueField) where
  toFun a := (a.constantUnit, a.higherCoeff)
  invFun a := equalCharacteristicLubinTateUnitParameterOfCoefficients
    F n a.1 a.2
  left_inv a := by cases a; rfl
  right_inv a := rfl

/-- The finite-level unit parameter space is finite. -/
instance equalCharacteristicLubinTateUnitParameter_finite
    (F : LocalField.{u, v} K) (n : ℕ) :
    Finite (equalCharacteristicLubinTateUnitParameter F n) :=
  Finite.of_equiv (F.residueFieldˣ × (Fin n → F.residueField))
    (equalCharacteristicLubinTateUnitParameterEquiv F n).symm

/-- The finite polynomial power series represented by a visible unit
parameter. -/
noncomputable def equalCharacteristicLubinTateUnitParameterSeries
    (F : LocalField.{u, v} K) (n : ℕ)
    (a : equalCharacteristicLubinTateUnitParameter F n) :
    F.residueField⟦X⟧ :=
  PowerSeries.mk fun i =>
    if i = 0 then (a.constantUnit : F.residueField)
    else if hi : i - 1 < n then a.higherCoeff ⟨i - 1, hi⟩ else 0

/-- The parameter series has the stored unit as its constant coefficient. -/
@[simp]
theorem equalCharacteristicLubinTateUnitParameterSeries_coeff_zero
    (F : LocalField.{u, v} K) (n : ℕ)
    (a : equalCharacteristicLubinTateUnitParameter F n) :
    PowerSeries.coeff 0
      (equalCharacteristicLubinTateUnitParameterSeries F n a) =
        a.constantUnit := by
  simp [equalCharacteristicLubinTateUnitParameterSeries]

/-- Positive coefficients of the parameter series recover the stored higher coefficients. -/
@[simp]
theorem equalCharacteristicLubinTateUnitParameterSeries_coeff_succ
    (F : LocalField.{u, v} K) (n : ℕ)
    (a : equalCharacteristicLubinTateUnitParameter F n) (i : Fin n) :
    PowerSeries.coeff (i + 1)
      (equalCharacteristicLubinTateUnitParameterSeries F n a) =
        a.higherCoeff i := by
  simp [equalCharacteristicLubinTateUnitParameterSeries, i.isLt]

/-- A represented series is a unit because its constant coefficient is the
nonzero value of a residue-field unit. -/
theorem equalCharacteristicLubinTateUnitParameterSeries_isUnit
    (F : LocalField.{u, v} K) (n : ℕ)
    (a : equalCharacteristicLubinTateUnitParameter F n) :
    IsUnit (equalCharacteristicLubinTateUnitParameterSeries F n a) := by
  rw [PowerSeries.isUnit_iff_constantCoeff,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    equalCharacteristicLubinTateUnitParameterSeries_coeff_zero]
  exact a.constantUnit.isUnit

/-- The actual power-series unit attached to a finite parameter. -/
noncomputable def equalCharacteristicLubinTateUnitParameterUnit
    (F : LocalField.{u, v} K) (n : ℕ)
    (a : equalCharacteristicLubinTateUnitParameter F n) :
    F.residueField⟦X⟧ˣ :=
  (equalCharacteristicLubinTateUnitParameterSeries_isUnit F n a).unit

/-- The unit built from a parameter has the parameter series as its value. -/
@[simp]
theorem equalCharacteristicLubinTateUnitParameterUnit_val
    (F : LocalField.{u, v} K) (n : ℕ)
    (a : equalCharacteristicLubinTateUnitParameter F n) :
    (equalCharacteristicLubinTateUnitParameterUnit F n a :
      F.residueField⟦X⟧) =
      equalCharacteristicLubinTateUnitParameterSeries F n a :=
  (equalCharacteristicLubinTateUnitParameterSeries_isUnit F n a).unit_spec

/-- Visible coefficient equality determines the finite parameter. -/
theorem equalCharacteristicLubinTateUnitParameter_eq_of_coeff_eq
    (F : LocalField.{u, v} K) (n : ℕ)
    (a b : equalCharacteristicLubinTateUnitParameter F n)
    (hcoeff : ∀ i ≤ n,
      PowerSeries.coeff i
          (equalCharacteristicLubinTateUnitParameterSeries F n a) =
        PowerSeries.coeff i
          (equalCharacteristicLubinTateUnitParameterSeries F n b)) :
    a = b := by
  apply equalCharacteristicLubinTateUnitParameter_ext F n
  · apply Units.ext
    simpa using hcoeff 0 (Nat.zero_le n)
  · funext i
    simpa using hcoeff (i + 1) (Nat.succ_le_iff.mpr i.isLt)

/-- The primitive-root image attached to a finite unit parameter. -/
noncomputable def equalCharacteristicLubinTateUnitParameterRoot
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) (a : equalCharacteristicLubinTateUnitParameter F n) :
    SeparableClosure F.residueField⸨X⸩ :=
  equalCharacteristicLubinTateAmbientBracket F
    (equalCharacteristicSeparableCoefficientHom F)
    (equalCharacteristicSeparableUniformizer F) (n + 1)
    (equalCharacteristicLubinTateUnitParameterSeries F n a)
    (chosenEqualCharacteristicLubinTatePrimitiveRoot F n)

/-- Distinct visible unit parameters give distinct primitive roots. -/
theorem equalCharacteristicLubinTateUnitParameterRoot_injective
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) :
    Function.Injective
      (equalCharacteristicLubinTateUnitParameterRoot F n) := by
  intro a b hab
  apply equalCharacteristicLubinTateUnitParameter_eq_of_coeff_eq F n a b
  exact chosenEqualCharacteristicLubinTatePrimitiveRoot_bracket_eq_coeff F n
    (equalCharacteristicLubinTateUnitParameterSeries F n a)
    (equalCharacteristicLubinTateUnitParameterSeries F n b) hab

/-- Every parameter root is a root of the primitive polynomial. -/
theorem equalCharacteristicLubinTateUnitParameterRoot_isRoot
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) (a : equalCharacteristicLubinTateUnitParameter F n) :
    ((equalCharacteristicLubinTatePrimitivePolynomial F n).map
      (equalCharacteristicSeparableBaseHom F)).IsRoot
        (equalCharacteristicLubinTateUnitParameterRoot F n a) := by
  simpa [equalCharacteristicLubinTateUnitParameterRoot,
    equalCharacteristicLubinTateUnitParameterUnit_val] using
    equalCharacteristicLubinTatePrimitivePolynomial_isRoot_bracket F n
      (equalCharacteristicLubinTateUnitParameterUnit F n a)

/-- The finite parameter set has the expected cardinality. -/
theorem equalCharacteristicLubinTateUnitParameter_natCard
    (F : LocalField.{u, v} K) (n : ℕ) :
    Nat.card (equalCharacteristicLubinTateUnitParameter F n) =
      (Nat.card F.residueField - 1) *
        Nat.card F.residueField ^ n := by
  rw [Nat.card_congr
      (equalCharacteristicLubinTateUnitParameterEquiv F n),
    Nat.card_prod, Nat.card_units, Nat.card_fun, Nat.card_fin]

end EqualCharacteristic
end LubinTate
