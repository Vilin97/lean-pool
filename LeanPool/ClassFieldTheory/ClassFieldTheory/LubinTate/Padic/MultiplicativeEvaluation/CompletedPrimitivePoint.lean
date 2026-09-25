/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.Padic.MultiplicativeEvaluation.CompletedScalarEndomorphism
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FiniteLevel.ChangedUniformizer
/-!
# The completed multiplicative primitive point

This module evaluates the completed multiplicative comparison at the chosen
completed standard primitive point.  It proves the exact standard and
changed-uniformizer torsion bounds and constructs the actual unit action on
that point.
-/

@[expose] public section

noncomputable section

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.CompleteDVF
open LocalFieldTheory.DiscreteValuationField.Examples.Qp
open ValuationTheory.DiscreteValuationField
open SameUniformizer

attribute [local instance 50]
  padicCompletedMultiplicativeWittUniformSpace

attribute [local instance]
  padicCompletedMultiplicativeTargetWithIdeal
  padicCompletedMultiplicativeTargetCompleteSpace
  padicCompletedMultiplicativeTargetT2Space

/-- The completed multiplicative division point obtained by evaluating the
coefficient-extended comparison at the chosen completed standard primitive
point. -/
noncomputable def padicCompletedMultiplicativePrimitivePoint
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    (padicCompletedLevelCompleteDVF p n).valuationSubring :=
  padicCompletedLevelPowerSeriesEval p n
    (padicCompletedPrimitiveRootInteger p n)
    (padicCompletedPrimitiveRootInteger_hasEval p n)
    (padicCompletedStandardToMultiplicativeIntertwiner p)

/-- The completed multiplicative primitive point is topologically
nilpotent, so it is itself a valid power-series evaluation point. -/
theorem padicCompletedMultiplicativePrimitivePoint_hasEval
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    PowerSeries.HasEval
      (padicCompletedMultiplicativePrimitivePoint p n) := by
  exact
    padicCompletedLevelPowerSeriesEval_hasEval p n
      (padicCompletedPrimitiveRootInteger p n)
      (padicCompletedPrimitiveRootInteger_hasEval p n)
      (padicCompletedStandardToMultiplicativeIntertwiner p)
      (padicCompletedStandardToMultiplicativeIntertwiner_hasSubst p)

/-- The actual completed multiplicative primitive point is killed by the
scalar endomorphism for `π ^ (n + 1)`. -/
theorem
    padicCompletedMultiplicativePrimitivePoint_uniformizer_pow_succ_eq_zero
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    padicCompletedMultiplicativeScalarEndomorphismValue p n
        (padicCompletedMultiplicativePrimitivePoint p n)
        (padicCompletedMultiplicativePrimitivePoint_hasEval p n)
        ((padicIntEquivValuationSubring p (p : ℤ_[p])) ^ (n + 1)) =
      0 := by
  let π : (padicLocalField p).valuationSubring :=
    padicIntEquivValuationSubring p (p : ℤ_[p])
  change
    padicCompletedMultiplicativeScalarEndomorphismValue p n
        (padicCompletedMultiplicativePrimitivePoint p n)
        (padicCompletedMultiplicativePrimitivePoint_hasEval p n)
        (π ^ (n + 1)) =
      0
  have hbridge :=
    padicCompletedStandardToMultiplicativeIntertwiner_eval_endomorphism
      p n
      (padicCompletedPrimitiveRootInteger p n)
      (padicCompletedPrimitiveRootInteger_hasEval p n)
      (π ^ (n + 1))
  have hstandardPoint :
      padicCompletedStandardScalarEndomorphismValue p n
          (padicCompletedPrimitiveRootInteger p n)
          (padicCompletedPrimitiveRootInteger_hasEval p n)
          (π ^ (n + 1)) =
        0 := by
    have hUniformizer :=
      padicCompletedStandardScalarEndomorphismValue_uniformizer_pow
        p n
        (padicCompletedPrimitiveRootInteger p n)
        (padicCompletedPrimitiveRootInteger_hasEval p n)
        (n + 1)
    change
      padicCompletedStandardScalarEndomorphismValue p n
          (padicCompletedPrimitiveRootInteger p n)
          (padicCompletedPrimitiveRootInteger_hasEval p n)
          (π ^ (n + 1)) =
        Polynomial.eval₂
          (padicCompletedLevelPadicIntegerCoefficientHom p n)
          (padicCompletedPrimitiveRootInteger p n)
          (standardLubinTatePolynomialIterate
            (padicLocalField p) π (n + 1)) at hUniformizer
    rw [hUniformizer]
    exact padicCompletedPrimitiveRootInteger_iterate_succ_eq_zero p n
  have hleftZero :
      padicCompletedLevelPowerSeriesEval p n
          (padicCompletedStandardScalarEndomorphismValue p n
            (padicCompletedPrimitiveRootInteger p n)
            (padicCompletedPrimitiveRootInteger_hasEval p n)
            (π ^ (n + 1)))
          (padicCompletedStandardScalarEndomorphismValue_hasEval p n
            (padicCompletedPrimitiveRootInteger p n)
            (padicCompletedPrimitiveRootInteger_hasEval p n)
            (π ^ (n + 1)))
          (padicCompletedStandardToMultiplicativeIntertwiner p) =
        0 := by
    calc
      _ =
          padicCompletedLevelPowerSeriesEval p n
            0 PowerSeries.HasEval.zero
            (padicCompletedStandardToMultiplicativeIntertwiner p) :=
        padicCompletedLevelPowerSeriesEval_congr_point p n
          (padicCompletedStandardScalarEndomorphismValue_hasEval p n
            (padicCompletedPrimitiveRootInteger p n)
            (padicCompletedPrimitiveRootInteger_hasEval p n)
            (π ^ (n + 1)))
          PowerSeries.HasEval.zero hstandardPoint
          (padicCompletedStandardToMultiplicativeIntertwiner p)
      _ = 0 :=
        padicCompletedStandardToMultiplicativeIntertwiner_eval_zero p n
  exact hbridge.symm.trans hleftZero

/-- The actual completed multiplicative primitive point is not killed by
the scalar endomorphism for `π ^ n`. -/
theorem
    padicCompletedMultiplicativePrimitivePoint_uniformizer_pow_ne_zero
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    padicCompletedMultiplicativeScalarEndomorphismValue p n
        (padicCompletedMultiplicativePrimitivePoint p n)
        (padicCompletedMultiplicativePrimitivePoint_hasEval p n)
        ((padicIntEquivValuationSubring p (p : ℤ_[p])) ^ n) ≠
      0 := by
  let π : (padicLocalField p).valuationSubring :=
    padicIntEquivValuationSubring p (p : ℤ_[p])
  change
    padicCompletedMultiplicativeScalarEndomorphismValue p n
        (padicCompletedMultiplicativePrimitivePoint p n)
        (padicCompletedMultiplicativePrimitivePoint_hasEval p n)
        (π ^ n) ≠
      0
  intro hzero
  let lambda := padicCompletedPrimitiveRootInteger p n
  let hlambda := padicCompletedPrimitiveRootInteger_hasEval p n
  let lambdaN :=
    padicCompletedStandardScalarEndomorphismValue
      p n lambda hlambda (π ^ n)
  let hlambdaN : PowerSeries.HasEval lambdaN :=
    padicCompletedStandardScalarEndomorphismValue_hasEval
      p n lambda hlambda (π ^ n)
  have hbridge :=
    padicCompletedStandardToMultiplicativeIntertwiner_eval_endomorphism
      p n lambda hlambda (π ^ n)
  have hleftZero :
      padicCompletedLevelPowerSeriesEval p n lambdaN hlambdaN
          (padicCompletedStandardToMultiplicativeIntertwiner p) =
        0 := by
    exact hbridge.trans hzero
  have hlambdaNZero : lambdaN = 0 := by
    apply
      padicCompletedStandardToMultiplicativeIntertwiner_eval_injective
        p n hlambdaN PowerSeries.HasEval.zero
    exact hleftZero.trans
      (padicCompletedStandardToMultiplicativeIntertwiner_eval_zero
        p n).symm
  apply padicCompletedPrimitiveRootInteger_iterate_ne_zero p n
  rw [←
    padicCompletedStandardScalarEndomorphismValue_uniformizer_pow
      p n lambda hlambda n]
  exact hlambdaNZero

/-- The completed multiplicative primitive point is killed by the
`n + 1`-st power of the scalar `u p` defining the changed uniformizer. -/
theorem
    padicCompletedMultiplicativePrimitivePoint_changedUniformizer_pow_succ_eq_zero
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    padicCompletedMultiplicativeScalarEndomorphismValue p n
        (padicCompletedMultiplicativePrimitivePoint p n)
        (padicCompletedMultiplicativePrimitivePoint_hasEval p n)
        ((standardLubinTateChangedUniformizer
          (padicLocalField p)
          (padicIntEquivValuationSubring p (p : ℤ_[p])) u) ^ (n + 1)) =
      0 := by
  let π : (padicLocalField p).valuationSubring :=
    padicIntEquivValuationSubring p (p : ℤ_[p])
  let x := padicCompletedMultiplicativePrimitivePoint p n
  let hx := padicCompletedMultiplicativePrimitivePoint_hasEval p n
  let xπ :=
    padicCompletedMultiplicativeScalarEndomorphismValue
      p n x hx (π ^ (n + 1))
  let hxπ : PowerSeries.HasEval xπ :=
    padicCompletedMultiplicativeScalarEndomorphismValue_hasEval
      p n x hx (π ^ (n + 1))
  have hxπZero : xπ = 0 := by
    change
      padicCompletedMultiplicativeScalarEndomorphismValue p n
          (padicCompletedMultiplicativePrimitivePoint p n)
          (padicCompletedMultiplicativePrimitivePoint_hasEval p n)
          ((padicIntEquivValuationSubring p (p : ℤ_[p])) ^
            (n + 1)) =
        0
    exact
      padicCompletedMultiplicativePrimitivePoint_uniformizer_pow_succ_eq_zero
        p n
  change
    padicCompletedMultiplicativeScalarEndomorphismValue p n
        x hx
        ((standardLubinTateChangedUniformizer
          (padicLocalField p) π u) ^ (n + 1)) =
      0
  calc
    _ =
        padicCompletedMultiplicativeScalarEndomorphismValue p n
          xπ hxπ
          ((u : (padicLocalField p).valuationSubring) ^ (n + 1)) := by
      rw [standardLubinTateChangedUniformizer_eq_unit_mul, mul_pow]
      simpa only [xπ, hxπ] using
        (padicCompletedMultiplicativeScalarEndomorphismValue_mul
          p n x hx
          ((u : (padicLocalField p).valuationSubring) ^ (n + 1))
          (π ^ (n + 1)))
    _ =
        padicCompletedMultiplicativeScalarEndomorphismValue p n
          0 PowerSeries.HasEval.zero
          ((u : (padicLocalField p).valuationSubring) ^ (n + 1)) := by
      exact
        padicCompletedLevelPowerSeriesEval_congr_point p n
          hxπ PowerSeries.HasEval.zero hxπZero
          (padicCompletedMultiplicativeScalarEndomorphism p
            ((u : (padicLocalField p).valuationSubring) ^ (n + 1)))
    _ = 0 :=
      padicCompletedMultiplicativeScalarEndomorphismValue_zero p n _

/-- The completed multiplicative primitive point is not killed one level
early by the scalar `u p`. -/
theorem
    padicCompletedMultiplicativePrimitivePoint_changedUniformizer_pow_ne_zero
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    padicCompletedMultiplicativeScalarEndomorphismValue p n
        (padicCompletedMultiplicativePrimitivePoint p n)
        (padicCompletedMultiplicativePrimitivePoint_hasEval p n)
        ((standardLubinTateChangedUniformizer
          (padicLocalField p)
          (padicIntEquivValuationSubring p (p : ℤ_[p])) u) ^ n) ≠
      0 := by
  let π : (padicLocalField p).valuationSubring :=
    padicIntEquivValuationSubring p (p : ℤ_[p])
  intro hzero
  let x := padicCompletedMultiplicativePrimitivePoint p n
  let hx := padicCompletedMultiplicativePrimitivePoint_hasEval p n
  let xπ :=
    padicCompletedMultiplicativeScalarEndomorphismValue
      p n x hx (π ^ n)
  let hxπ : PowerSeries.HasEval xπ :=
    padicCompletedMultiplicativeScalarEndomorphismValue_hasEval
      p n x hx (π ^ n)
  change
    padicCompletedMultiplicativeScalarEndomorphismValue p n x hx
        ((standardLubinTateChangedUniformizer
          (padicLocalField p) π u) ^ n) =
      0 at hzero
  have hdecomp :
      padicCompletedMultiplicativeScalarEndomorphismValue p n
          x hx
          ((standardLubinTateChangedUniformizer
            (padicLocalField p) π u) ^ n) =
        padicCompletedMultiplicativeScalarEndomorphismValue p n
          xπ hxπ
          ((u : (padicLocalField p).valuationSubring) ^ n) := by
    rw [standardLubinTateChangedUniformizer_eq_unit_mul, mul_pow]
    simpa only [xπ, hxπ] using
      (padicCompletedMultiplicativeScalarEndomorphismValue_mul
        p n x hx
        ((u : (padicLocalField p).valuationSubring) ^ n)
        (π ^ n))
  have hunitZero :
      padicCompletedMultiplicativeScalarEndomorphismValue p n
          xπ hxπ
          ((u : (padicLocalField p).valuationSubring) ^ n) =
        0 :=
    hdecomp.symm.trans hzero
  have hunitZero' :
      padicCompletedMultiplicativeScalarEndomorphismValue p n
          xπ hxπ
          (((u ^ n : (padicLocalField p).valuationSubringˣ) :
            (padicLocalField p).valuationSubring)) =
        0 := by
    simpa only [Units.val_pow_eq_pow_val] using hunitZero
  have hxπZero : xπ = 0 := by
    apply
      padicCompletedMultiplicativeScalarEndomorphismValue_unit_injective
        p n (u ^ n) hxπ PowerSeries.HasEval.zero
    exact hunitZero'.trans
      (padicCompletedMultiplicativeScalarEndomorphismValue_zero p n
        ((u ^ n : (padicLocalField p).valuationSubringˣ) :
          (padicLocalField p).valuationSubring)).symm
  apply
    padicCompletedMultiplicativePrimitivePoint_uniformizer_pow_ne_zero
      p n
  change xπ = 0
  exact hxπZero

/-- The multiplicative scalar endomorphism attached to a `p`-adic unit,
with coefficients extended to the completed unramified Witt ring. -/
noncomputable def padicCompletedMultiplicativeUnitEndomorphism
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) :
    PowerSeries (padicCompletedUnramifiedWittRing p) :=
  padicCompletedMultiplicativeScalarEndomorphism p
    (u : (padicLocalField p).valuationSubring)

/-- The completed multiplicative unit endomorphism admits formal
substitution. -/
theorem padicCompletedMultiplicativeUnitEndomorphism_hasSubst
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) :
    PowerSeries.HasSubst
      (padicCompletedMultiplicativeUnitEndomorphism p u) :=
  by
    simpa only [padicCompletedMultiplicativeUnitEndomorphism] using
      padicCompletedMultiplicativeScalarEndomorphism_hasSubst p
        (u : (padicLocalField p).valuationSubring)

/-- The action of a completed multiplicative unit endomorphism on the
completed multiplicative primitive point. -/
noncomputable def padicCompletedMultiplicativePrimitivePointUnitAction
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    (padicCompletedLevelCompleteDVF p n).valuationSubring :=
  padicCompletedLevelPowerSeriesEval p n
    (padicCompletedMultiplicativePrimitivePoint p n)
    (padicCompletedMultiplicativePrimitivePoint_hasEval p n)
    (padicCompletedMultiplicativeUnitEndomorphism p u)

/-- The unit translate of the completed multiplicative primitive point is
again a convergent evaluation point. -/
theorem padicCompletedMultiplicativePrimitivePointUnitAction_hasEval
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    PowerSeries.HasEval
      (padicCompletedMultiplicativePrimitivePointUnitAction p u n) := by
  exact
    padicCompletedLevelPowerSeriesEval_hasEval p n
      (padicCompletedMultiplicativePrimitivePoint p n)
      (padicCompletedMultiplicativePrimitivePoint_hasEval p n)
      (padicCompletedMultiplicativeUnitEndomorphism p u)
      (padicCompletedMultiplicativeUnitEndomorphism_hasSubst p u)

end LubinTate

end
