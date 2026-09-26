/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.Padic.MultiplicativeEvaluation.CompletedCoefficientEvaluation
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.Padic.MultiplicativeEvaluation.CompletedPrimitivePoint
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.Padic.MultiplicativeEvaluation.CompletedScalarEndomorphism
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.Padic.MultiplicativeEvaluation.FiniteLevelEvaluation
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.Padic.MultiplicativeEvaluation.FiniteLevelPrimitiveRoot
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.Padic.ChangedUniformizerIntertwiner.CompletedSeries
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.Padic.ChangedUniformizerIntertwiner.DefectCorrection
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.Padic.ChangedUniformizerIntertwiner.IntertwinerConstruction
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.Padic.ChangedUniformizerIntertwiner.ScalarCompatibility
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.Padic.ChangedUniformizerIntertwiner.ScalarEndomorphisms
/-!
# Changed-uniformizer evaluation on completed p-adic levels

This endpoint evaluates the genuine changed-uniformizer intertwiner at the
completed multiplicative primitive point.  It proves the exact scalar,
Frobenius, root, and level-embedding identities used by the completed
Lubin--Tate tower.
-/

@[expose] public section

noncomputable
section

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

/-- The changed-uniformizer theta value at the genuine completed
multiplicative primitive point. -/
noncomputable def padicChangedUniformizerThetaValue
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    (padicCompletedLevelCompleteDVF p n).valuationSubring :=
  padicCompletedLevelPowerSeriesEval p n
    (padicCompletedMultiplicativePrimitivePoint p n)
    (padicCompletedMultiplicativePrimitivePoint_hasEval p n)
    (padicChangedUniformizerIntertwiner p u)

/-- The changed-uniformizer theta value is topologically nilpotent. -/
theorem padicChangedUniformizerThetaValue_hasEval
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    PowerSeries.HasEval (padicChangedUniformizerThetaValue p u n) := by
  exact
    padicCompletedLevelPowerSeriesEval_hasEval p n
      (padicCompletedMultiplicativePrimitivePoint p n)
      (padicCompletedMultiplicativePrimitivePoint_hasEval p n)
      (padicChangedUniformizerIntertwiner p u)
      (padicChangedUniformizerIntertwiner_hasSubst p u)

/-- Analytic action of a completed changed-standard scalar endomorphism. -/
noncomputable def padicCompletedChangedStandardScalarEndomorphismValue
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ)
    (x : (padicCompletedLevelCompleteDVF p n).valuationSubring)
    (hx : PowerSeries.HasEval x)
    (a : (padicLocalField p).valuationSubring) :
    (padicCompletedLevelCompleteDVF p n).valuationSubring :=
  padicCompletedLevelPowerSeriesEval p n x hx
    (padicCompletedChangedStandardScalarEndomorphism p u a)

/-- A completed changed-standard scalar value remains a convergent
evaluation point. -/
theorem padicCompletedChangedStandardScalarEndomorphismValue_hasEval
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ)
    (x : (padicCompletedLevelCompleteDVF p n).valuationSubring)
    (hx : PowerSeries.HasEval x)
    (a : (padicLocalField p).valuationSubring) :
    PowerSeries.HasEval
      (padicCompletedChangedStandardScalarEndomorphismValue
        p u n x hx a) :=
  padicCompletedLevelPowerSeriesEval_hasEval p n x hx
    (padicCompletedChangedStandardScalarEndomorphism p u a)
    (padicCompletedChangedStandardScalarEndomorphism_hasSubst p u a)

/-- Multiplication of changed-standard scalars is composition of their
completed analytic actions. -/
theorem padicCompletedChangedStandardScalarEndomorphismValue_mul
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ)
    (x : (padicCompletedLevelCompleteDVF p n).valuationSubring)
    (hx : PowerSeries.HasEval x)
    (a b : (padicLocalField p).valuationSubring) :
    padicCompletedChangedStandardScalarEndomorphismValue
        p u n x hx (a * b) =
      padicCompletedChangedStandardScalarEndomorphismValue p u n
        (padicCompletedChangedStandardScalarEndomorphismValue
          p u n x hx b)
        (padicCompletedChangedStandardScalarEndomorphismValue_hasEval
          p u n x hx b) a := by
  rw [padicCompletedChangedStandardScalarEndomorphismValue,
    padicCompletedChangedStandardScalarEndomorphism_mul]
  exact
    padicCompletedLevelPowerSeriesEval_subst p n x hx
      (padicCompletedChangedStandardScalarEndomorphism p u b)
      (padicCompletedChangedStandardScalarEndomorphism p u a)
      (padicCompletedChangedStandardScalarEndomorphism_hasSubst p u b)
      (padicCompletedChangedStandardScalarEndomorphismValue_hasEval
        p u n x hx b)

/-- The scalar `1` fixes every completed changed-standard evaluation
point. -/
@[simp]
theorem padicCompletedChangedStandardScalarEndomorphismValue_one
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ)
    (x : (padicCompletedLevelCompleteDVF p n).valuationSubring)
    (hx : PowerSeries.HasEval x) :
    padicCompletedChangedStandardScalarEndomorphismValue
        p u n x hx 1 =
      x := by
  rw [padicCompletedChangedStandardScalarEndomorphismValue,
    padicCompletedChangedStandardScalarEndomorphism_one,
    padicCompletedLevelPowerSeriesEval_X]

/-- Evaluating a power of the changed uniformizer is evaluation of the
corresponding changed standard division-polynomial iterate. -/
theorem
    padicCompletedChangedStandardScalarEndomorphismValue_uniformizer_pow
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ)
    (x : (padicCompletedLevelCompleteDVF p n).valuationSubring)
    (hx : PowerSeries.HasEval x) (r : ℕ) :
    padicCompletedChangedStandardScalarEndomorphismValue p u n x hx
        ((standardLubinTateChangedUniformizer
          (padicLocalField p)
          (padicIntEquivValuationSubring p (p : ℤ_[p])) u) ^ r) =
      Polynomial.eval₂
        (padicCompletedLevelPadicIntegerCoefficientHom p n) x
        (standardLubinTatePolynomialIterate
          (padicLocalField p)
          (standardLubinTateChangedUniformizer
            (padicLocalField p)
            (padicIntEquivValuationSubring p (p : ℤ_[p])) u) r) := by
  let hπ :=
    standardLubinTateChangedUniformizer_isUniformizer
      (padicMultiplicativeLubinTateSeries_isUniformizer p) u
  let πu : (padicLocalField p).valuationSubring :=
    standardLubinTateChangedUniformizer
      (padicLocalField p)
      (padicIntEquivValuationSubring p (p : ℤ_[p])) u
  change
    padicCompletedChangedStandardScalarEndomorphismValue
        p u n x hx (πu ^ r) =
      Polynomial.eval₂
        (padicCompletedLevelPadicIntegerCoefficientHom p n) x
        (standardLubinTatePolynomialIterate
          (padicLocalField p) πu r)
  induction r with
  | zero =>
      rw [pow_zero,
        padicCompletedChangedStandardScalarEndomorphismValue_one,
        standardLubinTatePolynomialIterate_zero,
        Polynomial.eval₂_X]
  | succ r ih =>
      rw [pow_succ',
        padicCompletedChangedStandardScalarEndomorphismValue_mul]
      rw [padicCompletedChangedStandardScalarEndomorphismValue,
        padicCompletedChangedStandardScalarEndomorphism_uniformizer,
        padicCompletedChangedStandardSeries,
        ← standardLubinTatePolynomial_toPowerSeries_eq_series hπ,
        padicCompletedLevelPowerSeriesEval_map_polynomial,
        ih,
        standardLubinTatePolynomialIterate_succ,
        Polynomial.eval₂_comp]

/-- Genuine completed-level evaluation of the changed-uniformizer scalar
intertwining identity. -/
theorem padicChangedUniformizerIntertwiner_endomorphism_evaluation
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ)
    (a : (padicLocalField p).valuationSubring) (n : ℕ)
    (x : (padicCompletedLevelCompleteDVF p n).valuationSubring)
    (hx : PowerSeries.HasEval x) :
    padicCompletedLevelPowerSeriesEval p n
        (padicCompletedMultiplicativeScalarEndomorphismValue
          p n x hx a)
        (padicCompletedMultiplicativeScalarEndomorphismValue_hasEval
          p n x hx a)
        (padicChangedUniformizerIntertwiner p u) =
      padicCompletedChangedStandardScalarEndomorphismValue p u n
        (padicCompletedLevelPowerSeriesEval p n x hx
          (padicChangedUniformizerIntertwiner p u))
        (padicCompletedLevelPowerSeriesEval_hasEval p n x hx
          (padicChangedUniformizerIntertwiner p u)
          (padicChangedUniformizerIntertwiner_hasSubst p u))
        a := by
  let M := padicCompletedMultiplicativeScalarEndomorphism p a
  let H := padicChangedUniformizerIntertwiner p u
  let S := padicCompletedChangedStandardScalarEndomorphism p u a
  let xM :=
    padicCompletedMultiplicativeScalarEndomorphismValue p n x hx a
  let xH := padicCompletedLevelPowerSeriesEval p n x hx H
  let hxM : PowerSeries.HasEval xM :=
    padicCompletedMultiplicativeScalarEndomorphismValue_hasEval
      p n x hx a
  let hxH : PowerSeries.HasEval xH :=
    padicCompletedLevelPowerSeriesEval_hasEval p n x hx H
      (padicChangedUniformizerIntertwiner_hasSubst p u)
  calc
    padicCompletedLevelPowerSeriesEval p n xM hxM H =
        padicCompletedLevelPowerSeriesEval p n x hx
          (PowerSeries.subst M H) := by
      exact
        (padicCompletedLevelPowerSeriesEval_subst p n x hx
          M H
          (padicCompletedMultiplicativeScalarEndomorphism_hasSubst p a)
          hxM).symm
    _ =
        padicCompletedLevelPowerSeriesEval p n x hx
          (PowerSeries.subst H S) := by
      rw [padicChangedUniformizerIntertwiner_endomorphism]
    _ =
        padicCompletedLevelPowerSeriesEval p n xH hxH S := by
      exact
        padicCompletedLevelPowerSeriesEval_subst p n x hx
          H S (padicChangedUniformizerIntertwiner_hasSubst p u) hxH

/-- The changed-uniformizer intertwiner carries the actual multiplicative
action of `u p` to the defining changed standard Lubin--Tate series. -/
theorem padicChangedUniformizerIntertwiner_changedSeries_evaluation
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ)
    (x : (padicCompletedLevelCompleteDVF p n).valuationSubring)
    (hx : PowerSeries.HasEval x) :
    padicCompletedLevelPowerSeriesEval p n
        (padicCompletedMultiplicativeScalarEndomorphismValue p n x hx
          (standardLubinTateChangedUniformizer
            (padicLocalField p)
            (padicIntEquivValuationSubring p (p : ℤ_[p])) u))
        (padicCompletedMultiplicativeScalarEndomorphismValue_hasEval
          p n x hx
          (standardLubinTateChangedUniformizer
            (padicLocalField p)
            (padicIntEquivValuationSubring p (p : ℤ_[p])) u))
        (padicChangedUniformizerIntertwiner p u) =
      padicCompletedLevelPowerSeriesEval p n
        (padicCompletedLevelPowerSeriesEval p n x hx
          (padicChangedUniformizerIntertwiner p u))
        (padicCompletedLevelPowerSeriesEval_hasEval p n x hx
          (padicChangedUniformizerIntertwiner p u)
          (padicChangedUniformizerIntertwiner_hasSubst p u))
        (padicCompletedChangedStandardSeries p u) := by
  simpa only [
    padicCompletedChangedStandardScalarEndomorphismValue,
    padicCompletedChangedStandardScalarEndomorphism_uniformizer] using
      padicChangedUniformizerIntertwiner_endomorphism_evaluation
        p u
        (standardLubinTateChangedUniformizer
          (padicLocalField p)
          (padicIntEquivValuationSubring p (p : ℤ_[p])) u)
        n x hx

/-- Evaluation of the changed-uniformizer intertwiner is injective on
topologically nilpotent completed-level integers.  Its inverse is the
formal substitution inverse determined by the genuine Witt-unit linear
coefficient. -/
theorem padicChangedUniformizerIntertwiner_eval_injective
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ)
    {x y : (padicCompletedLevelCompleteDVF p n).valuationSubring}
    (hx : PowerSeries.HasEval x) (hy : PowerSeries.HasEval y)
    (hxy :
      padicCompletedLevelPowerSeriesEval p n x hx
          (padicChangedUniformizerIntertwiner p u) =
        padicCompletedLevelPowerSeriesEval p n y hy
          (padicChangedUniformizerIntertwiner p u)) :
    x = y := by
  apply
    padicCompletedLevelPowerSeriesEval_injective_of_unitLinearCoefficient
      p n (padicChangedUniformizerIntertwiner p u)
      (padicChangedUniformizerIntertwiner_constantCoeff p u)
      ?_ hx hy hxy
  rw [padicChangedUniformizerIntertwiner_coeff_one]
  exact (padicChangedUniformizerLinearCoefficient p u).isUnit

/-- The changed-uniformizer intertwiner evaluates to zero at the zero
point. -/
theorem padicChangedUniformizerIntertwiner_eval_zero
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    padicCompletedLevelPowerSeriesEval p n
        0 PowerSeries.HasEval.zero
        (padicChangedUniformizerIntertwiner p u) =
      0 := by
  obtain ⟨B, hB⟩ :
      (PowerSeries.X :
          PowerSeries (padicCompletedUnramifiedWittRing p)) ∣
        padicChangedUniformizerIntertwiner p u := by
    rw [PowerSeries.X_dvd_iff]
    exact padicChangedUniformizerIntertwiner_constantCoeff p u
  rw [hB, map_mul,
    padicCompletedLevelPowerSeriesEval_X, zero_mul]

/-- The changed-uniformizer theta value is killed by the `n + 1`-fold
changed standard division-polynomial iterate. -/
theorem padicChangedUniformizerThetaValue_iterate_succ_eq_zero
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    Polynomial.eval₂
        (padicCompletedLevelPadicIntegerCoefficientHom p n)
        (padicChangedUniformizerThetaValue p u n)
        (standardLubinTatePolynomialIterate
          (padicLocalField p)
          (standardLubinTateChangedUniformizer
            (padicLocalField p)
            (padicIntEquivValuationSubring p (p : ℤ_[p])) u)
          (n + 1)) =
      0 := by
  let π : (padicLocalField p).valuationSubring :=
    padicIntEquivValuationSubring p (p : ℤ_[p])
  let πu : (padicLocalField p).valuationSubring :=
    standardLubinTateChangedUniformizer
      (padicLocalField p) π u
  change
    Polynomial.eval₂
        (padicCompletedLevelPadicIntegerCoefficientHom p n)
        (padicChangedUniformizerThetaValue p u n)
        (standardLubinTatePolynomialIterate
          (padicLocalField p) πu (n + 1)) =
      0
  let x := padicCompletedMultiplicativePrimitivePoint p n
  let hx := padicCompletedMultiplicativePrimitivePoint_hasEval p n
  let xChanged :=
    padicCompletedMultiplicativeScalarEndomorphismValue
      p n x hx (πu ^ (n + 1))
  let hxChanged : PowerSeries.HasEval xChanged :=
    padicCompletedMultiplicativeScalarEndomorphismValue_hasEval
      p n x hx (πu ^ (n + 1))
  have hbridge :=
    padicChangedUniformizerIntertwiner_endomorphism_evaluation
      p u (πu ^ (n + 1)) n x hx
  have hxChangedZero : xChanged = 0 := by
    change
      padicCompletedMultiplicativeScalarEndomorphismValue p n
          (padicCompletedMultiplicativePrimitivePoint p n)
          (padicCompletedMultiplicativePrimitivePoint_hasEval p n)
          ((standardLubinTateChangedUniformizer
            (padicLocalField p)
            (padicIntEquivValuationSubring p (p : ℤ_[p])) u) ^
              (n + 1)) =
        0
    exact
      padicCompletedMultiplicativePrimitivePoint_changedUniformizer_pow_succ_eq_zero
        p u n
  have hleftZero :
      padicCompletedLevelPowerSeriesEval p n xChanged hxChanged
          (padicChangedUniformizerIntertwiner p u) =
        0 := by
    calc
      _ =
          padicCompletedLevelPowerSeriesEval p n
            0 PowerSeries.HasEval.zero
            (padicChangedUniformizerIntertwiner p u) :=
        padicCompletedLevelPowerSeriesEval_congr_point p n
          hxChanged PowerSeries.HasEval.zero hxChangedZero
          (padicChangedUniformizerIntertwiner p u)
      _ = 0 :=
        padicChangedUniformizerIntertwiner_eval_zero p u n
  have hrightZero :
      padicCompletedChangedStandardScalarEndomorphismValue p u n
          (padicChangedUniformizerThetaValue p u n)
          (padicChangedUniformizerThetaValue_hasEval p u n)
          (πu ^ (n + 1)) =
        0 :=
    hbridge.symm.trans hleftZero
  have hpow :
      padicCompletedChangedStandardScalarEndomorphismValue p u n
          (padicChangedUniformizerThetaValue p u n)
          (padicChangedUniformizerThetaValue_hasEval p u n)
          (πu ^ (n + 1)) =
        Polynomial.eval₂
          (padicCompletedLevelPadicIntegerCoefficientHom p n)
          (padicChangedUniformizerThetaValue p u n)
          (standardLubinTatePolynomialIterate
            (padicLocalField p) πu (n + 1)) := by
    simpa only [π, πu] using
      (padicCompletedChangedStandardScalarEndomorphismValue_uniformizer_pow
        p u n
        (padicChangedUniformizerThetaValue p u n)
        (padicChangedUniformizerThetaValue_hasEval p u n)
        (n + 1))
  exact hpow.symm.trans hrightZero

/-- The changed-uniformizer theta value is not killed one level early. -/
theorem padicChangedUniformizerThetaValue_iterate_ne_zero
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    Polynomial.eval₂
        (padicCompletedLevelPadicIntegerCoefficientHom p n)
        (padicChangedUniformizerThetaValue p u n)
        (standardLubinTatePolynomialIterate
          (padicLocalField p)
          (standardLubinTateChangedUniformizer
            (padicLocalField p)
            (padicIntEquivValuationSubring p (p : ℤ_[p])) u) n) ≠
      0 := by
  let π : (padicLocalField p).valuationSubring :=
    padicIntEquivValuationSubring p (p : ℤ_[p])
  let πu : (padicLocalField p).valuationSubring :=
    standardLubinTateChangedUniformizer
      (padicLocalField p) π u
  change
    Polynomial.eval₂
        (padicCompletedLevelPadicIntegerCoefficientHom p n)
        (padicChangedUniformizerThetaValue p u n)
        (standardLubinTatePolynomialIterate
          (padicLocalField p) πu n) ≠
      0
  intro hzero
  let x := padicCompletedMultiplicativePrimitivePoint p n
  let hx := padicCompletedMultiplicativePrimitivePoint_hasEval p n
  let xChanged :=
    padicCompletedMultiplicativeScalarEndomorphismValue
      p n x hx (πu ^ n)
  let hxChanged : PowerSeries.HasEval xChanged :=
    padicCompletedMultiplicativeScalarEndomorphismValue_hasEval
      p n x hx (πu ^ n)
  have hbridge :=
    padicChangedUniformizerIntertwiner_endomorphism_evaluation
      p u (πu ^ n) n x hx
  have hpow :
      padicCompletedChangedStandardScalarEndomorphismValue p u n
          (padicChangedUniformizerThetaValue p u n)
          (padicChangedUniformizerThetaValue_hasEval p u n)
          (πu ^ n) =
        Polynomial.eval₂
          (padicCompletedLevelPadicIntegerCoefficientHom p n)
          (padicChangedUniformizerThetaValue p u n)
          (standardLubinTatePolynomialIterate
            (padicLocalField p) πu n) := by
    simpa only [π, πu] using
      (padicCompletedChangedStandardScalarEndomorphismValue_uniformizer_pow
        p u n
        (padicChangedUniformizerThetaValue p u n)
        (padicChangedUniformizerThetaValue_hasEval p u n) n)
  have hrightZero :
      padicCompletedChangedStandardScalarEndomorphismValue p u n
          (padicChangedUniformizerThetaValue p u n)
          (padicChangedUniformizerThetaValue_hasEval p u n)
          (πu ^ n) =
        0 :=
    hpow.trans hzero
  have hleftZero :
      padicCompletedLevelPowerSeriesEval p n xChanged hxChanged
          (padicChangedUniformizerIntertwiner p u) =
        0 := by
    exact hbridge.trans hrightZero
  have hxChangedZero : xChanged = 0 := by
    apply padicChangedUniformizerIntertwiner_eval_injective
      p u n hxChanged PowerSeries.HasEval.zero
    exact hleftZero.trans
      (padicChangedUniformizerIntertwiner_eval_zero p u n).symm
  apply
    padicCompletedMultiplicativePrimitivePoint_changedUniformizer_pow_ne_zero
      p u n
  change xChanged = 0
  exact hxChangedZero

/-- The changed-uniformizer theta value is an actual root of the genuine
changed primitive Lubin--Tate polynomial in the completed level. -/
theorem padicChangedUniformizerThetaValue_isRoot
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    ((standardLubinTatePrimitivePolynomial
        (padicLocalField p)
        (standardLubinTateChangedUniformizer
          (padicLocalField p)
          (padicIntEquivValuationSubring p (p : ℤ_[p])) u) n).map
      (padicCompletedLevelPadicIntegerCoefficientHom p n)).IsRoot
        (padicChangedUniformizerThetaValue p u n) := by
  let F := padicLocalField p
  let πu : (padicLocalField p).valuationSubring :=
    standardLubinTateChangedUniformizer
      (padicLocalField p)
      (padicIntEquivValuationSubring p (p : ℤ_[p])) u
  let φ := padicCompletedLevelPadicIntegerCoefficientHom p n
  let theta := padicChangedUniformizerThetaValue p u n
  have hfactor :=
    congrArg (Polynomial.eval₂ φ theta)
      (standardLubinTatePolynomialIterate_succ_factor F πu n)
  rw [Polynomial.eval₂_mul,
    padicChangedUniformizerThetaValue_iterate_succ_eq_zero p u n]
      at hfactor
  have hprimitive :
      Polynomial.eval₂ φ theta
          (standardLubinTatePrimitivePolynomial F πu n) =
        0 :=
    (mul_eq_zero.mp hfactor.symm).resolve_left
      (padicChangedUniformizerThetaValue_iterate_ne_zero p u n)
  rw [Polynomial.IsRoot, Polynomial.eval_map]
  exact hprimitive

/-- Field-valued form of the changed primitive-root equation. -/
theorem padicChangedUniformizerThetaValue_field_isRoot
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    ((standardLubinTatePrimitivePolynomialOverField
        (padicLocalField p)
        (standardLubinTateChangedUniformizer
          (padicLocalField p)
          (padicIntEquivValuationSubring p (p : ℤ_[p])) u) n).map
      (algebraMap ℚ_[p] (padicCompletedLevelField p n))).IsRoot
        ((padicChangedUniformizerThetaValue p u n :
          (padicCompletedLevelCompleteDVF p n).valuationSubring) :
            padicCompletedLevelField p n) := by
  let F := padicLocalField p
  let πu : (padicLocalField p).valuationSubring :=
    standardLubinTateChangedUniformizer
      (padicLocalField p)
      (padicIntEquivValuationSubring p (p : ℤ_[p])) u
  let Q := standardLubinTatePrimitivePolynomial F πu n
  let theta := padicChangedUniformizerThetaValue p u n
  have hroot := padicChangedUniformizerThetaValue_isRoot p u n
  have hinteger :
      Polynomial.eval₂
          (padicCompletedLevelPadicIntegerCoefficientHom p n)
          theta Q =
        0 := by
    simpa only [Polynomial.IsRoot, Polynomial.eval_map, F, πu, Q, theta]
      using hroot
  have hcoe := congrArg
    (fun z : (padicCompletedLevelCompleteDVF p n).valuationSubring =>
      (z : padicCompletedLevelField p n)) hinteger
  have hfield :
      Polynomial.eval₂
          (padicCompletedLevelPadicFieldCoefficientHom p n)
          (theta : padicCompletedLevelField p n) Q =
        0 := by
    change
      ((Polynomial.eval₂
          (padicCompletedLevelPadicIntegerCoefficientHom p n)
          theta Q :
            (padicCompletedLevelCompleteDVF p n).valuationSubring) :
          padicCompletedLevelField p n) =
        0 at hcoe
    rw [padicCompletedLevelPadicIntegerPolynomialEval_coe] at hcoe
    exact hcoe
  rw [standardLubinTatePrimitivePolynomialOverField,
    Polynomial.IsRoot, Polynomial.eval_map, Polynomial.eval₂_map]
  change
    Polynomial.eval₂
        (padicCompletedLevelPadicFieldCoefficientHom p n)
        (theta : padicCompletedLevelField p n) Q =
      0
  exact hfield

/-- The theta value annihilates the minimal polynomial of the canonical
generator of the changed finite Lubin--Tate level. -/
theorem padicChangedUniformizerThetaValue_aeval_levelMinpoly
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    let hπ :=
      standardLubinTateChangedUniformizer_isUniformizer
        (padicMultiplicativeLubinTateSeries_isUniformizer p) u
    Polynomial.aeval
        ((padicChangedUniformizerThetaValue p u n :
          (padicCompletedLevelCompleteDVF p n).valuationSubring) :
            padicCompletedLevelField p n)
        (minpoly ℚ_[p] (standardLubinTateLevelPowerBasis hπ n).gen) =
      0 := by
  let hπ :=
    standardLubinTateChangedUniformizer_isUniformizer
      (padicMultiplicativeLubinTateSeries_isUniformizer p) u
  change
    Polynomial.aeval
        ((padicChangedUniformizerThetaValue p u n :
          (padicCompletedLevelCompleteDVF p n).valuationSubring) :
            padicCompletedLevelField p n)
        (minpoly ℚ_[p] (standardLubinTateLevelPowerBasis hπ n).gen) =
      0
  rw [standardLubinTateLevelPowerBasis_minpoly hπ n,
    Polynomial.aeval_def]
  simpa only [Polynomial.IsRoot, Polynomial.eval_map] using
    padicChangedUniformizerThetaValue_field_isRoot p u n

/-- The genuine embedding of the changed finite Lubin--Tate level into
the completed standard level, sending its canonical generator to theta. -/
noncomputable def padicChangedUniformizerLevelEmbedding
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    let hπ :=
      standardLubinTateChangedUniformizer_isUniformizer
        (padicMultiplicativeLubinTateSeries_isUniformizer p) u
    standardLubinTateLevelField hπ n →ₐ[ℚ_[p]]
      padicCompletedLevelField p n := by
  let hπ :=
    standardLubinTateChangedUniformizer_isUniformizer
      (padicMultiplicativeLubinTateSeries_isUniformizer p) u
  let theta : padicCompletedLevelField p n :=
    ((padicChangedUniformizerThetaValue p u n :
      (padicCompletedLevelCompleteDVF p n).valuationSubring) :
        padicCompletedLevelField p n)
  change
    standardLubinTateLevelField hπ n →ₐ[ℚ_[p]]
      padicCompletedLevelField p n
  exact
    (standardLubinTateLevelPowerBasis hπ n).lift theta
      (by
        simpa only [theta] using
          padicChangedUniformizerThetaValue_aeval_levelMinpoly p u n)

/-- The changed-level embedding sends the canonical power-basis generator
to the actual theta value. -/
@[simp]
theorem padicChangedUniformizerLevelEmbedding_apply_gen
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    let hπ :=
      standardLubinTateChangedUniformizer_isUniformizer
        (padicMultiplicativeLubinTateSeries_isUniformizer p) u
    padicChangedUniformizerLevelEmbedding p u n
        (standardLubinTateLevelPowerBasis hπ n).gen =
      ((padicChangedUniformizerThetaValue p u n :
        (padicCompletedLevelCompleteDVF p n).valuationSubring) :
          padicCompletedLevelField p n) := by
  let hπ :=
    standardLubinTateChangedUniformizer_isUniformizer
      (padicMultiplicativeLubinTateSeries_isUniformizer p) u
  let theta : padicCompletedLevelField p n :=
    ((padicChangedUniformizerThetaValue p u n :
      (padicCompletedLevelCompleteDVF p n).valuationSubring) :
        padicCompletedLevelField p n)
  change
    (standardLubinTateLevelPowerBasis hπ n).lift
        theta
        (padicChangedUniformizerThetaValue_aeval_levelMinpoly p u n)
        (standardLubinTateLevelPowerBasis hπ n).gen =
      theta
  exact
    (standardLubinTateLevelPowerBasis hπ n).lift_gen _ _

/-- Evaluating Frobenius on the coefficients of the changed-uniformizer
intertwiner is the same as first applying the multiplicative unit
endomorphism to the evaluation point and then evaluating the original
intertwiner. -/
theorem padicChangedUniformizerIntertwiner_frobenius_evaluation
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ)
    (x : (padicCompletedLevelCompleteDVF p n).valuationSubring)
    (hx : PowerSeries.HasEval x) :
    padicCompletedLevelPowerSeriesEval p n x hx
        (PowerSeries.map WittVector.frobenius
          (padicChangedUniformizerIntertwiner p u)) =
      padicCompletedLevelPowerSeriesEval p n
        (padicCompletedLevelPowerSeriesEval p n x hx
          (padicCompletedMultiplicativeUnitEndomorphism p u))
        (padicCompletedLevelPowerSeriesEval_hasEval p n x hx
          (padicCompletedMultiplicativeUnitEndomorphism p u)
          (padicCompletedMultiplicativeUnitEndomorphism_hasSubst p u))
        (padicChangedUniformizerIntertwiner p u) := by
  let U := padicCompletedMultiplicativeUnitEndomorphism p u
  let Θ := padicChangedUniformizerIntertwiner p u
  have hseries :
      PowerSeries.map WittVector.frobenius Θ =
        PowerSeries.subst U Θ := by
    simpa only [U, Θ, padicCompletedMultiplicativeUnitEndomorphism] using
      (padicChangedUniformizerIntertwiner_frobenius p u)
  rw [hseries]
  exact
    padicCompletedLevelPowerSeriesEval_subst p n x hx U Θ
      (padicCompletedMultiplicativeUnitEndomorphism_hasSubst p u)
      (padicCompletedLevelPowerSeriesEval_hasEval p n x hx U
        (padicCompletedMultiplicativeUnitEndomorphism_hasSubst p u))

/-- At the completed multiplicative primitive point, coefficient Frobenius
on theta is evaluation of theta at the corresponding unit translate. -/
theorem
    padicChangedUniformizerThetaValue_frobeniusCoefficients
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    padicCompletedLevelPowerSeriesEval p n
        (padicCompletedMultiplicativePrimitivePoint p n)
        (padicCompletedMultiplicativePrimitivePoint_hasEval p n)
        (PowerSeries.map WittVector.frobenius
          (padicChangedUniformizerIntertwiner p u)) =
      padicCompletedLevelPowerSeriesEval p n
        (padicCompletedMultiplicativePrimitivePointUnitAction p u n)
        (padicCompletedMultiplicativePrimitivePointUnitAction_hasEval p u n)
        (padicChangedUniformizerIntertwiner p u) := by
  simpa only [padicCompletedMultiplicativePrimitivePointUnitAction] using
    padicChangedUniformizerIntertwiner_frobenius_evaluation p u n
      (padicCompletedMultiplicativePrimitivePoint p n)
      (padicCompletedMultiplicativePrimitivePoint_hasEval p n)

end LubinTate

end
