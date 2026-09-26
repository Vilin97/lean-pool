/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.HasseWeil.FormalZetaDegreeIndexOne

/-!
# The noncircular indexed F. K. Schmidt argument

The degree-index argument must not assume that the constant extension already
has divisor-degree index one.  This file repairs that dependency: both the
original zeta series and the zeta series after extending constants are allowed
to have indexed denominators.

After substituting `T ^ d` into the extended indexed denominator, clearing
denominators gives

`P_extended(T ^ d) D_d(T) ^ d = P(T) ^ d D_(d e)(T)`.

Here `d` is the original degree index and `e` is the (a priori arbitrary)
degree index after constant extension.  If `d > 1`, the derivative at `T = 1`
of the left side vanishes to order at least two.  The right side has a simple
zero there when `P(1) ≠ 0`.  This contradiction proves `d = 1` without
assuming the conclusion for the constant extension.
-/

@[expose] public section

namespace BGS.HasseWeil

noncomputable section

open Polynomial
open scoped PowerSeries

/-- Substituting `T ^ d` into an indexed denominator over the degree-`d`
constant extension multiplies its index by `d`. -/
theorem subst_indexedCurveZetaDenominator
    (q d e : ℕ) (hd : 0 < d) :
    PowerSeries.subst (PowerSeries.X ^ d)
        (indexedCurveZetaDenominator (q ^ d) e) =
      indexedCurveZetaDenominator q (d * e) := by
  let hs : PowerSeries.HasSubst (PowerSeries.X ^ d : PowerSeries ℂ) :=
    PowerSeries.HasSubst.X_pow hd.ne'
  have hsone : PowerSeries.subst (PowerSeries.X ^ d : PowerSeries ℂ)
      (1 : PowerSeries ℂ) = (1 : PowerSeries ℂ) := by
    rw [← PowerSeries.coe_substAlgHom hs]
    exact map_one (PowerSeries.substAlgHom hs)
  rw [indexedCurveZetaDenominator, PowerSeries.subst_mul hs]
  simp only [PowerSeries.subst_sub hs, PowerSeries.subst_mul hs,
    PowerSeries.subst_pow hs, hsone, PowerSeries.subst_C,
    PowerSeries.subst_X hs, indexedCurveZetaDenominator]
  congr 1
  · ring
  · simp only [Nat.cast_pow, pow_mul]
    rfl

/-- Clearing two indexed rational forms across a degree-`d` constant
extension.  In particular, no ordinary rational form is assumed for the
extended curve. -/
theorem clearedNumeratorIdentity_of_two_indexed_rationalForms
    (Z extendedZeta : PowerSeries ℂ) (q d e : ℕ)
    (P extendedP : Polynomial ℂ)
    (hd : 0 < d)
    (hindexed : HasIndexedCurveZetaRationalForm Z q d P)
    (hextended :
      HasIndexedCurveZetaRationalForm extendedZeta (q ^ d) e extendedP)
    (hextension : HasFormalDegreeExtensionZetaIdentity Z extendedZeta d) :
    extendedP.comp (Polynomial.X ^ d) *
        indexedCurveZetaDenominatorPolynomial q d ^ d =
      P ^ d * indexedCurveZetaDenominatorPolynomial q (d * e) := by
  let hs : PowerSeries.HasSubst (PowerSeries.X ^ d : PowerSeries ℂ) :=
    PowerSeries.HasSubst.X_pow hd.ne'
  have hextendedCleared :
      Z ^ d * indexedCurveZetaDenominator q (d * e) =
        ((extendedP.comp (Polynomial.X ^ d) : Polynomial ℂ) :
          PowerSeries ℂ) := by
    have h := congrArg
      (PowerSeries.subst (PowerSeries.X ^ d : PowerSeries ℂ)) hextended
    rw [PowerSeries.subst_mul hs, hextension,
      subst_indexedCurveZetaDenominator q d e hd,
      subst_coe_eq_coe_comp_X_pow extendedP d hd] at h
    exact h
  have hindexedPow :
      Z ^ d * indexedCurveZetaDenominator q d ^ d =
        ((P ^ d : Polynomial ℂ) : PowerSeries ℂ) := by
    have h := congrArg (fun F : PowerSeries ℂ => F ^ d) hindexed
    simpa only [mul_pow, Polynomial.coe_pow] using h
  apply Polynomial.coe_injective ℂ
  simp only [Polynomial.coe_mul, Polynomial.coe_pow,
    coe_indexedCurveZetaDenominatorPolynomial]
  calc
    ((extendedP.comp (Polynomial.X ^ d) : Polynomial ℂ) :
          PowerSeries ℂ) * indexedCurveZetaDenominator q d ^ d =
        (Z ^ d * indexedCurveZetaDenominator q (d * e)) *
          indexedCurveZetaDenominator q d ^ d := by rw [hextendedCleared]
    _ = (Z ^ d * indexedCurveZetaDenominator q d ^ d) *
          indexedCurveZetaDenominator q (d * e) := by ring
    _ = ((P ^ d : Polynomial ℂ) : PowerSeries ℂ) *
          indexedCurveZetaDenominator q (d * e) := by rw [hindexedPow]
    _ = (P : PowerSeries ℂ) ^ d *
          indexedCurveZetaDenominator q (d * e) := by
      simp only [Polynomial.coe_pow]

/-- The indexed denominator has a simple zero at `T = 1`; this is its exact
derivative there. -/
theorem indexedCurveZetaDenominatorPolynomial_derivative_eval_one
    (q n : ℕ) :
    (indexedCurveZetaDenominatorPolynomial q n).derivative.eval 1 =
      -(n : ℂ) * (1 - (q : ℂ) ^ n) := by
  rw [indexedCurveZetaDenominatorPolynomial, Polynomial.derivative_mul]
  simp only [Polynomial.derivative_sub, Polynomial.derivative_one,
    Polynomial.derivative_pow, Polynomial.derivative_X,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub,
    Polynomial.eval_one, Polynomial.eval_zero, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X]
  ring

/-- Over a nontrivial finite field, every positive-index zeta denominator has
a nonzero derivative at `T = 1`. -/
theorem indexedCurveZetaDenominatorPolynomial_derivative_eval_one_ne_zero
    (q n : ℕ) (hq : 1 < q) (hn : 0 < n) :
    (indexedCurveZetaDenominatorPolynomial q n).derivative.eval 1 ≠ 0 := by
  rw [indexedCurveZetaDenominatorPolynomial_derivative_eval_one]
  apply mul_ne_zero
  · exact neg_ne_zero.mpr (Nat.cast_ne_zero.mpr hn.ne')
  · apply sub_ne_zero.mpr
    norm_cast
    exact (Nat.one_lt_pow hn.ne' hq).ne

/-- At `T = 1`, a product containing at least two copies of the indexed
denominator has zero derivative. -/
theorem derivative_eval_one_mul_indexedDenominator_pow_eq_zero
    (Q : Polynomial ℂ) (q d : ℕ) (htwo : 2 ≤ d) :
    (Q * indexedCurveZetaDenominatorPolynomial q d ^ d).derivative.eval 1 = 0 := by
  rw [Polynomial.derivative_mul]
  simp only [Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_pow, indexedCurveZetaDenominatorPolynomial_eval_one,
    zero_pow (by omega : d ≠ 0), mul_zero,
    Polynomial.derivative_pow, Polynomial.eval_C]
  rw [zero_pow (by omega : d - 1 ≠ 0)]
  ring

/-- At `T = 1`, differentiating a numerator times one indexed denominator
leaves the numerator value times the derivative of that denominator. -/
theorem derivative_eval_one_pow_mul_indexedDenominator
    (P : Polynomial ℂ) (q d n : ℕ) :
    (P ^ d * indexedCurveZetaDenominatorPolynomial q n).derivative.eval 1 =
      P.eval 1 ^ d *
        (indexedCurveZetaDenominatorPolynomial q n).derivative.eval 1 := by
  rw [Polynomial.derivative_mul]
  simp only [Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_pow, indexedCurveZetaDenominatorPolynomial_eval_one,
    mul_zero, zero_add]

/-- Pure polynomial form of the noncircular F. K. Schmidt conclusion. -/
theorem degreeIndex_eq_one_of_twoIndexed_clearedNumeratorIdentity
    (q d e : ℕ) (P extendedP : Polynomial ℂ)
    (hq : 1 < q) (hd : 0 < d) (he : 0 < e)
    (hPone : P.eval 1 ≠ 0)
    (hcleared :
      extendedP.comp (Polynomial.X ^ d) *
          indexedCurveZetaDenominatorPolynomial q d ^ d =
        P ^ d * indexedCurveZetaDenominatorPolynomial q (d * e)) :
    d = 1 := by
  by_contra hne
  have htwo : 2 ≤ d := by omega
  have hderiv :=
    congrArg (fun R : Polynomial ℂ => R.derivative.eval 1) hcleared
  rw [derivative_eval_one_mul_indexedDenominator_pow_eq_zero
      (extendedP.comp (Polynomial.X ^ d)) q d htwo,
    derivative_eval_one_pow_mul_indexedDenominator P q d (d * e)] at hderiv
  have hdenom :
      (indexedCurveZetaDenominatorPolynomial q (d * e)).derivative.eval 1 ≠ 0 :=
    indexedCurveZetaDenominatorPolynomial_derivative_eval_one_ne_zero
      q (d * e) hq (Nat.mul_pos hd he)
  exact (mul_ne_zero (pow_ne_zero d hPone) hdenom) hderiv.symm

/-- Noncircular formal F. K. Schmidt theorem.  The extended zeta series may
have any positive degree index `e`; only indexed rationality is required. -/
theorem degreeIndex_eq_one_of_two_indexed_rationalForms_and_degreeExtension
    (Z extendedZeta : PowerSeries ℂ) (q d e : ℕ)
    (P extendedP : Polynomial ℂ)
    (hq : 1 < q) (hd : 0 < d) (he : 0 < e)
    (hPone : P.eval 1 ≠ 0)
    (hindexed : HasIndexedCurveZetaRationalForm Z q d P)
    (hextended :
      HasIndexedCurveZetaRationalForm extendedZeta (q ^ d) e extendedP)
    (hextension : HasFormalDegreeExtensionZetaIdentity Z extendedZeta d) :
    d = 1 := by
  apply degreeIndex_eq_one_of_twoIndexed_clearedNumeratorIdentity
    q d e P extendedP hq hd he hPone
  exact clearedNumeratorIdentity_of_two_indexed_rationalForms
    Z extendedZeta q d e P extendedP hd hindexed hextended hextension

end

end BGS.HasseWeil
