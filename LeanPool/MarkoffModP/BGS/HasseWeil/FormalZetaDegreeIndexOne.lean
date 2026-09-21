/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.HasseWeil.FormalZetaRationality
import Mathlib.RingTheory.PowerSeries.Substitution

/-!
# An ordinary-extension specialization of the degree-index argument

Suppose a zeta series has the indexed denominator

`(1 - T^d) (1 - q^d T^d)`.

After extending the constants by degree `d`, the formal identity is

`Z_extended(T^d) = Z(T)^d`.

If the extended zeta series has the ordinary denominator over the enlarged
constant field, clearing denominators gives

`P_extended(T^d) D(T)^(d - 1) = P(T)^d`.

For `d > 1`, evaluation at `T = 1` forces `P(1) = 0`.  Thus the single,
explicit noncancellation hypothesis `P(1) ≠ 0` forces `d = 1`.  This file
contains only that formal algebra.  Its ordinary-rationality premise for the
extended zeta series is deliberately stronger than indexed rationality and is
not used to close the geometric F. K. Schmidt argument.  The noncircular
indexed-to-indexed theorem is in `FormalZetaDegreeIndexOneIndexed`.
-/

namespace BGS.HasseWeil

noncomputable section

open Polynomial
open scoped PowerSeries

/-- Polynomial realization of the indexed curve-zeta denominator. -/
def indexedCurveZetaDenominatorPolynomial (q d : ℕ) : Polynomial ℂ :=
  (1 - Polynomial.X ^ d) *
    (1 - Polynomial.C ((q : ℂ) ^ d) * Polynomial.X ^ d)

@[simp, norm_cast] theorem coe_indexedCurveZetaDenominatorPolynomial
    (q d : ℕ) :
    (indexedCurveZetaDenominatorPolynomial q d : PowerSeries ℂ) =
      indexedCurveZetaDenominator q d := by
  simp only [indexedCurveZetaDenominatorPolynomial,
    indexedCurveZetaDenominator,
    Polynomial.coe_mul, Polynomial.coe_sub, Polynomial.coe_one,
    Polynomial.coe_pow, Polynomial.coe_X, Polynomial.coe_C]

@[simp] theorem indexedCurveZetaDenominatorPolynomial_eval_one
    (q d : ℕ) :
    (indexedCurveZetaDenominatorPolynomial q d).eval 1 = 0 := by
  simp [indexedCurveZetaDenominatorPolynomial]

/-- The formal constant-extension identity
`Z_extended(T^d) = Z(T)^d`.

This is kept as an explicit proposition because proving it for the geometric
closed-place zeta series is a separate part of the constant-extension
argument. -/
def HasFormalDegreeExtensionZetaIdentity
    (Z extendedZeta : PowerSeries ℂ) (d : ℕ) : Prop :=
  PowerSeries.subst (PowerSeries.X ^ d) extendedZeta = Z ^ d

/-- Substituting `T^d` into a polynomial power series agrees with polynomial
composition by `T^d`. -/
theorem subst_coe_eq_coe_comp_X_pow
    (Q : Polynomial ℂ) (d : ℕ) (hd : 0 < d) :
    PowerSeries.subst (PowerSeries.X ^ d) (Q : PowerSeries ℂ) =
      ((Q.comp (Polynomial.X ^ d) : Polynomial ℂ) : PowerSeries ℂ) := by
  rw [PowerSeries.subst_coe (PowerSeries.HasSubst.X_pow hd.ne')]
  change Polynomial.aeval (PowerSeries.X ^ d) Q = _
  induction Q using Polynomial.induction_on' with
  | add p q hp hq =>
      simp only [map_add, hp, hq, Polynomial.add_comp, Polynomial.coe_add]
  | monomial n a =>
      simp [Polynomial.monomial_comp]

/-- Substituting `T^d` into the ordinary denominator over the degree-`d`
constant extension produces the indexed denominator over the original
constant field. -/
theorem subst_curveZetaDenominator_pow
    (q d : ℕ) (hd : 0 < d) :
    PowerSeries.subst (PowerSeries.X ^ d)
        (curveZetaDenominator (q ^ d)) =
      indexedCurveZetaDenominator q d := by
  let hs : PowerSeries.HasSubst (PowerSeries.X ^ d : PowerSeries ℂ) :=
    PowerSeries.HasSubst.X_pow hd.ne'
  have hsone : PowerSeries.subst (PowerSeries.X ^ d : PowerSeries ℂ)
      (1 : PowerSeries ℂ) = (1 : PowerSeries ℂ) := by
    rw [← PowerSeries.coe_substAlgHom hs]
    exact map_one (PowerSeries.substAlgHom hs)
  rw [curveZetaDenominator, PowerSeries.subst_mul hs]
  simp only [linearPowerSeriesFactor,
    PowerSeries.subst_sub hs, PowerSeries.subst_mul hs,
    hsone, PowerSeries.subst_C, PowerSeries.subst_X hs,
    indexedCurveZetaDenominator]
  norm_num

/-- Clearing the base and constant-extension denominators leaves exactly
`d - 1` copies of the indexed denominator.

No noncancellation hypothesis is used here. -/
theorem clearedNumeratorIdentity_of_indexed_rational_and_degreeExtension
    (Z extendedZeta : PowerSeries ℂ) (q d : ℕ)
    (P extendedP : Polynomial ℂ)
    (hd : 0 < d)
    (hindexed : HasIndexedCurveZetaRationalForm Z q d P)
    (hextended : HasCurveZetaRationalForm extendedZeta (q ^ d) extendedP)
    (hextension : HasFormalDegreeExtensionZetaIdentity Z extendedZeta d) :
    extendedP.comp (Polynomial.X ^ d) *
        indexedCurveZetaDenominatorPolynomial q d ^ (d - 1) =
      P ^ d := by
  let hs : PowerSeries.HasSubst (PowerSeries.X ^ d : PowerSeries ℂ) :=
    PowerSeries.HasSubst.X_pow hd.ne'
  have hextendedCleared :
      Z ^ d * indexedCurveZetaDenominator q d =
        ((extendedP.comp (Polynomial.X ^ d) : Polynomial ℂ) :
          PowerSeries ℂ) := by
    have h := congrArg
      (PowerSeries.subst (PowerSeries.X ^ d : PowerSeries ℂ)) hextended
    rw [PowerSeries.subst_mul hs, hextension,
      subst_curveZetaDenominator_pow q d hd,
      subst_coe_eq_coe_comp_X_pow extendedP d hd] at h
    exact h
  have hindexedPow :
      Z ^ d * indexedCurveZetaDenominator q d ^ d =
        ((P ^ d : Polynomial ℂ) : PowerSeries ℂ) := by
    have h := congrArg (fun F : PowerSeries ℂ => F ^ d) hindexed
    simpa only [mul_pow, Polynomial.coe_pow] using h
  have hpred : d - 1 + 1 = d :=
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hd.ne')
  apply Polynomial.coe_injective ℂ
  simp only [Polynomial.coe_mul, Polynomial.coe_pow,
    coe_indexedCurveZetaDenominatorPolynomial]
  calc
    ((extendedP.comp (Polynomial.X ^ d) : Polynomial ℂ) :
          PowerSeries ℂ) * indexedCurveZetaDenominator q d ^ (d - 1) =
        (Z ^ d * indexedCurveZetaDenominator q d) *
          indexedCurveZetaDenominator q d ^ (d - 1) := by
            rw [hextendedCleared]
    _ = Z ^ d * indexedCurveZetaDenominator q d ^ d := by
      rw [mul_assoc, mul_comm (indexedCurveZetaDenominator q d),
        ← pow_succ, hpred]
    _ = (P : PowerSeries ℂ) ^ d := by
      simpa only [Polynomial.coe_pow] using hindexedPow

/-- If `d > 1`, the cleared identity forces the original indexed numerator
to vanish at `T = 1`.  This is the formal pole-order mismatch. -/
theorem indexedNumerator_eval_one_eq_zero_of_clearedIdentity
    (q d : ℕ) (P extendedP : Polynomial ℂ)
    (hd : 0 < d) (htwo : 2 ≤ d)
    (hcleared :
      extendedP.comp (Polynomial.X ^ d) *
          indexedCurveZetaDenominatorPolynomial q d ^ (d - 1) =
        P ^ d) :
    P.eval 1 = 0 := by
  have hpredPos : 0 < d - 1 := by omega
  have heval := congrArg (Polynomial.eval 1) hcleared
  have hzero' : 0 = P.eval 1 ^ d := by
    simpa only [Polynomial.eval_mul, Polynomial.eval_pow,
      indexedCurveZetaDenominatorPolynomial_eval_one,
      zero_pow hpredPos.ne', mul_zero] using heval
  exact (pow_eq_zero_iff hd.ne').mp hzero'.symm

/-- Pure polynomial form of the F. K. Schmidt conclusion: numerator
noncancellation at `T = 1` rules out every positive index greater than one. -/
theorem degreeIndex_eq_one_of_clearedNumeratorIdentity
    (q d : ℕ) (P extendedP : Polynomial ℂ)
    (hd : 0 < d) (hPone : P.eval 1 ≠ 0)
    (hcleared :
      extendedP.comp (Polynomial.X ^ d) *
          indexedCurveZetaDenominatorPolynomial q d ^ (d - 1) =
        P ^ d) :
    d = 1 := by
  by_contra hne
  have htwo : 2 ≤ d := by omega
  exact hPone
    (indexedNumerator_eval_one_eq_zero_of_clearedIdentity
      q d P extendedP hd htwo hcleared)

/-- Conditional ordinary-extension specialization of the degree-index theorem.

This algebraic implication is retained as a convenience lemma.  The geometric
development does not use its strong ordinary-rationality premise for the
degree-`d` constant extension; it uses the indexed-to-indexed replacement
instead. -/
theorem degreeIndex_eq_one_of_indexed_rational_and_degreeExtension
    (Z extendedZeta : PowerSeries ℂ) (q d : ℕ)
    (P extendedP : Polynomial ℂ)
    (hd : 0 < d)
    (hPone : P.eval 1 ≠ 0)
    (hindexed : HasIndexedCurveZetaRationalForm Z q d P)
    (hextended : HasCurveZetaRationalForm extendedZeta (q ^ d) extendedP)
    (hextension : HasFormalDegreeExtensionZetaIdentity Z extendedZeta d) :
    d = 1 := by
  apply degreeIndex_eq_one_of_clearedNumeratorIdentity q d P extendedP hd hPone
  exact clearedNumeratorIdentity_of_indexed_rational_and_degreeExtension
    Z extendedZeta q d P extendedP hd hindexed hextended hextension

end

end BGS.HasseWeil
