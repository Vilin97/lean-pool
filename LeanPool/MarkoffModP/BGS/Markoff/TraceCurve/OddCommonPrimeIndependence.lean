/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.Markoff.TraceCurve.CommonKummerIndependence

/-!
# Odd common-prime Kummer classes on the split trace curve

This module proves the rational-function and quadratic-base obstructions needed when an odd prime
divides both covering exponents.  Exact height-one-prime divisibility rules out nontrivial powers
of the residual ratio `(1 - sigma * X) / (1 - X)`, and a norm calculation upgrades this to
independence of the two degree-one trace-coordinate classes modulo an odd prime.

Turning this base-field class calculation into irreducibility for noncoprime covers still requires
the roots-of-unity eigencharacter descent in the first Kummer extension.
-/

@[expose] public section

namespace BGS.Markoff

open Polynomial

noncomputable section

variable {K : Type*} [Field K]

/-- No nontrivial power below a prime exponent of the residual trace ratio
can itself be a prime power in the rational-function field.  This is the
height-one-prime obstruction at `sigma * X - 1`; the denominator prime
`1 - X` is distinct precisely when `sigma != 1`. -/
theorem splitTraceResidualRatio_pow_ne_primePower
    (sigma : K) (hsigma : sigma ≠ 0) (hnondegenerate : sigma ≠ 1)
    (q a : ℕ) (_hq : q.Prime) (ha : 0 < a) (haq : a < q)
    (z : RatFunc K) :
    z ^ q ≠
      ((1 - RatFunc.C sigma * RatFunc.X) / (1 - RatFunc.X)) ^ a := by
  intro hpow
  let numeratorPrime : K[X] := normalizedSplitTraceEisensteinPrime sigma
  let numerator : K[X] := 1 - C sigma * X
  let denominator : K[X] := 1 - X
  have hdenominator : denominator ≠ 0 := by
    intro h
    have hval := congrArg (Polynomial.eval (0 : K)) h
    simp [denominator] at hval
  have hdenominatorRat :
      algebraMap K[X] (RatFunc K) denominator ≠ 0 :=
    (map_ne_zero_iff (algebraMap K[X] (RatFunc K))
      (RatFunc.algebraMap_injective K)).mpr hdenominator
  have hzdenominatorRat :
      algebraMap K[X] (RatFunc K) z.denom ≠ 0 :=
    (map_ne_zero_iff (algebraMap K[X] (RatFunc K))
      (RatFunc.algebraMap_injective K)).mpr z.denom_ne_zero
  have hcrossRat :
      algebraMap K[X] (RatFunc K)
          (z.num ^ q * denominator ^ a) =
        algebraMap K[X] (RatFunc K)
          (numerator ^ a * z.denom ^ q) := by
    have hpow' :
        (algebraMap K[X] (RatFunc K) z.num /
            algebraMap K[X] (RatFunc K) z.denom) ^ q =
          (algebraMap K[X] (RatFunc K) numerator /
            algebraMap K[X] (RatFunc K) denominator) ^ a := by
      rw [RatFunc.num_div_denom]
      simpa [numerator, denominator, RatFunc.algebraMap_C,
        RatFunc.algebraMap_X] using hpow
    rw [div_pow, div_pow] at hpow'
    field_simp [hzdenominatorRat, hdenominatorRat] at hpow'
    simpa only [map_mul, map_pow, mul_assoc, mul_left_comm, mul_comm] using hpow'
  have hcross :
      z.num ^ q * denominator ^ a = numerator ^ a * z.denom ^ q :=
    (RatFunc.algebraMap_injective K) hcrossRat
  have hprimeIrreducible : Irreducible numeratorPrime :=
    normalizedSplitTraceEisensteinPrime_irreducible sigma hsigma
  have hprime : Prime numeratorPrime := hprimeIrreducible.prime
  have hprimeNotDvdDenominator : ¬ numeratorPrime ∣ denominator := by
    intro h
    apply normalizedSplitTraceEisensteinPrime_not_dvd_leading
      sigma hsigma hnondegenerate
    simpa [numeratorPrime, denominator, normalizedSplitTraceLeadingCoefficient] using
      (dvd_mul_of_dvd_right h X)
  have hnumeratorEq : numerator = -numeratorPrime := by
    simp [numerator, numeratorPrime, normalizedSplitTraceEisensteinPrime]
  have hprimeDvdNumeratorPow : numeratorPrime ∣ numerator ^ a := by
    rw [hnumeratorEq, neg_pow]
    exact dvd_mul_of_dvd_right (dvd_pow_self numeratorPrime ha.ne') ((-1 : K[X]) ^ a)
  have hprimeDvdLeft : numeratorPrime ∣ z.num ^ q * denominator ^ a := by
    rw [hcross]
    exact dvd_mul_of_dvd_left hprimeDvdNumeratorPow _
  have hprimeNotDvdDenominatorPow : ¬ numeratorPrime ∣ denominator ^ a := by
    exact fun h => hprimeNotDvdDenominator (hprime.dvd_of_dvd_pow h)
  have hprimeDvdNumPow : numeratorPrime ∣ z.num ^ q :=
    (hprime.dvd_mul.mp hprimeDvdLeft).resolve_right hprimeNotDvdDenominatorPow
  have hprimeDvdNum : numeratorPrime ∣ z.num :=
    hprime.dvd_of_dvd_pow hprimeDvdNumPow
  have hprimeNotDvdDenom : ¬ numeratorPrime ∣ z.denom := by
    intro hprimeDvdDenom
    exact hprimeIrreducible.not_isUnit
      (z.isCoprime_num_denom.isUnit_of_dvd' hprimeDvdNum hprimeDvdDenom)
  obtain ⟨num', hnum⟩ := hprimeDvdNum
  have haqLe : a ≤ q := Nat.le_of_lt haq
  have hcancel :
      numeratorPrime ^ (q - a) * (num' ^ q * denominator ^ a) =
        (-1 : K[X]) ^ a * z.denom ^ q := by
    apply mul_left_cancel₀ (pow_ne_zero a hprime.ne_zero)
    calc
      numeratorPrime ^ a *
          (numeratorPrime ^ (q - a) * (num' ^ q * denominator ^ a)) =
          (numeratorPrime * num') ^ q * denominator ^ a := by
            calc
              numeratorPrime ^ a *
                    (numeratorPrime ^ (q - a) *
                      (num' ^ q * denominator ^ a)) =
                  (numeratorPrime ^ a * numeratorPrime ^ (q - a)) *
                    (num' ^ q * denominator ^ a) := by ring
              _ = numeratorPrime ^ (a + (q - a)) *
                    (num' ^ q * denominator ^ a) := by rw [pow_add]
              _ = numeratorPrime ^ q *
                    (num' ^ q * denominator ^ a) := by rw [Nat.add_sub_of_le haqLe]
              _ = (numeratorPrime * num') ^ q * denominator ^ a := by
                rw [mul_pow]
                ring
      _ = z.num ^ q * denominator ^ a := by rw [← hnum]
      _ = numerator ^ a * z.denom ^ q := hcross
      _ = numeratorPrime ^ a *
          ((-1 : K[X]) ^ a * z.denom ^ q) := by
            rw [hnumeratorEq, neg_pow]
            ring
  have hsubPositive : 0 < q - a := Nat.sub_pos_of_lt haq
  have hprimeDvdLeftAfterCancel :
      numeratorPrime ∣
        numeratorPrime ^ (q - a) * (num' ^ q * denominator ^ a) :=
    dvd_mul_of_dvd_left (dvd_pow_self numeratorPrime hsubPositive.ne') _
  have hprimeDvdSignedDenomPow :
      numeratorPrime ∣ (-1 : K[X]) ^ a * z.denom ^ q := by
    rw [← hcancel]
    exact hprimeDvdLeftAfterCancel
  have hprimeNotDvdSign : ¬ numeratorPrime ∣ (-1 : K[X]) ^ a := by
    intro h
    exact hprimeIrreducible.not_isUnit
      (isUnit_of_dvd_unit h (isUnit_neg_one.pow a))
  have hprimeDvdDenomPow : numeratorPrime ∣ z.denom ^ q :=
    (hprime.dvd_mul.mp hprimeDvdSignedDenomPow).resolve_left hprimeNotDvdSign
  exact hprimeNotDvdDenom (hprime.dvd_of_dvd_pow hprimeDvdDenomPow)

/-- The residual ratio is exactly `X * splitTraceRadicand sigma` in the
rational base of the trace curve. -/
theorem RatFunc.X_mul_splitTraceRadicand_eq_residualRatio
    (sigma : K) :
    RatFunc.X * splitTraceRadicand sigma =
      (1 - RatFunc.C sigma * RatFunc.X) / (1 - RatFunc.X) := by
  have hX : (RatFunc.X : RatFunc K) ≠ 0 := RatFunc.X_ne_zero
  have hOneSubX : (1 - RatFunc.X : RatFunc K) ≠ 0 := by
    intro h
    have honeX : (1 : RatFunc K) = RatFunc.X := sub_eq_zero.mp h
    have hdegree := congrArg RatFunc.intDegree honeX
    norm_num at hdegree
  simp only [splitTraceRadicand, splitTraceRadicandNumerator,
    splitTraceRadicandDenominator, map_sub, map_one, map_mul,
    RatFunc.algebraMap_C, RatFunc.algebraMap_X]
  field_simp [hX, hOneSubX]

/-- Trace-radicand form of the odd-common-prime residual obstruction. -/
theorem splitTrace_X_mul_radicand_pow_ne_primePower
    (sigma : K) (hsigma : sigma ≠ 0) (hnondegenerate : sigma ≠ 1)
    (q a : ℕ) (hq : q.Prime) (ha : 0 < a) (haq : a < q)
    (z : RatFunc K) :
    z ^ q ≠ (RatFunc.X * splitTraceRadicand sigma) ^ a := by
  rw [RatFunc.X_mul_splitTraceRadicand_eq_residualRatio]
  exact splitTraceResidualRatio_pow_ne_primePower
    sigma hsigma hnondegenerate q a hq ha haq z

/-- Divisibility form used after taking norms: the exponent of the residual
ratio need only be nonzero modulo `q`. -/
theorem splitTrace_X_mul_radicand_pow_ne_primePower_of_not_dvd
    (sigma : K) (hsigma : sigma ≠ 0) (hnondegenerate : sigma ≠ 1)
    (q a : ℕ) (hq : q.Prime) (hqa : ¬ q ∣ a)
    (z : RatFunc K) :
    z ^ q ≠ (RatFunc.X * splitTraceRadicand sigma) ^ a := by
  intro hpow
  let residual : RatFunc K := RatFunc.X * splitTraceRadicand sigma
  have hresidual : residual ≠ 0 :=
    mul_ne_zero RatFunc.X_ne_zero (splitTraceRadicand_ne_zero sigma hsigma)
  have hremainderNe : a % q ≠ 0 := by
    intro hzero
    apply hqa
    rw [Nat.dvd_iff_mod_eq_zero]
    exact hzero
  have hremainderPositive : 0 < a % q := Nat.pos_of_ne_zero hremainderNe
  have hremainderLt : a % q < q := Nat.mod_lt _ hq.pos
  let reducedRoot : RatFunc K := z / residual ^ (a / q)
  apply splitTrace_X_mul_radicand_pow_ne_primePower
    sigma hsigma hnondegenerate q (a % q) hq
      hremainderPositive hremainderLt reducedRoot
  have hdecomposition : a % q + q * (a / q) = a := Nat.mod_add_div a q
  have hpowerDecomposition :
      residual ^ a =
        residual ^ (a % q) * (residual ^ (a / q)) ^ q := by
    calc
      residual ^ a = residual ^ (a % q + q * (a / q)) := by rw [hdecomposition]
      _ = residual ^ (a % q) * residual ^ (q * (a / q)) := by rw [pow_add]
      _ = residual ^ (a % q) * (residual ^ (a / q)) ^ q := by
        rw [← pow_mul, Nat.mul_comm]
  calc
    reducedRoot ^ q = z ^ q / (residual ^ (a / q)) ^ q := by
      simp [reducedRoot, div_pow]
    _ = residual ^ a / (residual ^ (a / q)) ^ q := by
      rw [hpow]
    _ = residual ^ (a % q) := by
      rw [hpowerDecomposition]
      field_simp [hresidual]
    _ = (RatFunc.X * splitTraceRadicand sigma) ^ (a % q) := by rfl

/-- Odd-prime Kummer-class independence of the two degree-one trace
coordinates.  The norm first forces the two character exponents to agree;
the remaining diagonal character is exactly the residual rational function
handled above. -/
theorem splitTraceBaseCoordinates_mixedPower_ne_oddPrimePower
    (sigma : K) (hsigma : sigma ≠ 0) (hnondegenerate : sigma ≠ 1)
    (q a b : ℕ) (hq : q.Prime) (hqTwo : q ≠ 2)
    (haq : a < q) (hbq : b < q) (hab : a ≠ 0 ∨ b ≠ 0)
    (z : SplitTraceBaseFunctionField K sigma) :
    letI : Fact (Irreducible (splitTraceBaseKummerPolynomial sigma)) :=
      ⟨splitTraceBaseKummerPolynomial_irreducible sigma hsigma⟩
    z ^ q ≠
      (splitTraceBaseU sigma * splitTraceBaseV sigma) ^ a *
        splitTraceBaseV sigma ^ b := by
  let hBaseIrred := splitTraceBaseKummerPolynomial_irreducible sigma hsigma
  let : Fact (Irreducible (splitTraceBaseKummerPolynomial sigma)) := ⟨hBaseIrred⟩
  let baseField := SplitTraceBaseFunctionField K sigma
  let U : baseField := splitTraceBaseU sigma
  let V : baseField := splitTraceBaseV sigma
  have hr : splitTraceRadicand sigma ≠ 0 :=
    splitTraceRadicand_ne_zero sigma hsigma
  have hV : V ≠ 0 := by
    change AdjoinRoot.root (splitTraceBaseKummerPolynomial sigma) ≠ 0
    exact (root_X_pow_sub_C_ne_zero_iff hBaseIrred).mpr hr
  have hU : U ≠ 0 := by
    exact (map_ne_zero_iff _
      (algebraMap (RatFunc K) baseField).injective).mpr RatFunc.X_ne_zero
  have hUV : U * V ≠ 0 := mul_ne_zero hU hV
  have hrightNonzero : (U * V) ^ a * V ^ b ≠ 0 :=
    mul_ne_zero (pow_ne_zero a hUV) (pow_ne_zero b hV)
  intro hpow
  have hz : z ≠ 0 := by
    intro hz
    apply hrightNonzero
    simpa [hz, hq.ne_zero] using hpow.symm
  let : Module.Finite (RatFunc K) baseField :=
    (monic_X_pow_sub_C _ (by norm_num : (2 : ℕ) ≠ 0)).finite_adjoinRoot
  have hnorm := congrArg (Algebra.norm (RatFunc K)) hpow
  rw [map_pow, map_mul, map_pow, map_pow] at hnorm
  have hnormZNe : Algebra.norm (RatFunc K) z ≠ 0 :=
    Algebra.norm_ne_zero_iff.mpr hz
  have hnormUVNe : Algebra.norm (RatFunc K) (U * V) ≠ 0 :=
    Algebra.norm_ne_zero_iff.mpr hUV
  have hnormVNe : Algebra.norm (RatFunc K) V ≠ 0 :=
    Algebra.norm_ne_zero_iff.mpr hV
  have hdegree := congrArg RatFunc.intDegree hnorm
  rw [RatFunc.intDegree_pow _ hnormZNe,
    RatFunc.intDegree_mul (pow_ne_zero a hnormUVNe) (pow_ne_zero b hnormVNe),
    RatFunc.intDegree_pow _ hnormUVNe,
    RatFunc.intDegree_pow _ hnormVNe,
    norm_splitTraceBaseU_mul_V_intDegree sigma hsigma] at hdegree
  have hnormV : Algebra.norm (RatFunc K) V = -splitTraceRadicand sigma := by
    simpa [V, splitTraceBaseV] using norm_splitTraceBaseRoot sigma hsigma
  have hnormVIntDegree :
      (Algebra.norm (RatFunc K) V).intDegree = -1 := by
    rw [hnormV, RatFunc.intDegree_neg, splitTraceRadicand_intDegree sigma hsigma]
  rw [hnormVIntDegree] at hdegree
  have hdiv : (q : ℤ) ∣ (a : ℤ) - (b : ℤ) := by
    refine ⟨(Algebra.norm (RatFunc K) z).intDegree, ?_⟩
    simpa [sub_eq_add_neg, mul_add] using hdegree.symm
  have habEq : a = b := by
    rcases le_total b a with hba | hab
    · have hdivNat : q ∣ a - b := by
        rw [← Int.natCast_dvd_natCast]
        simpa [Nat.cast_sub hba] using hdiv
      have hzero : a - b = 0 :=
        Nat.eq_zero_of_dvd_of_lt hdivNat (lt_of_le_of_lt (Nat.sub_le a b) haq)
      exact Nat.le_antisymm (Nat.sub_eq_zero_iff_le.mp hzero) hba
    · have hdivNeg : (q : ℤ) ∣ (b : ℤ) - (a : ℤ) := by
        simpa only [neg_sub] using (dvd_neg.mpr hdiv)
      have hdivNat : q ∣ b - a := by
        rw [← Int.natCast_dvd_natCast]
        simpa [Nat.cast_sub hab] using hdivNeg
      have hzero : b - a = 0 :=
        Nat.eq_zero_of_dvd_of_lt hdivNat (lt_of_le_of_lt (Nat.sub_le b a) hbq)
      exact Nat.le_antisymm hab (Nat.sub_eq_zero_iff_le.mp hzero)
  subst b
  have haPositive : 0 < a := by
    rcases hab with ha | ha <;> exact Nat.pos_of_ne_zero ha
  have hqNotDvdA : ¬ q ∣ a := Nat.not_dvd_of_pos_of_lt haPositive haq
  have hqNotDvdTwoA : ¬ q ∣ 2 * a := by
    intro h
    rcases hq.dvd_mul.mp h with hqDvdTwo | hqDvdA
    · exact hqTwo ((Nat.dvd_prime Nat.prime_two).mp hqDvdTwo |>.resolve_left hq.ne_one)
    · exact hqNotDvdA hqDvdA
  let residual : RatFunc K := RatFunc.X * splitTraceRadicand sigma
  have hrootSquare : V ^ 2 = algebraMap (RatFunc K) baseField
      (splitTraceRadicand sigma) := by
    change splitTraceBaseV sigma ^ 2 =
      algebraMap (RatFunc K) (SplitTraceBaseFunctionField K sigma)
        (splitTraceRadicand sigma)
    apply sub_eq_zero.mp
    have h := AdjoinRoot.eval₂_root (splitTraceBaseKummerPolynomial sigma)
    rw [splitTraceBaseKummerPolynomial] at h
    simp only [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
      Polynomial.eval₂_C] at h
    rw [← AdjoinRoot.algebraMap_eq] at h
    exact h
  have hcoordinateProduct :
      (U * V) * V = algebraMap (RatFunc K) baseField residual := by
    rw [mul_assoc, ← pow_two, hrootSquare]
    simp [U, residual, baseField, splitTraceBaseU]
  have hpowResidual :
      z ^ q = algebraMap (RatFunc K) baseField (residual ^ a) := by
    calc
      z ^ q = (U * V) ^ a * V ^ a := hpow
      _ = ((U * V) * V) ^ a := by
        simpa [mul_assoc] using (mul_pow (U * V) V a).symm
      _ = (algebraMap (RatFunc K) baseField residual) ^ a := by rw [hcoordinateProduct]
      _ = algebraMap (RatFunc K) baseField (residual ^ a) := by rw [map_pow]
  have hnormResidual := congrArg (Algebra.norm (RatFunc K)) hpowResidual
  rw [map_pow, Algebra.norm_algebraMap,
    splitTraceBaseFunctionField_finrank sigma hsigma] at hnormResidual
  apply splitTrace_X_mul_radicand_pow_ne_primePower_of_not_dvd
    sigma hsigma hnondegenerate q (2 * a) hq hqNotDvdTwoA
      (Algebra.norm (RatFunc K) z)
  simpa [residual, pow_mul, Nat.mul_comm] using hnormResidual

end

end BGS.Markoff
