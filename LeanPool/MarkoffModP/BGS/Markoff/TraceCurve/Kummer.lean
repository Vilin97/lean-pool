/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.Markoff.TraceCurve.Geometry
import Mathlib.FieldTheory.KummerExtension
import Mathlib.FieldTheory.RatFunc.Degree
import Mathlib.RingTheory.Norm.Basic

/-!
# Kummer descent for the split trace power cover

The normalized split trace cover is obtained from the base curve

`u * (1 - u) * v^2 + sigma * u - 1 = 0`

by adjoining `eta` and `xi` with `eta^e = v` and `xi^d = u * v`.  This file makes that
two-stage Kummer construction explicit.  Oddness is imposed because Mathlib's composite-binomial
criterion currently covers odd exponents; coprimality of `d` and `e` is used in the second norm
argument.  Neither hypothesis is hidden in a structure field.
-/

namespace BGS.Markoff

open Polynomial AdjoinRoot

noncomputable section

section ExactPowerSubstitution

variable {L : Type*} [Field L]

/-- The two Kummer root relations really land on the correctly cleared trace-cover polynomial. -/
theorem eval_splitTraceCoverPolynomial_of_powerRootRelations
    (sigma u v xi eta : L) (d e : ℕ)
    (hbase : u * (1 - u) * v ^ 2 + sigma * u - 1 = 0)
    (heta : eta ^ e = v) (hxi : xi ^ d = u * v) :
    MvPolynomial.eval ![xi, eta] (splitTraceCoverPolynomial 1 sigma d e) = 0 := by
  rw [eval_splitTraceCoverPolynomial]
  have hetaTwo : eta ^ (2 * e) = (eta ^ e) ^ 2 := by
    simpa [Nat.mul_comm] using (pow_mul eta e 2)
  have hxiTwo : xi ^ (2 * d) = (xi ^ d) ^ 2 := by
    simpa [Nat.mul_comm] using (pow_mul xi d 2)
  rw [hetaTwo, hxiTwo, heta, hxi]
  linear_combination v * hbase

end ExactPowerSubstitution

section RationalBase

variable {K : Type*} [Field K]

/-- Numerator of the quadratic radicand on the rational `u`-line. -/
def splitTraceRadicandNumerator (sigma : K) : K[X] :=
  1 - C sigma * X

/-- Denominator of the quadratic radicand on the rational `u`-line. -/
def splitTraceRadicandDenominator : K[X] :=
  X * (1 - X)

/-- The base trace curve has function equation `v^2 = splitTraceRadicand sigma`. -/
def splitTraceRadicand (sigma : K) : RatFunc K :=
  algebraMap K[X] (RatFunc K) (splitTraceRadicandNumerator sigma) /
    algebraMap K[X] (RatFunc K) splitTraceRadicandDenominator

lemma splitTraceRadicandNumerator_natDegree (sigma : K) (hsigma : sigma ≠ 0) :
    (splitTraceRadicandNumerator sigma).natDegree = 1 := by
  rw [← Polynomial.degree_eq_iff_natDegree_eq_of_pos (by norm_num : 0 < 1)]
  rw [splitTraceRadicandNumerator]
  compute_degree!

lemma splitTraceRadicandDenominator_natDegree :
    (splitTraceRadicandDenominator : K[X]).natDegree = 2 := by
  rw [← Polynomial.degree_eq_iff_natDegree_eq_of_pos (by norm_num : 0 < 2)]
  rw [splitTraceRadicandDenominator]
  compute_degree!

lemma splitTraceRadicandNumerator_ne_zero (sigma : K) (hsigma : sigma ≠ 0) :
    splitTraceRadicandNumerator sigma ≠ 0 := by
  intro h
  have := congrArg Polynomial.natDegree h
  simp [splitTraceRadicandNumerator_natDegree sigma hsigma] at this

lemma splitTraceRadicandDenominator_ne_zero :
    (splitTraceRadicandDenominator : K[X]) ≠ 0 := by
  intro h
  have := congrArg Polynomial.natDegree h
  simp [splitTraceRadicandDenominator_natDegree (K := K)] at this

lemma splitTraceRadicand_ne_zero (sigma : K) (hsigma : sigma ≠ 0) :
    splitTraceRadicand sigma ≠ 0 := by
  apply div_ne_zero
  · exact (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr
      (splitTraceRadicandNumerator_ne_zero sigma hsigma)
  · exact (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr
      (splitTraceRadicandDenominator_ne_zero (K := K))

lemma splitTraceRadicand_intDegree (sigma : K) (hsigma : sigma ≠ 0) :
    (splitTraceRadicand sigma).intDegree = -1 := by
  rw [splitTraceRadicand, RatFunc.intDegree_div]
  · rw [RatFunc.intDegree_polynomial, RatFunc.intDegree_polynomial,
      splitTraceRadicandNumerator_natDegree sigma hsigma,
      splitTraceRadicandDenominator_natDegree]
    norm_num
  · exact (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr
      (splitTraceRadicandNumerator_ne_zero sigma hsigma)
  · exact (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr
      (splitTraceRadicandDenominator_ne_zero (K := K))

/-- The rational radicand satisfies the cleared base trace equation before adjoining its square
root. -/
lemma splitTraceRadicand_equation (sigma : K) :
    RatFunc.X * (1 - RatFunc.X) * splitTraceRadicand sigma +
      RatFunc.C sigma * RatFunc.X - 1 = 0 := by
  have hOneNeX : (1 : RatFunc K) ≠ RatFunc.X := by
    intro h
    have hDegree := congrArg RatFunc.intDegree h
    norm_num at hDegree
  have hDenominator :
      RatFunc.X * (1 - RatFunc.X) ≠ (0 : RatFunc K) :=
    mul_ne_zero RatFunc.X_ne_zero (sub_ne_zero.mpr hOneNeX)
  simp only [splitTraceRadicand, splitTraceRadicandNumerator,
    splitTraceRadicandDenominator, map_sub, map_one, map_mul,
    RatFunc.algebraMap_C, RatFunc.algebraMap_X]
  field_simp [hDenominator]
  ring_nf
  simp [RatFunc.X_ne_zero]

lemma RatFunc.intDegree_pow (z : RatFunc K) (hz : z ≠ 0) (n : ℕ) :
    (z ^ n).intDegree = (n : ℤ) * z.intDegree := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, RatFunc.intDegree_mul (pow_ne_zero n hz) hz, ih]
      push_cast
      ring

/-- An element of rational-function degree not divisible by `q` cannot be a `q`-th power. -/
lemma RatFunc.pow_ne_of_not_dvd_intDegree
    (a : RatFunc K) (ha : a ≠ 0) (q : ℕ) (hdegree : ¬ (q : ℤ) ∣ a.intDegree)
    (z : RatFunc K) :
    z ^ q ≠ a := by
  intro hpow
  by_cases hq : q = 0
  · subst q
    apply hdegree
    rw [← hpow]
    simp
  have hz : z ≠ 0 := by
    intro hz
    apply ha
    simpa [hz, hq] using hpow.symm
  apply hdegree
  refine ⟨z.intDegree, ?_⟩
  rw [← hpow, RatFunc.intDegree_pow z hz q]

/-- The monic quadratic defining the base function field. -/
def splitTraceBaseKummerPolynomial (sigma : K) : Polynomial (RatFunc K) :=
  X ^ 2 - C (splitTraceRadicand sigma)

theorem splitTraceBaseKummerPolynomial_irreducible
    (sigma : K) (hsigma : sigma ≠ 0) :
    Irreducible (splitTraceBaseKummerPolynomial sigma) := by
  rw [splitTraceBaseKummerPolynomial]
  apply X_pow_sub_C_irreducible_of_prime Nat.prime_two
  intro z
  apply RatFunc.pow_ne_of_not_dvd_intDegree
    (splitTraceRadicand sigma) (splitTraceRadicand_ne_zero sigma hsigma)
  rw [splitTraceRadicand_intDegree sigma hsigma]
  norm_num

/-- The quadratic base root has norm `-splitTraceRadicand sigma`. -/
lemma norm_splitTraceBaseRoot
    (sigma : K) (hsigma : sigma ≠ 0) :
    letI : Fact (Irreducible (splitTraceBaseKummerPolynomial sigma)) :=
      ⟨splitTraceBaseKummerPolynomial_irreducible sigma hsigma⟩
    Algebra.norm (RatFunc K)
      (AdjoinRoot.root (splitTraceBaseKummerPolynomial sigma)) =
        -splitTraceRadicand sigma := by
  let hIrred := splitTraceBaseKummerPolynomial_irreducible sigma hsigma
  letI : Fact (Irreducible (splitTraceBaseKummerPolynomial sigma)) := ⟨hIrred⟩
  let pb := AdjoinRoot.powerBasis hIrred.ne_zero
  have hdim : pb.dim = 2 := by
    change (splitTraceBaseKummerPolynomial sigma).natDegree = 2
    simp [splitTraceBaseKummerPolynomial]
  change Algebra.norm (RatFunc K) pb.gen = -splitTraceRadicand sigma
  rw [Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly, hdim,
    AdjoinRoot.minpoly_powerBasis_gen_of_monic]
  · simp [pb, splitTraceBaseKummerPolynomial]
  · exact monic_X_pow_sub_C _ (by norm_num)

/-- A prime-power root of the base coordinate `v` cannot already lie in the quadratic base
function field.  The obstruction is the rational-function degree `-1` of its norm. -/
theorem splitTraceBaseRoot_not_primePower
    (sigma : K) (hsigma : sigma ≠ 0) (q : ℕ) (hq : q.Prime)
    (z : AdjoinRoot (splitTraceBaseKummerPolynomial sigma)) :
    z ^ q ≠ AdjoinRoot.root (splitTraceBaseKummerPolynomial sigma) := by
  let hIrred := splitTraceBaseKummerPolynomial_irreducible sigma hsigma
  letI : Fact (Irreducible (splitTraceBaseKummerPolynomial sigma)) := ⟨hIrred⟩
  intro hpow
  have hnorm := congrArg (Algebra.norm (RatFunc K)) hpow
  rw [map_pow, norm_splitTraceBaseRoot sigma hsigma] at hnorm
  have hRadicandNegNe : -splitTraceRadicand sigma ≠ 0 :=
    neg_ne_zero.mpr (splitTraceRadicand_ne_zero sigma hsigma)
  have hNotDvd : ¬ (q : ℤ) ∣ (-splitTraceRadicand sigma).intDegree := by
    rw [RatFunc.intDegree_neg, splitTraceRadicand_intDegree sigma hsigma]
    intro hdvd
    rw [Int.natCast_dvd] at hdvd
    exact hq.ne_one (Nat.eq_one_of_dvd_one hdvd)
  exact RatFunc.pow_ne_of_not_dvd_intDegree
    (-splitTraceRadicand sigma) hRadicandNegNe q hNotDvd
    (Algebra.norm (RatFunc K) z) hnorm

/-- For every positive odd `e`, adjoining an `e`-th root of the base coordinate `v` is a genuine
degree-`e` Kummer extension. -/
theorem splitTraceEtaKummerPolynomial_irreducible
    (sigma : K) (hsigma : sigma ≠ 0) (e : ℕ) (heOdd : Odd e) :
    letI : Fact (Irreducible (splitTraceBaseKummerPolynomial sigma)) :=
      ⟨splitTraceBaseKummerPolynomial_irreducible sigma hsigma⟩
    Irreducible
      (X ^ e - C (AdjoinRoot.root (splitTraceBaseKummerPolynomial sigma))) := by
  let hBaseIrred := splitTraceBaseKummerPolynomial_irreducible sigma hsigma
  letI : Fact (Irreducible (splitTraceBaseKummerPolynomial sigma)) := ⟨hBaseIrred⟩
  apply X_pow_sub_C_irreducible_of_odd heOdd
  intro q hq _ z
  exact splitTraceBaseRoot_not_primePower sigma hsigma q hq z

/-- The rational parameter `u`, embedded in the quadratic base function field. -/
def splitTraceBaseU (sigma : K) :
    AdjoinRoot (splitTraceBaseKummerPolynomial sigma) :=
  algebraMap (RatFunc K) _ RatFunc.X

/-- The quadratic coordinate `v` in the base function field. -/
def splitTraceBaseV (sigma : K) :
    AdjoinRoot (splitTraceBaseKummerPolynomial sigma) :=
  AdjoinRoot.root (splitTraceBaseKummerPolynomial sigma)

/-- The two base coordinates satisfy the birational trace equation inside the quadratic function
field. -/
lemma splitTraceBaseU_V_equation
    (sigma : K) (hsigma : sigma ≠ 0) :
    letI : Fact (Irreducible (splitTraceBaseKummerPolynomial sigma)) :=
      ⟨splitTraceBaseKummerPolynomial_irreducible sigma hsigma⟩
    splitTraceBaseU sigma * (1 - splitTraceBaseU sigma) * splitTraceBaseV sigma ^ 2 +
      algebraMap (RatFunc K) (AdjoinRoot (splitTraceBaseKummerPolynomial sigma))
        (RatFunc.C sigma) * splitTraceBaseU sigma - 1 = 0 := by
  let hBaseIrred := splitTraceBaseKummerPolynomial_irreducible sigma hsigma
  letI : Fact (Irreducible (splitTraceBaseKummerPolynomial sigma)) := ⟨hBaseIrred⟩
  have hRootSquare : splitTraceBaseV sigma ^ 2 =
      algebraMap (RatFunc K) (AdjoinRoot (splitTraceBaseKummerPolynomial sigma))
        (splitTraceRadicand sigma) := by
    apply sub_eq_zero.mp
    have h := AdjoinRoot.eval₂_root (splitTraceBaseKummerPolynomial sigma)
    rw [splitTraceBaseKummerPolynomial] at h
    simp only [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
      Polynomial.eval₂_C] at h
    rw [← AdjoinRoot.algebraMap_eq] at h
    exact h
  have hMapped := congrArg
    (algebraMap (RatFunc K) (AdjoinRoot (splitTraceBaseKummerPolynomial sigma)))
    (splitTraceRadicand_equation sigma)
  simp only [map_add, map_sub, map_mul, map_one, map_zero] at hMapped
  rw [splitTraceBaseU, hRootSquare]
  exact hMapped

lemma splitTraceBaseFunctionField_finrank
    (sigma : K) (hsigma : sigma ≠ 0) :
    letI : Fact (Irreducible (splitTraceBaseKummerPolynomial sigma)) :=
      ⟨splitTraceBaseKummerPolynomial_irreducible sigma hsigma⟩
    Module.finrank (RatFunc K)
      (AdjoinRoot (splitTraceBaseKummerPolynomial sigma)) = 2 := by
  let hIrred := splitTraceBaseKummerPolynomial_irreducible sigma hsigma
  letI : Fact (Irreducible (splitTraceBaseKummerPolynomial sigma)) := ⟨hIrred⟩
  rw [PowerBasis.finrank (AdjoinRoot.powerBasis hIrred.ne_zero)]
  change (splitTraceBaseKummerPolynomial sigma).natDegree = 2
  simp [splitTraceBaseKummerPolynomial]

/-- The norm of `u * v` has rational-function degree one.  This is the second independent divisor
obstruction used after adjoining the `e`-th root of `v`. -/
lemma norm_splitTraceBaseU_mul_V_intDegree
    (sigma : K) (hsigma : sigma ≠ 0) :
    letI : Fact (Irreducible (splitTraceBaseKummerPolynomial sigma)) :=
      ⟨splitTraceBaseKummerPolynomial_irreducible sigma hsigma⟩
    (Algebra.norm (RatFunc K) (splitTraceBaseU sigma * splitTraceBaseV sigma)).intDegree = 1 := by
  let hIrred := splitTraceBaseKummerPolynomial_irreducible sigma hsigma
  letI : Fact (Irreducible (splitTraceBaseKummerPolynomial sigma)) := ⟨hIrred⟩
  have hNorm : Algebra.norm (RatFunc K) (splitTraceBaseU sigma * splitTraceBaseV sigma) =
      RatFunc.X ^ 2 * (-splitTraceRadicand sigma) := by
    rw [map_mul]
    rw [splitTraceBaseU, Algebra.norm_algebraMap,
      splitTraceBaseFunctionField_finrank sigma hsigma]
    rw [splitTraceBaseV, norm_splitTraceBaseRoot sigma hsigma]
  rw [hNorm, RatFunc.intDegree_mul]
  · rw [RatFunc.intDegree_pow RatFunc.X RatFunc.X_ne_zero,
      RatFunc.intDegree_X, RatFunc.intDegree_neg,
      splitTraceRadicand_intDegree sigma hsigma]
    norm_num
  · exact pow_ne_zero 2 RatFunc.X_ne_zero
  · exact neg_ne_zero.mpr (splitTraceRadicand_ne_zero sigma hsigma)

/-- The first Kummer polynomial, adjoining `eta` with `eta^e = v`. -/
def splitTraceEtaKummerPolynomial (sigma : K) (e : ℕ) :
    Polynomial (AdjoinRoot (splitTraceBaseKummerPolynomial sigma)) :=
  X ^ e - C (splitTraceBaseV sigma)

lemma splitTraceEtaKummerPolynomial_irreducible'
    (sigma : K) (hsigma : sigma ≠ 0) (e : ℕ) (heOdd : Odd e) :
    letI : Fact (Irreducible (splitTraceBaseKummerPolynomial sigma)) :=
      ⟨splitTraceBaseKummerPolynomial_irreducible sigma hsigma⟩
    Irreducible (splitTraceEtaKummerPolynomial sigma e) := by
  simpa [splitTraceEtaKummerPolynomial, splitTraceBaseV] using
    splitTraceEtaKummerPolynomial_irreducible sigma hsigma e heOdd

lemma splitTraceEtaFunctionField_finrank
    (sigma : K) (hsigma : sigma ≠ 0) (e : ℕ) (heOdd : Odd e) :
    letI : Fact (Irreducible (splitTraceBaseKummerPolynomial sigma)) :=
      ⟨splitTraceBaseKummerPolynomial_irreducible sigma hsigma⟩
    letI : Fact (Irreducible (splitTraceEtaKummerPolynomial sigma e)) :=
      ⟨splitTraceEtaKummerPolynomial_irreducible' sigma hsigma e heOdd⟩
    Module.finrank (AdjoinRoot (splitTraceBaseKummerPolynomial sigma))
      (AdjoinRoot (splitTraceEtaKummerPolynomial sigma e)) = e := by
  let hBaseIrred := splitTraceBaseKummerPolynomial_irreducible sigma hsigma
  letI : Fact (Irreducible (splitTraceBaseKummerPolynomial sigma)) := ⟨hBaseIrred⟩
  let hEtaIrred := splitTraceEtaKummerPolynomial_irreducible' sigma hsigma e heOdd
  letI : Fact (Irreducible (splitTraceEtaKummerPolynomial sigma e)) := ⟨hEtaIrred⟩
  rw [PowerBasis.finrank (AdjoinRoot.powerBasis hEtaIrred.ne_zero)]
  change (splitTraceEtaKummerPolynomial sigma e).natDegree = e
  simp [splitTraceEtaKummerPolynomial]

/-- The second Kummer radicand, corresponding to `xi^d = u * v`. -/
def splitTraceXiRadicand (sigma : K) (e : ℕ) :
    AdjoinRoot (splitTraceEtaKummerPolynomial sigma e) :=
  algebraMap (AdjoinRoot (splitTraceBaseKummerPolynomial sigma)) _
    (splitTraceBaseU sigma * splitTraceBaseV sigma)

/-- After adjoining the `e`-th root of `v`, the element `u*v` is not a `q`-th power whenever
`q` is prime and coprime to `e`.  The proof takes two successive norms; their rational-function
degree forces `q` to divide `e`, a contradiction. -/
theorem splitTraceXiRadicand_not_primePower
    (sigma : K) (hsigma : sigma ≠ 0) (e : ℕ) (heOdd : Odd e)
    (q : ℕ) (hq : q.Prime) (hqe : ¬ q ∣ e)
    (z : AdjoinRoot (splitTraceEtaKummerPolynomial sigma e)) :
    z ^ q ≠ splitTraceXiRadicand sigma e := by
  let hBaseIrred := splitTraceBaseKummerPolynomial_irreducible sigma hsigma
  letI : Fact (Irreducible (splitTraceBaseKummerPolynomial sigma)) := ⟨hBaseIrred⟩
  let hEtaIrred := splitTraceEtaKummerPolynomial_irreducible' sigma hsigma e heOdd
  letI : Fact (Irreducible (splitTraceEtaKummerPolynomial sigma e)) := ⟨hEtaIrred⟩
  letI : Module.Finite (RatFunc K)
      (AdjoinRoot (splitTraceBaseKummerPolynomial sigma)) :=
    (monic_X_pow_sub_C _ (by norm_num : (2 : ℕ) ≠ 0)).finite_adjoinRoot
  have he : e ≠ 0 := by
    rintro rfl
    simp at heOdd
  letI : Module.Finite (AdjoinRoot (splitTraceBaseKummerPolynomial sigma))
      (AdjoinRoot (splitTraceEtaKummerPolynomial sigma e)) :=
    (monic_X_pow_sub_C _ he).finite_adjoinRoot
  have hBaseV : splitTraceBaseV sigma ≠ 0 := by
    change AdjoinRoot.root (splitTraceBaseKummerPolynomial sigma) ≠ 0
    have hroot := (root_X_pow_sub_C_ne_zero_iff hBaseIrred).mpr
      (splitTraceRadicand_ne_zero sigma hsigma)
    exact hroot
  have hBaseU : splitTraceBaseU sigma ≠ 0 := by
    exact (map_ne_zero_iff _
      (algebraMap (RatFunc K)
        (AdjoinRoot (splitTraceBaseKummerPolynomial sigma))).injective).mpr RatFunc.X_ne_zero
  have hBaseUV : splitTraceBaseU sigma * splitTraceBaseV sigma ≠ 0 :=
    mul_ne_zero hBaseU hBaseV
  have hXiRadicand : splitTraceXiRadicand sigma e ≠ 0 := by
    exact (map_ne_zero_iff _
      (algebraMap (AdjoinRoot (splitTraceBaseKummerPolynomial sigma))
        (AdjoinRoot (splitTraceEtaKummerPolynomial sigma e))).injective).mpr hBaseUV
  intro hpow
  have hz : z ≠ 0 := by
    intro hz
    apply hXiRadicand
    simpa [hz, hq.ne_zero] using hpow.symm
  have hFirstNorm := congrArg
    (Algebra.norm (AdjoinRoot (splitTraceBaseKummerPolynomial sigma))) hpow
  rw [map_pow, splitTraceXiRadicand, Algebra.norm_algebraMap,
    splitTraceEtaFunctionField_finrank sigma hsigma e heOdd] at hFirstNorm
  have hSecondNorm := congrArg (Algebra.norm (RatFunc K)) hFirstNorm
  rw [map_pow, map_pow] at hSecondNorm
  have hNormZNe :
      Algebra.norm (AdjoinRoot (splitTraceBaseKummerPolynomial sigma)) z ≠ 0 :=
    Algebra.norm_ne_zero_iff.mpr hz
  have hDoubleNormZNe :
      Algebra.norm (RatFunc K)
        (Algebra.norm (AdjoinRoot (splitTraceBaseKummerPolynomial sigma)) z) ≠ 0 :=
    Algebra.norm_ne_zero_iff.mpr hNormZNe
  have hNormBaseUVNe :
      Algebra.norm (RatFunc K) (splitTraceBaseU sigma * splitTraceBaseV sigma) ≠ 0 :=
    Algebra.norm_ne_zero_iff.mpr hBaseUV
  have hDegree := congrArg RatFunc.intDegree hSecondNorm
  rw [RatFunc.intDegree_pow _ hDoubleNormZNe,
    RatFunc.intDegree_pow _ hNormBaseUVNe,
    norm_splitTraceBaseU_mul_V_intDegree sigma hsigma] at hDegree
  apply hqe
  rw [← Int.natCast_dvd_natCast]
  exact ⟨_, by simpa using hDegree.symm⟩

/-- The second Kummer polynomial, adjoining `xi` with `xi^d = u*v`. -/
def splitTraceXiKummerPolynomial (sigma : K) (e d : ℕ) :
    Polynomial (AdjoinRoot (splitTraceEtaKummerPolynomial sigma e)) :=
  X ^ d - C (splitTraceXiRadicand sigma e)

/-- The three fields in the explicit Kummer tower. -/
abbrev SplitTraceBaseFunctionField (K : Type*) [Field K] (sigma : K) :=
  AdjoinRoot (splitTraceBaseKummerPolynomial sigma)

abbrev SplitTraceEtaFunctionField (K : Type*) [Field K] (sigma : K) (e : ℕ) :=
  AdjoinRoot (splitTraceEtaKummerPolynomial sigma e)

abbrev SplitTraceXiFunctionField (K : Type*) [Field K] (sigma : K) (e d : ℕ) :=
  AdjoinRoot (splitTraceXiKummerPolynomial sigma e d)

/-- Embed a base-function-field element through both Kummer stages. -/
def splitTraceBaseElementInXiField (sigma : K) (e d : ℕ)
    (a : SplitTraceBaseFunctionField K sigma) :
    SplitTraceXiFunctionField K sigma e d :=
  algebraMap (SplitTraceEtaFunctionField K sigma e) _
    (algebraMap (SplitTraceBaseFunctionField K sigma) _ a)

/-- The canonical `eta` root, embedded into the top Kummer field. -/
def splitTraceEtaRootInXiField (sigma : K) (e d : ℕ) :
    SplitTraceXiFunctionField K sigma e d :=
  algebraMap (SplitTraceEtaFunctionField K sigma e) _
    (AdjoinRoot.root (splitTraceEtaKummerPolynomial sigma e))

/-- The canonical `xi` root in the top Kummer field. -/
def splitTraceXiRoot (sigma : K) (e d : ℕ) :
    SplitTraceXiFunctionField K sigma e d :=
  AdjoinRoot.root (splitTraceXiKummerPolynomial sigma e d)

/-- For positive odd coprime exponents, the second Kummer polynomial is irreducible.  This is the
connectedness step that the printed translate argument does not supply. -/
theorem splitTraceXiKummerPolynomial_irreducible
    (sigma : K) (hsigma : sigma ≠ 0) (e d : ℕ)
    (heOdd : Odd e) (hdOdd : Odd d) (hde : d.Coprime e) :
    letI : Fact (Irreducible (splitTraceBaseKummerPolynomial sigma)) :=
      ⟨splitTraceBaseKummerPolynomial_irreducible sigma hsigma⟩
    letI : Fact (Irreducible (splitTraceEtaKummerPolynomial sigma e)) :=
      ⟨splitTraceEtaKummerPolynomial_irreducible' sigma hsigma e heOdd⟩
    Irreducible (splitTraceXiKummerPolynomial sigma e d) := by
  let hBaseIrred := splitTraceBaseKummerPolynomial_irreducible sigma hsigma
  letI : Fact (Irreducible (splitTraceBaseKummerPolynomial sigma)) := ⟨hBaseIrred⟩
  let hEtaIrred := splitTraceEtaKummerPolynomial_irreducible' sigma hsigma e heOdd
  letI : Fact (Irreducible (splitTraceEtaKummerPolynomial sigma e)) := ⟨hEtaIrred⟩
  rw [splitTraceXiKummerPolynomial]
  apply X_pow_sub_C_irreducible_of_odd hdOdd
  intro q hq hqd z
  have hqe : ¬ q ∣ e :=
    (hq.coprime_iff_not_dvd.mp (Nat.Coprime.of_dvd_left hqd hde))
  exact splitTraceXiRadicand_not_primePower sigma hsigma e heOdd q hq hqe z

/-- The canonical roots of the proved Kummer tower lie on the exact cleared trace-cover
polynomial.  This connects the function-field construction back to `splitTraceCoverPolynomial`. -/
theorem splitTraceKummerTower_roots_on_cover
    (sigma : K) (hsigma : sigma ≠ 0)
    (e d : ℕ) (heOdd : Odd e) (hdOdd : Odd d) (hde : d.Coprime e) :
    letI : Fact (Irreducible (splitTraceBaseKummerPolynomial sigma)) :=
      ⟨splitTraceBaseKummerPolynomial_irreducible sigma hsigma⟩
    letI : Fact (Irreducible (splitTraceEtaKummerPolynomial sigma e)) :=
      ⟨splitTraceEtaKummerPolynomial_irreducible' sigma hsigma e heOdd⟩
    letI : Fact (Irreducible (splitTraceXiKummerPolynomial sigma e d)) :=
      ⟨splitTraceXiKummerPolynomial_irreducible sigma hsigma e d heOdd hdOdd hde⟩
    MvPolynomial.eval
      ![splitTraceXiRoot sigma e d, splitTraceEtaRootInXiField sigma e d]
      (splitTraceCoverPolynomial 1
        (splitTraceBaseElementInXiField sigma e d
          (algebraMap (RatFunc K) (SplitTraceBaseFunctionField K sigma) (RatFunc.C sigma)))
        d e) = 0 := by
  let hBaseIrred := splitTraceBaseKummerPolynomial_irreducible sigma hsigma
  letI : Fact (Irreducible (splitTraceBaseKummerPolynomial sigma)) := ⟨hBaseIrred⟩
  let hEtaIrred := splitTraceEtaKummerPolynomial_irreducible' sigma hsigma e heOdd
  letI : Fact (Irreducible (splitTraceEtaKummerPolynomial sigma e)) := ⟨hEtaIrred⟩
  let hXiIrred :=
    splitTraceXiKummerPolynomial_irreducible sigma hsigma e d heOdd hdOdd hde
  letI : Fact (Irreducible (splitTraceXiKummerPolynomial sigma e d)) := ⟨hXiIrred⟩
  let baseToXi : SplitTraceBaseFunctionField K sigma →+*
      SplitTraceXiFunctionField K sigma e d :=
    (algebraMap (SplitTraceEtaFunctionField K sigma e)
      (SplitTraceXiFunctionField K sigma e d)).comp
      (algebraMap (SplitTraceBaseFunctionField K sigma)
        (SplitTraceEtaFunctionField K sigma e))
  have hBase := splitTraceBaseU_V_equation sigma hsigma
  have hBaseTop := congrArg baseToXi hBase
  simp only [map_add, map_sub, map_mul, map_pow, map_one, map_zero] at hBaseTop
  have hEtaRoot :
      (AdjoinRoot.root (splitTraceEtaKummerPolynomial sigma e)) ^ e =
        algebraMap (SplitTraceBaseFunctionField K sigma)
          (SplitTraceEtaFunctionField K sigma e) (splitTraceBaseV sigma) := by
    apply sub_eq_zero.mp
    have h := AdjoinRoot.eval₂_root (splitTraceEtaKummerPolynomial sigma e)
    rw [splitTraceEtaKummerPolynomial] at h
    simp only [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
      Polynomial.eval₂_C] at h
    rw [← AdjoinRoot.algebraMap_eq] at h
    exact h
  have hEtaTop := congrArg
    (algebraMap (SplitTraceEtaFunctionField K sigma e)
      (SplitTraceXiFunctionField K sigma e d)) hEtaRoot
  simp only [map_pow] at hEtaTop
  have hXiRoot :
      (splitTraceXiRoot sigma e d) ^ d =
        algebraMap (SplitTraceEtaFunctionField K sigma e)
          (SplitTraceXiFunctionField K sigma e d) (splitTraceXiRadicand sigma e) := by
    apply sub_eq_zero.mp
    have h := AdjoinRoot.eval₂_root (splitTraceXiKummerPolynomial sigma e d)
    rw [splitTraceXiKummerPolynomial] at h
    simp only [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
      Polynomial.eval₂_C] at h
    rw [← AdjoinRoot.algebraMap_eq] at h
    exact h
  apply eval_splitTraceCoverPolynomial_of_powerRootRelations
    (splitTraceBaseElementInXiField sigma e d
      (algebraMap (RatFunc K) (SplitTraceBaseFunctionField K sigma) (RatFunc.C sigma)))
    (splitTraceBaseElementInXiField sigma e d (splitTraceBaseU sigma))
    (splitTraceBaseElementInXiField sigma e d (splitTraceBaseV sigma))
    (splitTraceXiRoot sigma e d) (splitTraceEtaRootInXiField sigma e d) d e
  · simpa [baseToXi, splitTraceBaseElementInXiField] using hBaseTop
  · simpa [splitTraceEtaRootInXiField, splitTraceBaseElementInXiField, baseToXi] using hEtaTop
  · simpa [splitTraceXiRadicand, splitTraceBaseElementInXiField, baseToXi,
      splitTraceXiRoot] using hXiRoot

lemma splitTraceXiFunctionField_finrank
    (sigma : K) (hsigma : sigma ≠ 0) (e d : ℕ)
    (heOdd : Odd e) (hdOdd : Odd d) (hde : d.Coprime e) :
    letI : Fact (Irreducible (splitTraceBaseKummerPolynomial sigma)) :=
      ⟨splitTraceBaseKummerPolynomial_irreducible sigma hsigma⟩
    letI : Fact (Irreducible (splitTraceEtaKummerPolynomial sigma e)) :=
      ⟨splitTraceEtaKummerPolynomial_irreducible' sigma hsigma e heOdd⟩
    letI : Fact (Irreducible (splitTraceXiKummerPolynomial sigma e d)) :=
      ⟨splitTraceXiKummerPolynomial_irreducible sigma hsigma e d heOdd hdOdd hde⟩
    Module.finrank (AdjoinRoot (splitTraceEtaKummerPolynomial sigma e))
      (AdjoinRoot (splitTraceXiKummerPolynomial sigma e d)) = d := by
  let hBaseIrred := splitTraceBaseKummerPolynomial_irreducible sigma hsigma
  letI : Fact (Irreducible (splitTraceBaseKummerPolynomial sigma)) := ⟨hBaseIrred⟩
  let hEtaIrred := splitTraceEtaKummerPolynomial_irreducible' sigma hsigma e heOdd
  letI : Fact (Irreducible (splitTraceEtaKummerPolynomial sigma e)) := ⟨hEtaIrred⟩
  let hXiIrred :=
    splitTraceXiKummerPolynomial_irreducible sigma hsigma e d heOdd hdOdd hde
  letI : Fact (Irreducible (splitTraceXiKummerPolynomial sigma e d)) := ⟨hXiIrred⟩
  rw [PowerBasis.finrank (AdjoinRoot.powerBasis hXiIrred.ne_zero)]
  change (splitTraceXiKummerPolynomial sigma e d).natDegree = d
  simp [splitTraceXiKummerPolynomial]

/-- The iterated Kummer function-field tower for the odd, coprime split trace power cover is a
domain.  All three irreducibility facts are constructed from the explicit norm-degree arguments
above; none is assumed as a field or typeclass parameter.  This theorem does not yet identify the
tower with a localization or tensor base change of the affine coordinate ring. -/
theorem splitTraceOddCoprimeKummerTower_isDomain
    (sigma : K) (hsigma : sigma ≠ 0)
    (e d : ℕ) (heOdd : Odd e) (hdOdd : Odd d) (hde : d.Coprime e) :
    letI : Fact (Irreducible (splitTraceBaseKummerPolynomial sigma)) :=
      ⟨splitTraceBaseKummerPolynomial_irreducible sigma hsigma⟩
    letI : Fact (Irreducible (splitTraceEtaKummerPolynomial sigma e)) :=
      ⟨splitTraceEtaKummerPolynomial_irreducible' sigma hsigma e heOdd⟩
    IsDomain (AdjoinRoot (splitTraceXiKummerPolynomial sigma e d)) := by
  let hBaseIrred := splitTraceBaseKummerPolynomial_irreducible sigma hsigma
  letI : Fact (Irreducible (splitTraceBaseKummerPolynomial sigma)) := ⟨hBaseIrred⟩
  let hEtaIrred := splitTraceEtaKummerPolynomial_irreducible' sigma hsigma e heOdd
  letI : Fact (Irreducible (splitTraceEtaKummerPolynomial sigma e)) := ⟨hEtaIrred⟩
  let hXiIrred :=
    splitTraceXiKummerPolynomial_irreducible sigma hsigma e d heOdd hdOdd hde
  letI : Fact (Irreducible (splitTraceXiKummerPolynomial sigma e d)) := ⟨hXiIrred⟩
  exact AdjoinRoot.isDomain_of_prime hXiIrred.prime

/-- Reconstructing the same explicit Kummer tower after an arbitrary extension of the constant
field again gives a domain.  The remaining scheme-level wall is to identify this reconstructed
tower with the localization of the tensor-product base change of the original coordinate ring. -/
theorem splitTraceOddCoprimeKummerTower_isDomain_afterConstantExtension
    {L : Type*} [Field L] (phi : K →+* L)
    (sigma : K) (hsigma : sigma ≠ 0)
    (e d : ℕ) (heOdd : Odd e) (hdOdd : Odd d) (hde : d.Coprime e) :
    letI : Fact (Irreducible (splitTraceBaseKummerPolynomial (phi sigma))) :=
      ⟨splitTraceBaseKummerPolynomial_irreducible (phi sigma)
        ((map_ne_zero_iff phi phi.injective).mpr hsigma)⟩
    letI : Fact (Irreducible (splitTraceEtaKummerPolynomial (phi sigma) e)) :=
      ⟨splitTraceEtaKummerPolynomial_irreducible' (phi sigma)
        ((map_ne_zero_iff phi phi.injective).mpr hsigma) e heOdd⟩
    IsDomain (AdjoinRoot (splitTraceXiKummerPolynomial (phi sigma) e d)) := by
  exact splitTraceOddCoprimeKummerTower_isDomain
    (phi sigma) ((map_ne_zero_iff phi phi.injective).mpr hsigma)
    e d heOdd hdOdd hde

end RationalBase

end

end BGS.Markoff
