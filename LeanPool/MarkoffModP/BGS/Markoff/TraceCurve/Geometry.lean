/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.Markoff.Core.RotationTorus
import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-!
# Split trace curves: an exact polynomial model and the first irreducibility wall

The source equation is a Laurent equation on a two-dimensional torus.  We keep that torus
equation separate from its cleared affine polynomial, because boundary monomials are units on the
torus but not in an affine polynomial ring.

For the degree-one cover, the birational change `u = x / y` turns the normalized equation into

`u * (1 - u) * y^2 + sigma * u - 1 = 0`.

The latter polynomial is Eisenstein at `sigma * u - 1` when `sigma` is neither zero nor one.  This
gives an irreducibility proof that survives every field extension.  The higher power-cover descent
required by the paper is deliberately not encoded in this theorem: irreducibility of the quotient
curve does not imply irreducibility after adjoining the two power roots.
-/

namespace BGS.Markoff

open Polynomial

section ExactTraceCurve

variable {K : Type*} [Field K]

/-- A weighted split-torus trace.  The paper's orbit coordinates have this form. -/
def weightedSplitTorusTrace (alpha beta : K) (w : Kˣ) : K :=
  alpha * (w : K) + beta * (w⁻¹ : Kˣ)

@[simp]
theorem weightedSplitTorusTrace_one_one (w : Kˣ) :
    weightedSplitTorusTrace 1 1 w = splitTorusTrace w := by
  simp [weightedSplitTorusTrace, splitTorusTrace]

/-- The exact split trace-cover equation from source equation (31). -/
def SplitTraceCurveEquation (alpha beta : K) (d e : ℕ) (x y : Kˣ) : Prop :=
  weightedSplitTorusTrace alpha beta (y ^ e) = splitTorusTrace (x ^ d)

/-- The affine polynomial obtained by multiplying the Laurent equation by `x^d * y^e`.

Variable `0` is `x` and variable `1` is `y`.  In particular, the third term contains the factor
`y^e`; this is the factor missing from the displayed polynomial on source line 749.
-/
noncomputable def splitTraceCoverPolynomial (alpha beta : K) (d e : ℕ) :
    MvPolynomial (Fin 2) K :=
  MvPolynomial.C alpha * MvPolynomial.X 0 ^ d * MvPolynomial.X 1 ^ (2 * e) +
    MvPolynomial.C beta * MvPolynomial.X 0 ^ d -
    MvPolynomial.X 0 ^ (2 * d) * MvPolynomial.X 1 ^ e -
    MvPolynomial.X 1 ^ e

theorem eval_splitTraceCoverPolynomial (alpha beta : K) (d e : ℕ) (x y : K) :
    MvPolynomial.eval ![x, y] (splitTraceCoverPolynomial alpha beta d e) =
      alpha * x ^ d * y ^ (2 * e) + beta * x ^ d - x ^ (2 * d) * y ^ e - y ^ e := by
  simp [splitTraceCoverPolynomial]

/-- On the torus, vanishing of the cleared polynomial is exactly the source Laurent equation.
No affine boundary point is silently added to this statement. -/
theorem eval_splitTraceCoverPolynomial_eq_zero_iff
    (alpha beta : K) (d e : ℕ) (x y : Kˣ) :
    MvPolynomial.eval ![(x : K), (y : K)] (splitTraceCoverPolynomial alpha beta d e) = 0 ↔
      SplitTraceCurveEquation alpha beta d e x y := by
  rw [eval_splitTraceCoverPolynomial]
  unfold SplitTraceCurveEquation weightedSplitTorusTrace splitTorusTrace
  simp only [Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val]
  change alpha * (x : K) ^ d * (y : K) ^ (2 * e) + beta * (x : K) ^ d -
      (x : K) ^ (2 * d) * (y : K) ^ e - (y : K) ^ e = 0 ↔
    alpha * (y : K) ^ e + beta * ((y : K) ^ e)⁻¹ =
      (x : K) ^ d + ((x : K) ^ d)⁻¹
  field_simp
  constructor <;> intro h <;> linear_combination h

/-- At the excluded parameter `alpha * beta = 1`, the normalized cleared polynomial visibly
factors.  This proves that the paper's nondegeneracy condition is mathematically necessary. -/
theorem splitTraceCoverPolynomial_degenerate_factorization (d e : ℕ) :
    splitTraceCoverPolynomial (1 : K) 1 d e =
      (MvPolynomial.X 1 ^ e - MvPolynomial.X 0 ^ d) *
        (MvPolynomial.X 0 ^ d * MvPolynomial.X 1 ^ e - 1) := by
  simp only [splitTraceCoverPolynomial, MvPolynomial.C_1]
  ring

/-- The birational degree-one equation obtained from the normalized cleared equation by setting
`u = x / y` and removing the invertible factor `y`. -/
def normalizedSplitTraceBirationalEquation (sigma u y : K) : K :=
  u * (1 - u) * y ^ 2 + sigma * u - 1

theorem normalizedSplitTrace_birational_change (sigma x y : K) (hy : y ≠ 0) :
    x * y ^ 2 + sigma * x - x ^ 2 * y - y =
      y * normalizedSplitTraceBirationalEquation sigma (x / y) y := by
  change x * y ^ 2 + sigma * x - x ^ 2 * y - y =
    y * ((x / y) * (1 - x / y) * y ^ 2 + sigma * (x / y) - 1)
  field_simp [hy]
  ring

end ExactTraceCurve

section BirationalIrreducibility

variable {K : Type*} [Field K]

/-- The coefficient of `y^2` in the birational degree-one trace equation. -/
noncomputable def normalizedSplitTraceLeadingCoefficient : K[X] :=
  X * (1 - X)

/-- The prime used in the Eisenstein proof. -/
noncomputable def normalizedSplitTraceEisensteinPrime (sigma : K) : K[X] :=
  C sigma * X - 1

/-- The birational degree-one trace equation, as a polynomial in `y` over `K[u]`. -/
noncomputable def normalizedSplitTraceBirationalPolynomial (sigma : K) : Polynomial K[X] :=
  C normalizedSplitTraceLeadingCoefficient * X ^ 2 +
    C (normalizedSplitTraceEisensteinPrime sigma)

@[simp]
theorem eval_normalizedSplitTraceBirationalPolynomial (sigma u y : K) :
    ((normalizedSplitTraceBirationalPolynomial sigma).eval (C y)).eval u =
      normalizedSplitTraceBirationalEquation sigma u y := by
  simp [normalizedSplitTraceBirationalPolynomial, normalizedSplitTraceLeadingCoefficient,
    normalizedSplitTraceEisensteinPrime, normalizedSplitTraceBirationalEquation]
  ring

lemma normalizedSplitTraceEisensteinPrime_irreducible (sigma : K) (hsigma : sigma ≠ 0) :
    Irreducible (normalizedSplitTraceEisensteinPrime sigma) := by
  simpa [normalizedSplitTraceEisensteinPrime, sub_eq_add_neg] using
    (Polynomial.irreducible_C_mul_X_add_C hsigma
      ((isUnit_neg_one : IsUnit (-1 : K)).isRelPrime_right))

lemma normalizedSplitTraceEisensteinPrime_not_dvd_leading
    (sigma : K) (hsigma : sigma ≠ 0) (hsigmaOne : sigma ≠ 1) :
    ¬ normalizedSplitTraceEisensteinPrime sigma ∣
      (normalizedSplitTraceLeadingCoefficient : K[X]) := by
  intro hdvd
  have hdvdEval := map_dvd (Polynomial.evalRingHom (sigma⁻¹)) hdvd
  have hinv : sigma⁻¹ ≠ 0 := inv_ne_zero hsigma
  have hinvOne : sigma⁻¹ ≠ 1 := inv_ne_one.mpr hsigmaOne
  have hzero : 1 - sigma⁻¹ = 0 := by
    simpa [normalizedSplitTraceEisensteinPrime, normalizedSplitTraceLeadingCoefficient,
      hsigma, hinv] using hdvdEval
  exact (sub_ne_zero.mpr (Ne.symm hinvOne)) hzero

lemma normalizedSplitTraceBirationalPolynomial_natDegree (sigma : K) :
    (normalizedSplitTraceBirationalPolynomial sigma).natDegree = 2 := by
  have hOneSubX : (1 - X : K[X]) ≠ 0 := by
    intro h
    have hval : (1 : K) = 0 := by
      simpa using congrArg (Polynomial.eval (0 : K)) h
    exact one_ne_zero hval
  have hLeading : (normalizedSplitTraceLeadingCoefficient : K[X]) ≠ 0 :=
    mul_ne_zero Polynomial.X_ne_zero hOneSubX
  simp [normalizedSplitTraceBirationalPolynomial, hLeading]

lemma normalizedSplitTraceBirationalPolynomial_isPrimitive
    (sigma : K) (hsigma : sigma ≠ 0) (hsigmaOne : sigma ≠ 1) :
    (normalizedSplitTraceBirationalPolynomial sigma).IsPrimitive := by
  rw [Polynomial.isPrimitive_iff_isUnit_of_C_dvd]
  intro r hr
  have hcoeff := (Polynomial.C_dvd_iff_dvd_coeff r
    (normalizedSplitTraceBirationalPolynomial sigma)).mp hr
  have hrPrime : r ∣ normalizedSplitTraceEisensteinPrime sigma := by
    simpa [normalizedSplitTraceBirationalPolynomial] using hcoeff 0
  have hrLeading : r ∣ (normalizedSplitTraceLeadingCoefficient : K[X]) := by
    simpa [normalizedSplitTraceBirationalPolynomial] using hcoeff 2
  exact ((normalizedSplitTraceEisensteinPrime_irreducible sigma hsigma).coprime_iff_not_dvd.mpr
    (normalizedSplitTraceEisensteinPrime_not_dvd_leading sigma hsigma hsigmaOne)).isUnit_of_dvd'
      hrPrime hrLeading

lemma normalizedSplitTraceBirationalPolynomial_isEisenstein
    (sigma : K) (hsigma : sigma ≠ 0) (hsigmaOne : sigma ≠ 1) :
    (normalizedSplitTraceBirationalPolynomial sigma).IsEisensteinAt
      (Ideal.span {normalizedSplitTraceEisensteinPrime sigma}) := by
  have hPrimeIrred := normalizedSplitTraceEisensteinPrime_irreducible sigma hsigma
  have hDegree := normalizedSplitTraceBirationalPolynomial_natDegree sigma
  have hLeadingCoeff :
      (normalizedSplitTraceBirationalPolynomial sigma).leadingCoeff =
        (normalizedSplitTraceLeadingCoefficient : K[X]) := by
    rw [leadingCoeff, hDegree]
    simp [normalizedSplitTraceBirationalPolynomial]
  have hCoeffZero :
      (normalizedSplitTraceBirationalPolynomial sigma).coeff 0 =
        normalizedSplitTraceEisensteinPrime sigma := by
    simp [normalizedSplitTraceBirationalPolynomial]
  refine {
    leading := ?_
    mem := ?_
    notMem := ?_ }
  · rw [Ideal.mem_span_singleton]
    rw [hLeadingCoeff]
    exact normalizedSplitTraceEisensteinPrime_not_dvd_leading sigma hsigma hsigmaOne
  · intro n hn
    rw [hDegree] at hn
    interval_cases n <;>
      simp [normalizedSplitTraceBirationalPolynomial]
  · rw [hCoeffZero, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    intro hdvd
    have hDegreePrime : (normalizedSplitTraceEisensteinPrime sigma).natDegree = 1 := by
      rw [← Polynomial.degree_eq_iff_natDegree_eq_of_pos (by norm_num : 0 < 1)]
      rw [normalizedSplitTraceEisensteinPrime]
      compute_degree!
    have hle := Polynomial.natDegree_le_of_dvd hdvd hPrimeIrred.ne_zero
    norm_num [Polynomial.natDegree_pow, hDegreePrime] at hle

/-- The degree-one birational trace polynomial is irreducible over every field, under exactly the
two nondegeneracy conditions used by the Eisenstein argument. -/
theorem normalizedSplitTraceBirationalPolynomial_irreducible
    (sigma : K) (hsigma : sigma ≠ 0) (hsigmaOne : sigma ≠ 1) :
    Irreducible (normalizedSplitTraceBirationalPolynomial sigma) := by
  have hPrimeIrred := normalizedSplitTraceEisensteinPrime_irreducible sigma hsigma
  have hIdealPrime : (Ideal.span {normalizedSplitTraceEisensteinPrime sigma}).IsPrime :=
    (Ideal.span_singleton_prime hPrimeIrred.ne_zero).mpr hPrimeIrred.prime
  apply (normalizedSplitTraceBirationalPolynomial_isEisenstein sigma hsigma hsigmaOne).irreducible
    hIdealPrime
    (normalizedSplitTraceBirationalPolynomial_isPrimitive sigma hsigma hsigmaOne)
  rw [normalizedSplitTraceBirationalPolynomial_natDegree]
  norm_num

theorem map_normalizedSplitTraceBirationalPolynomial
    {L : Type*} [Field L] (phi : K →+* L) (sigma : K) :
    (normalizedSplitTraceBirationalPolynomial sigma).map (Polynomial.mapRingHom phi) =
      normalizedSplitTraceBirationalPolynomial (phi sigma) := by
  simp [normalizedSplitTraceBirationalPolynomial, normalizedSplitTraceLeadingCoefficient,
    normalizedSplitTraceEisensteinPrime]

/-- Universal scalar-extension irreducibility.  In particular, taking an algebraic closure gives
absolute irreducibility of this explicit birational degree-one model. -/
theorem normalizedSplitTraceBirationalPolynomial_irreducible_after_baseChange
    {L : Type*} [Field L] (phi : K →+* L) (sigma : K)
    (hsigma : sigma ≠ 0) (hsigmaOne : sigma ≠ 1) :
    Irreducible
      ((normalizedSplitTraceBirationalPolynomial sigma).map (Polynomial.mapRingHom phi)) := by
  rw [map_normalizedSplitTraceBirationalPolynomial]
  apply normalizedSplitTraceBirationalPolynomial_irreducible
  · exact (map_ne_zero_iff phi phi.injective).mpr hsigma
  · intro h
    apply hsigmaOne
    apply phi.injective
    simpa using h

end BirationalIrreducibility

end BGS.Markoff
