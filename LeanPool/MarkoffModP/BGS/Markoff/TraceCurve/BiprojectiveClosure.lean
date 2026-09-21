/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.Markoff.TraceCurve.Boundary
import Mathlib.FieldTheory.KummerExtension

/-!
# Explicit biprojective closure of the trace cover

This uses `Option K` as the standard affine chart plus the point at infinity of `P^1(K)`.
It controls the raw closure in `P^1 × P^1`; it does not identify that generally singular closure
with its normalization.
-/

namespace BGS.Markoff

open Polynomial

noncomputable section

variable {K : Type*} [Field K]

/-- The bidegree-`(2d,2e)` homogenization of the cleared trace-cover polynomial. -/
def splitTraceBihomogeneousValue (alpha beta : K) (d e : ℕ)
    (X₀ X₁ Y₀ Y₁ : K) : K :=
  alpha * X₀ ^ d * X₁ ^ d * Y₀ ^ (2 * e) +
    beta * X₀ ^ d * X₁ ^ d * Y₁ ^ (2 * e) -
    X₀ ^ (2 * d) * Y₀ ^ e * Y₁ ^ e -
    X₁ ^ (2 * d) * Y₀ ^ e * Y₁ ^ e

/-- Canonical homogeneous coordinates for the affine chart and infinity of `P^1(K)`. -/
def projectiveLineChartCoordinates : Option K → K × K
  | some x => (x, 1)
  | none => (1, 0)

/-- Evaluation of the raw biprojective closure on canonical chart representatives. -/
def splitTraceBiprojectiveValue (alpha beta : K) (d e : ℕ)
    (z : Option K × Option K) : K :=
  let X := projectiveLineChartCoordinates z.1
  let Y := projectiveLineChartCoordinates z.2
  splitTraceBihomogeneousValue alpha beta d e X.1 X.2 Y.1 Y.2

theorem splitTraceBiprojectiveValue_affine (alpha beta : K) (d e : ℕ) (x y : K) :
    splitTraceBiprojectiveValue alpha beta d e (some x, some y) =
      MvPolynomial.eval ![x, y] (splitTraceCoverPolynomial alpha beta d e) := by
  rw [eval_splitTraceCoverPolynomial]
  simp [splitTraceBiprojectiveValue, projectiveLineChartCoordinates,
    splitTraceBihomogeneousValue]

theorem splitTraceBiprojectiveValue_infinity_affine
    (alpha beta : K) (d e : ℕ) (hd : 0 < d) (y : K) :
    splitTraceBiprojectiveValue alpha beta d e (none, some y) = -(y ^ e) := by
  have hd0 : d ≠ 0 := hd.ne'
  have h2d0 : 2 * d ≠ 0 := by omega
  simp [splitTraceBiprojectiveValue, projectiveLineChartCoordinates,
    splitTraceBihomogeneousValue, hd0, h2d0]

theorem splitTraceBiprojectiveValue_affine_infinity
    (alpha beta : K) (d e : ℕ) (he : 0 < e) (x : K) :
    splitTraceBiprojectiveValue alpha beta d e (some x, none) = alpha * x ^ d := by
  have he0 : e ≠ 0 := he.ne'
  have h2e0 : 2 * e ≠ 0 := by omega
  simp [splitTraceBiprojectiveValue, projectiveLineChartCoordinates,
    splitTraceBihomogeneousValue, he0, h2e0]

theorem splitTraceBiprojectiveValue_infinity_infinity
    (alpha beta : K) (d e : ℕ) (hd : 0 < d) (he : 0 < e) :
    splitTraceBiprojectiveValue alpha beta d e (none, none) = 0 := by
  have hd0 : d ≠ 0 := hd.ne'
  have he0 : e ≠ 0 := he.ne'
  have h2d0 : 2 * d ≠ 0 := by omega
  have h2e0 : 2 * e ≠ 0 := by omega
  simp [splitTraceBiprojectiveValue, projectiveLineChartCoordinates,
    splitTraceBihomogeneousValue, hd0, he0, h2d0, h2e0]

/-- The same bihomogeneous equation as a four-variable polynomial, ordered as
`X₀, X₁, Y₀, Y₁`. -/
def splitTraceBihomogeneousPolynomial (alpha beta : K) (d e : ℕ) :
    MvPolynomial (Fin 4) K :=
  MvPolynomial.C alpha * MvPolynomial.X 0 ^ d * MvPolynomial.X 1 ^ d *
      MvPolynomial.X 2 ^ (2 * e) +
    MvPolynomial.C beta * MvPolynomial.X 0 ^ d * MvPolynomial.X 1 ^ d *
      MvPolynomial.X 3 ^ (2 * e) -
    MvPolynomial.X 0 ^ (2 * d) * MvPolynomial.X 2 ^ e * MvPolynomial.X 3 ^ e -
    MvPolynomial.X 1 ^ (2 * d) * MvPolynomial.X 2 ^ e * MvPolynomial.X 3 ^ e

theorem eval_splitTraceBihomogeneousPolynomial
    (alpha beta : K) (d e : ℕ) (X₀ X₁ Y₀ Y₁ : K) :
    MvPolynomial.eval ![X₀, X₁, Y₀, Y₁]
      (splitTraceBihomogeneousPolynomial alpha beta d e) =
      splitTraceBihomogeneousValue alpha beta d e X₀ X₁ Y₀ Y₁ := by
  simp [splitTraceBihomogeneousPolynomial, splitTraceBihomogeneousValue]

/-! ### The four standard biprojective charts -/

/-- The finite-finite chart is the original cleared affine polynomial. -/
theorem splitTraceBihomogeneousValue_zero_zero_chart
    (alpha beta : K) (d e : ℕ) (x y : K) :
    splitTraceBihomogeneousValue alpha beta d e x 1 y 1 =
      MvPolynomial.eval ![x, y] (splitTraceCoverPolynomial alpha beta d e) := by
  rw [eval_splitTraceCoverPolynomial]
  simp [splitTraceBihomogeneousValue]

/-- Inverting the first projective coordinate leaves the affine polynomial unchanged. -/
theorem splitTraceBihomogeneousValue_infinity_zero_chart
    (alpha beta : K) (d e : ℕ) (x y : K) :
    splitTraceBihomogeneousValue alpha beta d e 1 x y 1 =
      MvPolynomial.eval ![x, y] (splitTraceCoverPolynomial alpha beta d e) := by
  rw [eval_splitTraceCoverPolynomial]
  simp [splitTraceBihomogeneousValue]
  ring

/-- Inverting the second projective coordinate swaps the two trace weights. -/
theorem splitTraceBihomogeneousValue_zero_infinity_chart
    (alpha beta : K) (d e : ℕ) (x y : K) :
    splitTraceBihomogeneousValue alpha beta d e x 1 1 y =
      MvPolynomial.eval ![x, y] (splitTraceCoverPolynomial beta alpha d e) := by
  rw [eval_splitTraceCoverPolynomial]
  simp [splitTraceBihomogeneousValue]
  ring

/-- Inverting both coordinates again gives the affine polynomial with swapped weights. -/
theorem splitTraceBihomogeneousValue_infinity_infinity_chart
    (alpha beta : K) (d e : ℕ) (x y : K) :
    splitTraceBihomogeneousValue alpha beta d e 1 x 1 y =
      MvPolynomial.eval ![x, y] (splitTraceCoverPolynomial beta alpha d e) := by
  rw [eval_splitTraceCoverPolynomial]
  simp [splitTraceBihomogeneousValue]
  ring

/-- Torus points of the weighted trace cover, as a finite-type-independent subtype. -/
abbrev WeightedSplitTraceTorusCurve (alpha beta : K) (d e : ℕ) :=
  {z : Kˣ × Kˣ // SplitTraceCurveEquation alpha beta d e z.1 z.2}

/-- First-coordinate inversion is a transition automorphism of the torus curve. -/
theorem splitTraceCurveEquation_left_inv_iff
    (alpha beta : K) (d e : ℕ) (x y : Kˣ) :
    SplitTraceCurveEquation alpha beta d e x⁻¹ y ↔
      SplitTraceCurveEquation alpha beta d e x y := by
  simp [SplitTraceCurveEquation, splitTorusTrace]
  ring_nf

/-- Second-coordinate inversion is the transition map to the chart with swapped weights. -/
theorem splitTraceCurveEquation_right_inv_iff_swapped
    (alpha beta : K) (d e : ℕ) (x y : Kˣ) :
    SplitTraceCurveEquation alpha beta d e x y⁻¹ ↔
      SplitTraceCurveEquation beta alpha d e x y := by
  simp [SplitTraceCurveEquation, weightedSplitTorusTrace, splitTorusTrace]
  constructor <;> intro h <;> linear_combination h

/-- The involutive first-coordinate transition on torus points. -/
def weightedSplitTraceTorusCurveLeftInversionEquiv
    (alpha beta : K) (d e : ℕ) :
    WeightedSplitTraceTorusCurve alpha beta d e ≃
      WeightedSplitTraceTorusCurve alpha beta d e where
  toFun z := ⟨(z.1.1⁻¹, z.1.2),
    (splitTraceCurveEquation_left_inv_iff alpha beta d e z.1.1 z.1.2).2 z.2⟩
  invFun z := ⟨(z.1.1⁻¹, z.1.2),
    (splitTraceCurveEquation_left_inv_iff alpha beta d e z.1.1 z.1.2).2 z.2⟩
  left_inv z := by ext <;> simp
  right_inv z := by ext <;> simp

/-- The involutive second-coordinate transition between the two weight orderings. -/
def weightedSplitTraceTorusCurveRightInversionEquiv
    (alpha beta : K) (d e : ℕ) :
    WeightedSplitTraceTorusCurve alpha beta d e ≃
      WeightedSplitTraceTorusCurve beta alpha d e where
  toFun z := ⟨(z.1.1, z.1.2⁻¹),
    (splitTraceCurveEquation_right_inv_iff_swapped
      beta alpha d e z.1.1 z.1.2).2 z.2⟩
  invFun z := ⟨(z.1.1, z.1.2⁻¹),
    (splitTraceCurveEquation_right_inv_iff_swapped
      alpha beta d e z.1.1 z.1.2).2 z.2⟩
  left_inv z := by ext <;> simp
  right_inv z := by ext <;> simp

/-- For covering degrees greater than one, the corner `(∞,∞)` of the raw closure has zero
formal gradient.  Thus the raw closure cannot be substituted for its normalization in the
Hasse--Weil step. -/
theorem splitTraceBihomogeneousPolynomial_pderiv_eval_infinity_infinity
    (alpha beta : K) (d e : ℕ) (hd : 1 < d) (he : 1 < e) (i : Fin 4) :
    MvPolynomial.eval ![(1 : K), 0, 1, 0]
      (MvPolynomial.pderiv i (splitTraceBihomogeneousPolynomial alpha beta d e)) = 0 := by
  have hd0 : d ≠ 0 := by omega
  have hd1 : d - 1 ≠ 0 := by omega
  have he0 : e ≠ 0 := by omega
  have he1 : e - 1 ≠ 0 := by omega
  have h2d0 : 2 * d ≠ 0 := by omega
  have h2d1 : 2 * d - 1 ≠ 0 := by omega
  have h2e0 : 2 * e ≠ 0 := by omega
  have h2e1 : 2 * e - 1 ≠ 0 := by omega
  fin_cases i <;>
    simp [splitTraceBihomogeneousPolynomial, hd0, hd1, he0, he1,
      h2d0, h2d1, h2e0, h2e1]

/-! ### Weighted local equations at the projective corners -/

/-- In the `(∞,∞)` chart, weighted scaling `x ↦ T^e x`, `y ↦ T^d y` separates
the binomial of weighted degree `de` from the terms of weighted degree `3de`. -/
theorem splitTraceBihomogeneousValue_infinity_infinity_weightedScaling
    (alpha beta : K) (d e : ℕ) (T x y : K) :
    splitTraceBihomogeneousValue alpha beta d e
        1 (T ^ e * x) 1 (T ^ d * y) =
      T ^ (d * e) * (alpha * x ^ d - y ^ e) +
        T ^ (3 * (d * e)) *
          (beta * x ^ d * y ^ (2 * e) - x ^ (2 * d) * y ^ e) := by
  simp only [splitTraceBihomogeneousValue, one_pow, one_mul, mul_one, mul_pow]
  ring_nf

/-- The `(0,∞)` corner has the same weighted local equation as `(∞,∞)`. -/
theorem splitTraceBihomogeneousValue_zero_infinity_weightedScaling
    (alpha beta : K) (d e : ℕ) (T x y : K) :
    splitTraceBihomogeneousValue alpha beta d e
        (T ^ e * x) 1 1 (T ^ d * y) =
      T ^ (d * e) * (alpha * x ^ d - y ^ e) +
        T ^ (3 * (d * e)) *
          (beta * x ^ d * y ^ (2 * e) - x ^ (2 * d) * y ^ e) := by
  simp only [splitTraceBihomogeneousValue, one_pow, one_mul, mul_one, mul_pow]
  ring_nf

/-- In the `(∞,0)` chart the leading coefficient is the second weight `beta`. -/
theorem splitTraceBihomogeneousValue_infinity_zero_weightedScaling
    (alpha beta : K) (d e : ℕ) (T x y : K) :
    splitTraceBihomogeneousValue alpha beta d e
        1 (T ^ e * x) (T ^ d * y) 1 =
      T ^ (d * e) * (beta * x ^ d - y ^ e) +
        T ^ (3 * (d * e)) *
          (alpha * x ^ d * y ^ (2 * e) - x ^ (2 * d) * y ^ e) := by
  simp only [splitTraceBihomogeneousValue, one_pow, one_mul, mul_one, mul_pow]
  ring_nf

/-- The `(0,0)` corner has the same weighted local equation as `(∞,0)`. -/
theorem splitTraceBihomogeneousValue_zero_zero_weightedScaling
    (alpha beta : K) (d e : ℕ) (T x y : K) :
    splitTraceBihomogeneousValue alpha beta d e
        (T ^ e * x) 1 (T ^ d * y) 1 =
      T ^ (d * e) * (beta * x ^ d - y ^ e) +
        T ^ (3 * (d * e)) *
          (alpha * x ^ d * y ^ (2 * e) - x ^ (2 * d) * y ^ e) := by
  simp only [splitTraceBihomogeneousValue, one_pow, one_mul, mul_one, mul_pow]
  ring_nf

/-- The common weighted initial polynomial at a corner, with coefficient `gamma`. -/
noncomputable def splitTraceCornerInitialPolynomial (gamma : K) (d e : ℕ) :
    MvPolynomial (Fin 2) K :=
  MvPolynomial.C gamma * MvPolynomial.X 0 ^ d - MvPolynomial.X 1 ^ e

/-- If both exponents have a common factor `q` and the leading coefficient is a `q`-th power,
the weighted initial polynomial has the corresponding binomial factor.  Over an algebraic closure
the coefficient condition is automatic. -/
theorem splitTraceCornerInitialPolynomial_factor_of_commonScaling
    (a : K) (q d e : ℕ) :
    MvPolynomial.C a * MvPolynomial.X 0 ^ d - MvPolynomial.X 1 ^ e ∣
      splitTraceCornerInitialPolynomial (a ^ q) (q * d) (q * e) := by
  change MvPolynomial.C a * MvPolynomial.X 0 ^ d - MvPolynomial.X 1 ^ e ∣
    MvPolynomial.C (a ^ q) * MvPolynomial.X 0 ^ (q * d) -
      MvPolynomial.X 1 ^ (q * e)
  rw [map_pow]
  rw [show MvPolynomial.X (0 : Fin 2) ^ (q * d) =
      (MvPolynomial.X 0 ^ d) ^ q by rw [Nat.mul_comm, pow_mul]]
  rw [show MvPolynomial.X (1 : Fin 2) ^ (q * e) =
      (MvPolynomial.X 1 ^ e) ^ q by rw [Nat.mul_comm, pow_mul]]
  rw [← mul_pow]
  exact sub_dvd_pow_sub_pow
    (MvPolynomial.C a * MvPolynomial.X (0 : Fin 2) ^ d)
    (MvPolynomial.X (1 : Fin 2) ^ e) q

/-- Over an algebraically closed field every positive common scaling of the corner exponents
produces an explicit binomial factor of the weighted initial polynomial. -/
theorem exists_splitTraceCornerInitialPolynomial_factor_of_commonScaling
    [IsAlgClosed K] (gamma : K) (q d e : ℕ) (hq : 0 < q) :
    ∃ a : K, a ^ q = gamma ∧
      MvPolynomial.C a * MvPolynomial.X 0 ^ d - MvPolynomial.X 1 ^ e ∣
        splitTraceCornerInitialPolynomial gamma (q * d) (q * e) := by
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_pow_nat_eq gamma hq
  refine ⟨a, ha, ?_⟩
  rw [← ha]
  exact splitTraceCornerInitialPolynomial_factor_of_commonScaling a q d e

/-- With a primitive `q`-th root of unity, the corner initial polynomial factors into exactly
the expected `q` binomials.  This is the algebraic input for counting branches above a corner;
lifting these initial factors to the normalization remains a separate theorem. -/
theorem splitTraceCornerInitialPolynomial_eq_prod_factors
    (gamma a zeta : K) (q d e : ℕ) (hq : 0 < q)
    (ha : a ^ q = gamma) (hzeta : IsPrimitiveRoot zeta q) :
    splitTraceCornerInitialPolynomial gamma (q * d) (q * e) =
      ∏ i ∈ Finset.range q,
        (MvPolynomial.C a * MvPolynomial.X 0 ^ d -
          MvPolynomial.C (zeta ^ i) * MvPolynomial.X 1 ^ e) := by
  let R := MvPolynomial (Fin 2) K
  let A : R := MvPolynomial.C a * MvPolynomial.X 0 ^ d
  let B : R := MvPolynomial.X 1 ^ e
  have hzetaR : IsPrimitiveRoot (MvPolynomial.C zeta : R) q :=
    hzeta.map_of_injective (MvPolynomial.C_injective (Fin 2) K)
  have hpoly := X_pow_sub_C_eq_prod hzetaR hq (show B ^ q = B ^ q from rfl)
  have heval := congrArg (Polynomial.eval A) hpoly
  simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_C, Polynomial.eval_prod] at heval
  rw [splitTraceCornerInitialPolynomial, ← ha]
  change MvPolynomial.C (a ^ q) * MvPolynomial.X 0 ^ (q * d) -
      MvPolynomial.X 1 ^ (q * e) = _
  rw [map_pow]
  rw [show MvPolynomial.X (0 : Fin 2) ^ (q * d) =
      (MvPolynomial.X 0 ^ d) ^ q by rw [Nat.mul_comm, pow_mul]]
  rw [show MvPolynomial.X (1 : Fin 2) ^ (q * e) =
      (MvPolynomial.X 1 ^ e) ^ q by rw [Nat.mul_comm, pow_mul]]
  rw [← mul_pow]
  rw [heval]
  simp [A, B, R, map_pow]

/-- The `q` binomials in the preceding factorization are pairwise distinct. -/
theorem splitTraceCornerInitialPolynomial_factors_injective
    (a zeta : K) (q d e : ℕ) (hzeta : IsPrimitiveRoot zeta q) :
    Function.Injective (fun i : Fin q =>
      (MvPolynomial.C a : MvPolynomial (Fin 2) K) * MvPolynomial.X 0 ^ d -
        MvPolynomial.C (zeta ^ (i : ℕ)) * MvPolynomial.X 1 ^ e) := by
  intro i j hij
  have hvalue := congrArg
    (fun P : MvPolynomial (Fin 2) K => MvPolynomial.eval ![(1 : K), 1] P) hij
  simp at hvalue
  apply Fin.ext
  exact hzeta.pow_inj i.isLt j.isLt hvalue

/-- For the actual exponents, the number of distinct factors in the weighted initial form is
controlled by `gcd d e`.  The characteristic hypothesis is automatic in the endgame because both
covering degrees are prime to the field characteristic. -/
theorem exists_splitTraceCornerInitialPolynomial_gcd_factorization
    [IsAlgClosed K] (gamma : K) (d e : ℕ) (hd : 0 < d)
    (hgChar : ((Nat.gcd d e : ℕ) : K) ≠ 0) :
    ∃ a zeta : K,
      a ^ Nat.gcd d e = gamma ∧ IsPrimitiveRoot zeta (Nat.gcd d e) ∧
      splitTraceCornerInitialPolynomial gamma d e =
        ∏ i ∈ Finset.range (Nat.gcd d e),
          (MvPolynomial.C a * MvPolynomial.X 0 ^ (d / Nat.gcd d e) -
            MvPolynomial.C (zeta ^ i) * MvPolynomial.X 1 ^ (e / Nat.gcd d e)) := by
  let q := Nat.gcd d e
  change ∃ a zeta : K,
    a ^ q = gamma ∧ IsPrimitiveRoot zeta q ∧
    splitTraceCornerInitialPolynomial gamma d e =
      ∏ i ∈ Finset.range q,
        (MvPolynomial.C a * MvPolynomial.X 0 ^ (d / q) -
          MvPolynomial.C (zeta ^ i) * MvPolynomial.X 1 ^ (e / q))
  have hq : 0 < q := Nat.gcd_pos_of_pos_left e hd
  letI : NeZero q := ⟨hq.ne'⟩
  letI : NeZero (q : K) := ⟨by simpa [q] using hgChar⟩
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_pow_nat_eq gamma hq
  obtain ⟨zeta, hzeta⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K q
  have hqd : q ∣ d := Nat.gcd_dvd_left d e
  have hqe : q ∣ e := Nat.gcd_dvd_right d e
  have hdEq : q * (d / q) = d := Nat.mul_div_cancel' hqd
  have heEq : q * (e / q) = e := Nat.mul_div_cancel' hqe
  refine ⟨a, zeta, ha, hzeta, ?_⟩
  calc
    splitTraceCornerInitialPolynomial gamma d e =
        splitTraceCornerInitialPolynomial gamma (q * (d / q)) (q * (e / q)) := by
      rw [hdEq, heEq]
    _ = _ := splitTraceCornerInitialPolynomial_eq_prod_factors
      gamma a zeta q (d / q) (e / q) hq ha hzeta

section Finite

variable (K : Type*) [Field K] [Fintype K] [DecidableEq K]

/-- Rational points of the raw closure in the canonical `P^1 × P^1` charts. -/
def splitTraceBiprojectiveZeros (alpha beta : K) (d e : ℕ) :
    Finset (Option K × Option K) :=
  Finset.univ.filter fun z => splitTraceBiprojectiveValue alpha beta d e z = 0

/-- Points of the raw closure outside the affine `A^1 × A^1` chart. -/
def splitTraceBiprojectiveAffineBoundary (alpha beta : K) (d e : ℕ) :
    Finset (Option K × Option K) :=
  (splitTraceBiprojectiveZeros K alpha beta d e).filter fun z =>
    z.1.isNone || z.2.isNone

/-- The three raw boundary points outside `A^1 × A^1`.  Together with the affine origin these
are the four boundary points of the torus chart. -/
def splitTraceBiprojectiveBoundaryCorners : Finset (Option K × Option K) :=
  {(none, some 0), (none, none), (some 0, none)}

theorem splitTraceBiprojectiveAffineBoundary_eq_corners
    (alpha beta : K) (d e : ℕ) (hd : 0 < d) (he : 0 < e)
    (halpha : alpha ≠ 0) :
    splitTraceBiprojectiveAffineBoundary K alpha beta d e =
      splitTraceBiprojectiveBoundaryCorners K := by
  ext z
  rcases z with ⟨x, y⟩
  cases x with
  | none =>
      cases y with
      | none =>
          simp [splitTraceBiprojectiveAffineBoundary, splitTraceBiprojectiveZeros,
            splitTraceBiprojectiveBoundaryCorners,
            splitTraceBiprojectiveValue_infinity_infinity alpha beta d e hd he]
      | some y =>
          simp [splitTraceBiprojectiveAffineBoundary, splitTraceBiprojectiveZeros,
            splitTraceBiprojectiveBoundaryCorners,
            splitTraceBiprojectiveValue_infinity_affine alpha beta d e hd y,
            pow_eq_zero_iff he.ne']
  | some x =>
      cases y with
      | none =>
          simp [splitTraceBiprojectiveAffineBoundary, splitTraceBiprojectiveZeros,
            splitTraceBiprojectiveBoundaryCorners,
            splitTraceBiprojectiveValue_affine_infinity alpha beta d e he x,
            halpha, pow_eq_zero_iff hd.ne']
      | some y =>
          simp [splitTraceBiprojectiveAffineBoundary, splitTraceBiprojectiveZeros,
            splitTraceBiprojectiveBoundaryCorners]

theorem splitTraceBiprojectiveAffineBoundary_card
    (alpha beta : K) (d e : ℕ) (hd : 0 < d) (he : 0 < e)
    (halpha : alpha ≠ 0) :
    (splitTraceBiprojectiveAffineBoundary K alpha beta d e).card = 3 := by
  rw [splitTraceBiprojectiveAffineBoundary_eq_corners K alpha beta d e hd he halpha]
  simp [splitTraceBiprojectiveBoundaryCorners]

/-- The denominator-cleared affine zero set is exactly the affine chart of the raw
biprojective closure. -/
def affineSplitTraceCoverZerosEquivBiprojectiveOffBoundary
    (alpha beta : K) (d e : ℕ) :
    ↥(affineSplitTraceCoverZeros K alpha beta d e) ≃
      ↥(splitTraceBiprojectiveZeros K alpha beta d e \
        splitTraceBiprojectiveAffineBoundary K alpha beta d e) :=
  Equiv.ofBijective
    (fun z =>
      ⟨(some z.1.1, some z.1.2), by
        rw [Finset.mem_sdiff]
        constructor
        · rw [splitTraceBiprojectiveZeros, Finset.mem_filter]
          refine ⟨Finset.mem_univ _, ?_⟩
          rw [splitTraceBiprojectiveValue_affine]
          exact (mem_affineSplitTraceCoverZeros_iff K alpha beta d e z.1).mp z.2
        · simp [splitTraceBiprojectiveAffineBoundary]⟩)
    ⟨by
      intro z w h
      apply Subtype.ext
      apply Prod.ext
      · exact Option.some.inj (congrArg (fun q => q.1.1) h)
      · exact Option.some.inj (congrArg (fun q => q.1.2) h), by
      rintro ⟨⟨x, y⟩, hxy⟩
      rcases Finset.mem_sdiff.mp hxy with ⟨hzero, hnotBoundary⟩
      cases x with
      | none =>
          exfalso
          apply hnotBoundary
          simp [splitTraceBiprojectiveAffineBoundary, hzero]
      | some x =>
          cases y with
          | none =>
              exfalso
              apply hnotBoundary
              simp [splitTraceBiprojectiveAffineBoundary, hzero]
          | some y =>
              have hvalue : splitTraceBiprojectiveValue alpha beta d e (some x, some y) = 0 :=
                (Finset.mem_filter.mp (show
                  (some x, some y) ∈ Finset.univ.filter
                    (fun z => splitTraceBiprojectiveValue alpha beta d e z = 0) by
                    exact hzero)).2
              refine ⟨⟨(x, y), ?_⟩, rfl⟩
              rw [mem_affineSplitTraceCoverZeros_iff]
              rw [← splitTraceBiprojectiveValue_affine]
              exact hvalue⟩

end Finite

end

end BGS.Markoff
