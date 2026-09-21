/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams.
-/
module

public import Mathlib.RingTheory.Polynomial.Pochhammer
public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.Algebra.Polynomial.Degree.Support
public import Mathlib.Algebra.Polynomial.Eval.SMul

/-!
# The ascending Pochhammer polynomial transform

This file defines the linear transformation on univariate polynomials that sends the
standard monomial `X ^ n` to the ascending Pochhammer polynomial `ascPochhammer R n`
that is $X (X+1) \cdots (X+n-1)$. The inverse transformation is also defined and some
identities are proven.

## Mathematical preliminaries

The transformation is expressed using Stirling numbers, for which different notations are
in use. Here the Stirling numbers are taken as `stirlingFirst` and `stirlingSecond` from
`Mathlib.Combinatorics.Enumerative.Stirling`.

In the NIST Handbook [DLMF], Section 26.8, the Stirling numbers are defined using the
notation `s` and `S`. The concordance is given by
$s(n,k)=(−1)^{n−k}{stirlingFirst}(n,k)$ and
$S(n,k)={stirlingSecond}(n,k)$.
The Mathlib functions {stirlingFirst} and {stirlingSecond} are nonnegative and are called the
unsigned Stirling numbers of the first and second kind. The `s` of [DLMF] is called the
signed Stirling number of the first kind.

DLMF [26.8.7](http://dlmf.nist.gov/26.8.E7) gives the expansion in terms of the signed
Stirling numbers of the first kind:
$$
\sum_{k=0}^{n} s(n,k) x^k = (x-n+1)_n .
$$

DLMF [26.8.10](http://dlmf.nist.gov/26.8.E10) gives the inverse expansion in terms of the
Stirling numbers of the second kind:
$$
\sum_{k=1}^{n} S(n,k) (x-k+1)_k = x^n .
$$

Finally, DLMF [26.8.39](http://dlmf.nist.gov/26.8.E39) gives the two Stirling inversion
identities:
$$
\sum_{j=k}^{n} s(j,k) S(n,j) = \sum_{j=k}^{n} s(n,j) S(j,k) = \delta_{n,k} .
$$
These DLMF formulas use falling factorials. In this file the rising factorials of
`ascPochhammer` are used and this entails a replacement of `x` by `-x`.

The resulting transformations define a linear equivalence of `Polynomial R`. It preserves
the leading coefficient and natural degree. The file also proves its interaction with
multiplication by `X`.

## Main definitions and results

* `ascPochhammerTransform`: the linear map sending `X ^ n` to `ascPochhammer R n`.
* `ascPochhammerInverseTransform`: its inverse, expressed using Stirling numbers of the
  second kind.
* `ascPochhammerLinearEquiv`: the resulting linear equivalence of `Polynomial R`.
* `coeff_ascPochhammerTransform`: the coefficient formula in terms of Stirling numbers
  of the first kind.
* `ascPochhammerTransform_X_mul`: the relation between multiplication by `X` and the
  shift `X ↦ X + 1`.

## References

[DLMF] NIST Digital Library of Mathematical Functions. https://dlmf.nist.gov/, Release 1.2.7 of
2026-06-15. F. W. J. Olver, A. B. Olde Daalhuis, D. W. Lozier, B. I. Schneider, R. F. Boisvert,
C. W. Clark, B. R. Miller, B. V. Saunders, H. S. Cohl, and M. A. McClain, eds.
-/

@[expose] public noncomputable section

variable (R : Type*) [CommRing R]

/-- The $k$-th coefficient of the $n$-th ascending Pochhammer polynomial is the
unsigned Stirling number of the first kind. -/
@[simp] theorem coeff_ascPochhammer (n k : ℕ) :
    (ascPochhammer R n).coeff k = (n.stirlingFirst k : R) := by
  induction n generalizing k with
  | zero =>
      cases k <;> simp [Polynomial.coeff_one]
  | succ n ih =>
      cases k with
      | zero =>
          simp [ascPochhammer_succ_left]
      | succ k =>
          rw [ascPochhammer_succ_right]
          simp [mul_add, ih, Nat.stirlingFirst_succ_succ,
            mul_comm, add_comm]

/-- Expansion of the ascending Pochhammer polynomial in the standard monomial basis,
with coefficients given by the unsigned Stirling numbers of the first kind. -/
theorem ascPochhammer_eq_sum_stirlingFirst (n : ℕ) :
    ascPochhammer R n =
      ∑ k ∈ Finset.range (n + 1), Polynomial.monomial k (n.stirlingFirst k : R) := by
  ext j
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_monomial, Finset.sum_ite_eq']
  split_ifs with h
  · simp only [coeff_ascPochhammer]
  · rw [coeff_ascPochhammer]
    have h_lt : n < j := by
      by_contra h_not_lt
      have h_j : j < n + 1 := by omega
      exact h (Finset.mem_range.mpr h_j)
    simp [Nat.stirlingFirst_eq_zero_of_lt h_lt]

/-- The image of `X ^ n` under the inverse ascending Pochhammer transform, expressed in
the standard monomial basis using signed Stirling numbers of the second kind. -/
noncomputable def inverseAscPochhammerBasis (n : ℕ) : Polynomial R :=
  ∑ k ∈ Finset.range (n + 1),
    Polynomial.monomial k (((-1 : R) ^ (n - k)) * (n.stirlingSecond k : R))

/- Some private defs and theorems towards the proof of `sum_stirlingSecond_mul_ascPochhammer`. -/
private def signedStirlingSecond (n k : ℕ) : R :=
  (-1 : R) ^ n * (-1 : R) ^ k * (n.stirlingSecond k : R)
private theorem signedStirlingSecond_succ_succ (n k : ℕ) :
    signedStirlingSecond R (n + 1) (k + 1) =
      signedStirlingSecond R n k -
        signedStirlingSecond R n (k + 1) * ((k + 1 : ℕ) : R) := by
  simp [signedStirlingSecond, Nat.stirlingSecond_succ_succ,
    pow_succ, Nat.cast_add, Nat.cast_mul]; ring
@[simp] private theorem signedStirlingSecond_succ_zero (n : ℕ) :
    signedStirlingSecond R (n + 1) 0 = 0 := by
  simp [signedStirlingSecond]
private theorem ascPochhammer_mul_X (k : ℕ) :
    ascPochhammer R k * Polynomial.X =
      ascPochhammer R (k + 1) -
        (k : R) • ascPochhammer R k := by
  rw [ascPochhammer_succ_right]
  simp [mul_add, Polynomial.smul_eq_C_mul, mul_comm]
private theorem sum_signedStirlingSecond_mul_ascPochhammer (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
        signedStirlingSecond R n k • ascPochhammer R k =
      Polynomial.X ^ n := by
  induction n with
  | zero =>
      simp [signedStirlingSecond]
  | succ n ih =>
      have hshift :
          ∑ k ∈ Finset.range (n + 1),
              (signedStirlingSecond R n k * (k : R)) •
                ascPochhammer R k
            =
          ∑ k ∈ Finset.range (n + 1),
              (signedStirlingSecond R n (k + 1) *
                ((k + 1 : ℕ) : R)) •
                ascPochhammer R (k + 1) := by
        rw [
          Finset.sum_range_succ'
            (fun k =>
              (signedStirlingSecond R n k * (k : R)) •
                ascPochhammer R k) n,
          Finset.sum_range_succ
            (fun k =>
              (signedStirlingSecond R n (k + 1) *
                ((k + 1 : ℕ) : R)) •
                ascPochhammer R (k + 1)) n
        ]
        simp [signedStirlingSecond,
          Nat.stirlingSecond_eq_zero_of_lt n.lt_succ_self]

      rw [
        Finset.sum_range_succ'
          (fun k =>
            signedStirlingSecond R (n + 1) k •
              ascPochhammer R k) (n + 1)
      ]
      simp only [signedStirlingSecond_succ_zero, zero_smul]
      simp_rw [signedStirlingSecond_succ_succ]
      simp_rw [sub_smul]
      rw [Finset.sum_sub_distrib]
      rw [← hshift]
      rw [pow_succ, ← ih, Finset.sum_mul]
      rw [← Finset.sum_sub_distrib]
      simp only [add_zero]
      simp_rw [smul_mul_assoc]
      simp_rw [ascPochhammer_mul_X]
      simp_rw [smul_sub]
      simp_rw [smul_smul]
private theorem neg_one_pow_sub_mul_stirlingSecond
    {n k : ℕ} (hk : k ≤ n) :
    ((-1 : R) ^ (n - k)) * (n.stirlingSecond k : R) =
      signedStirlingSecond R n k := by
  unfold signedStirlingSecond
  have hpow :
      (-1 : R) ^ n =
        (-1 : R) ^ (n - k) * (-1 : R) ^ k := by
    rw [← pow_add, Nat.sub_add_cancel hk]
  rw [hpow]
  have hs :
      (-1 : R) ^ k * (-1 : R) ^ k = 1 := by
    rw [← mul_pow]
    simp
  calc
    (-1 : R) ^ (n - k) * (n.stirlingSecond k : R)
        =
      (-1 : R) ^ (n - k) * 1 *
        (n.stirlingSecond k : R) := by simp
    _ =
      (-1 : R) ^ (n - k) *
        (((-1 : R) ^ k) * ((-1 : R) ^ k)) *
          (n.stirlingSecond k : R) := by rw [hs]
    _ =
      ((-1 : R) ^ (n - k) * (-1 : R) ^ k) *
        (-1 : R) ^ k * (n.stirlingSecond k : R) := by
      simp only [mul_assoc]
/- (End of private defs and theorems towards `sum_stirlingSecond_mul_ascPochhammer`.) -/

/-- Expansion of the standard monomial `X ^ n` in the ascending Pochhammer
basis, with coefficients given by signed Stirling numbers of the second kind. -/
theorem sum_stirlingSecond_mul_ascPochhammer (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
      (((-1 : R) ^ (n - k)) * (n.stirlingSecond k : R)) •
        ascPochhammer R k
      = Polynomial.X ^ n := by
  calc
    ∑ k ∈ Finset.range (n + 1),
        (((-1 : R) ^ (n - k)) *
          (n.stirlingSecond k : R)) • ascPochhammer R k
        =
      ∑ k ∈ Finset.range (n + 1),
        signedStirlingSecond R n k • ascPochhammer R k := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [neg_one_pow_sub_mul_stirlingSecond
            (R := R)
            (Nat.le_of_lt_succ (Finset.mem_range.mp hk))]
    _ = Polynomial.X ^ n :=
      sum_signedStirlingSecond_mul_ascPochhammer (R := R) n

/-- The `R`-linear transformation of `Polynomial R` sending the standard monomial `X ^ n`
to the ascending Pochhammer polynomial `ascPochhammer R n`. -/
noncomputable def ascPochhammerTransform :
    Polynomial R →ₗ[R] Polynomial R :=
  Polynomial.lsum fun n => LinearMap.id.smulRight (ascPochhammer R n)

/-- The ascending Pochhammer transform sends the monomial `a * X ^ n` to
`a • ascPochhammer R n`. -/
@[simp] theorem ascPochhammerTransform_monomial (n : ℕ) (a : R) :
    ascPochhammerTransform R (Polynomial.monomial n a) = a • ascPochhammer R n := by
  simp [ascPochhammerTransform]

/-- The ascending Pochhammer transform sends the standard monomial `X ^ n` to the
ascending Pochhammer polynomial `ascPochhammer R n`. -/
@[simp] theorem ascPochhammerTransform_X_pow (n : ℕ) :
    ascPochhammerTransform R (Polynomial.X ^ n) = ascPochhammer R n := by
  rw [Polynomial.X_pow_eq_monomial]
  simp

/-- The inverse ascending Pochhammer transform, defined by sending `X ^ n` to
`inverseAscPochhammerBasis R n` and extending linearly. -/
noncomputable def ascPochhammerInverseTransform :
    Polynomial R →ₗ[R] Polynomial R :=
  Polynomial.lsum fun n =>
    LinearMap.id.smulRight (inverseAscPochhammerBasis R n)

/-- The inverse ascending Pochhammer transform applied to a monomial. -/
@[simp] theorem ascPochhammerInverseTransform_monomial
    (n : ℕ) (a : R) :
    ascPochhammerInverseTransform R (Polynomial.monomial n a) =
      a • inverseAscPochhammerBasis R n := by
  simp [ascPochhammerInverseTransform]

/-- The inverse ascending Pochhammer transform sends `X ^ n` to
`inverseAscPochhammerBasis R n`. -/
@[simp] theorem ascPochhammerInverseTransform_X_pow (n : ℕ) :
    ascPochhammerInverseTransform R (Polynomial.X ^ n) =
      inverseAscPochhammerBasis R n := by
  rw [Polynomial.X_pow_eq_monomial]
  simp

/-- Applying the ascending Pochhammer transform to the inverse basis polynomials recovers
the standard monomials $X^n$. -/
theorem ascPochhammerTransform_inverseAscPochhammerBasis (n : ℕ) :
    ascPochhammerTransform R (inverseAscPochhammerBasis R n) =
      Polynomial.X ^ n := by
  simp [inverseAscPochhammerBasis, sum_stirlingSecond_mul_ascPochhammer]

/-- Applying the ascending Pochhammer transform after the inverse transform is the identity
on polynomials. -/
theorem ascPochhammerTransform_inverseTransform (p : Polynomial R) :
    ascPochhammerTransform R
      (ascPochhammerInverseTransform R p) = p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simp [map_add, hp, hq]
  | monomial n a =>
      rw [ascPochhammerInverseTransform_monomial]
      rw [map_smul]
      rw [ascPochhammerTransform_inverseAscPochhammerBasis]
      exact Polynomial.smul_X_eq_monomial

/-- The composition of the ascending Pochhammer transform and its inverse is the identity
linear map. -/
theorem ascPochhammerTransform_comp_inverse :
    (ascPochhammerTransform R).comp
      (ascPochhammerInverseTransform R) =
    LinearMap.id := by
  apply LinearMap.ext
  intro p
  exact ascPochhammerTransform_inverseTransform (R := R) p

/-- Expands the ascending Pochhammer transform of `p` by replacing each standard monomial
`X ^ n` by `ascPochhammer R n`, with the same coefficient. -/
theorem ascPochhammerTransform_apply (p : Polynomial R) :
    ascPochhammerTransform R p = p.sum fun n a ↦ a • ascPochhammer R n := by
  simp [ascPochhammerTransform]

/-- The `k`-th coefficient of the transformed polynomial, expressed as a sum over the
coefficients of the original polynomial. -/
theorem coeff_ascPochhammerTransform (p : Polynomial R) (k : ℕ) :
    (ascPochhammerTransform R p).coeff k =
      p.sum (fun n a ↦ a * (n.stirlingFirst k : R)) := by
  rw [ascPochhammerTransform_apply]
  simp [coeff_ascPochhammer]

/-- The `k`-th coefficient of the transformed polynomial, expressed as a finite
sum over degrees `0, ..., p.natDegree`. -/
theorem coeff_ascPochhammerTransform_eq_sum_range
    (p : Polynomial R) (k : ℕ) :
    (ascPochhammerTransform R p).coeff k =
      ∑ n ∈ Finset.range (p.natDegree + 1),
        p.coeff n * (n.stirlingFirst k : R) := by
  rw [coeff_ascPochhammerTransform]
  simpa using
    (Polynomial.sum_over_range p
      (f := fun n a ↦ a * (n.stirlingFirst k : R))
      (fun n => by simp))

/-- The leading coefficient of the polynomial is preserved under the ascending
Pochhammer transform. -/
theorem coeff_natDegree_ascPochhammerTransform (p : Polynomial R) :
    (ascPochhammerTransform R p).coeff p.natDegree =
      p.coeff p.natDegree := by
  rw [coeff_ascPochhammerTransform_eq_sum_range]
  rw [Finset.sum_eq_single_of_mem p.natDegree (by simp)]
  · simp [Nat.stirlingFirst_self]
  · intro n hn hne
    have hle : n ≤ p.natDegree :=
      Nat.le_of_lt_succ (Finset.mem_range.mp hn)
    have hlt : n < p.natDegree :=
      Nat.lt_of_le_of_ne hle hne
    simp [Nat.stirlingFirst_eq_zero_of_lt hlt]

/-- The natural degree of a polynomial is preserved under the ascending
Pochhammer transform. -/
theorem natDegree_ascPochhammerTransform (p : Polynomial R) :
    (ascPochhammerTransform R p).natDegree = p.natDegree := by
  by_cases hp : p = 0
  · subst p
    simp
  · apply Polynomial.eq_natDegree_of_le_mem_support
    · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
      intro N hN
      rw [coeff_ascPochhammerTransform_eq_sum_range]
      apply Finset.sum_eq_zero
      intro n hn
      have hnle : n ≤ p.natDegree :=
        Nat.le_of_lt_succ (Finset.mem_range.mp hn)
      have hnN : n < N :=
        Nat.lt_of_le_of_lt hnle hN
      simp [Nat.stirlingFirst_eq_zero_of_lt hnN]
    · rw [Polynomial.mem_support_iff]
      rw [coeff_natDegree_ascPochhammerTransform R p]
      exact Polynomial.mem_support_iff.mp
        (Polynomial.natDegree_mem_support_of_nonzero hp)

/-- The ascending Pochhammer transform is injective. -/
theorem ascPochhammerTransform_injective :
    Function.Injective (ascPochhammerTransform R) := by
  intro p q hpq
  by_contra hne
  letI : Nontrivial R :=
    Polynomial.Nontrivial.of_polynomial_ne hne
  have hpq0 : p - q ≠ 0 := sub_ne_zero.mpr hne
  have hmap :
      ascPochhammerTransform R (p - q) = 0 := by
    rw [map_sub, hpq, sub_self]
  have hc :
      ((ascPochhammerTransform R) (p - q)).coeff
          (p - q).natDegree = 0 := by
    rw [hmap]
    simp
  rw [coeff_natDegree_ascPochhammerTransform R (p - q)] at hc
  have hmem :
      (p - q).natDegree ∈ (p - q).support :=
    Polynomial.natDegree_mem_support_of_nonzero hpq0
  have hcoeff :
      (p - q).coeff (p - q).natDegree ≠ 0 := by
    exact Polynomial.mem_support_iff.mp hmem
  exact hcoeff hc

/-- The linear equivalence of `Polynomial R` that sends `X ^ n` to the ascending Pochhammer
polynomial `ascPochhammer R n`. -/
noncomputable def ascPochhammerLinearEquiv :
    Polynomial R ≃ₗ[R] Polynomial R where
  toLinearMap := ascPochhammerTransform R
  invFun := ascPochhammerInverseTransform R
  left_inv p := by
    apply ascPochhammerTransform_injective (R := R)
    exact ascPochhammerTransform_inverseTransform
      (R := R) (ascPochhammerTransform R p)
  right_inv p := by
    exact ascPochhammerTransform_inverseTransform (R := R) p

/-- The ascending Pochhammer transform intertwines multiplication by `X` with multiplication
by `X` followed by the shift `X ↦ X + 1`: `T (X * p) = X * (T p).comp (X + 1)`. -/
theorem ascPochhammerTransform_X_mul (p : Polynomial R) :
    ascPochhammerTransform R (Polynomial.X * p) =
      Polynomial.X *
        (ascPochhammerTransform R p).comp (Polynomial.X + 1) := by
  refine Polynomial.induction_on' p ?_ ?_
  · intro p q hp hq
    simp [mul_add, hp, hq]
  · intro n a
    rw [Polynomial.X_mul_monomial]
    rw [ascPochhammerTransform_monomial]
    rw [ascPochhammerTransform_monomial]
    rw [ascPochhammer_succ_left]
    rw [Polynomial.smul_comp]
    rw [mul_smul_comm]

end
