/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import Mathlib.RingTheory.Valuation.ValuationRing
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.Henselian.Factorization.ErrorPowers
/-!
# the finite minimum coefficient

The coefficientwise proof of Hensel's lemma chooses, among the finitely many
coefficients of `f - g₀h₀` and `ag₀ + bh₀ - 1`, one coefficient of minimum
valuation and calls it `π`.  In a valuation ring this is the same algebraic
input as choosing one coefficient that divides all coefficients in the finite
set.
-/

noncomputable section

open scoped Polynomial

namespace AlgebraicNumberTheory
namespace Valuations

/-- finite divisibility minimum in a valuation ring: every
nonempty finite set has an element that divides all elements of the set. -/
theorem henselFactorization_exists_mem_finset_dvd_all
    {R : Type*} [Monoid R] [PreValuationRing R] {s : Finset R}
    (hs : s.Nonempty) :
    ∃ π ∈ s, ∀ x ∈ s, π ∣ x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      rcases hs with ⟨x, hx⟩
      simp at hx
  | @insert a s ha ih =>
      by_cases hs' : s.Nonempty
      · rcases ih hs' with ⟨π, hπs, hπall⟩
        rcases ValuationRing.dvd_total π a with hπa | haπ
        · refine ⟨π, Finset.mem_insert_of_mem hπs, ?_⟩
          intro x hx
          rw [Finset.mem_insert] at hx
          rcases hx with rfl | hxs
          · exact hπa
          · exact hπall x hxs
        · refine ⟨a, Finset.mem_insert_self a s, ?_⟩
          intro x hx
          rw [Finset.mem_insert] at hx
          rcases hx with rfl | hxs
          · exact dvd_refl _
          · exact dvd_trans haπ (hπall x hxs)
      · refine ⟨a, Finset.mem_insert_self a s, ?_⟩
        intro x hx
        rw [Finset.mem_insert] at hx
        rcases hx with rfl | hxs
        · exact dvd_refl _
        · exact False.elim (hs' ⟨x, hxs⟩)

/-- the finite set of coefficients of two polynomials from
which the construction chooses the minimum-value coefficient. -/
def henselFactorizationTwoPolynomialCoeffFinset
    {R : Type*} [Semiring R] (P Q : R[X]) : Finset R := by
  classical
  exact P.support.image (fun n => P.coeff n) ∪
    Q.support.image (fun n => Q.coeff n)

/-- A coefficient supported in the left polynomial belongs to the two-polynomial
coefficient set. -/
theorem henselFactorization_mem_twoPolynomialCoeffFinset_left
    {R : Type*} [Semiring R] {P Q : R[X]} {n : ℕ}
    (hn : n ∈ P.support) :
    P.coeff n ∈ henselFactorizationTwoPolynomialCoeffFinset P Q := by
  classical
  unfold henselFactorizationTwoPolynomialCoeffFinset
  exact Finset.mem_union.mpr
    (Or.inl (Finset.mem_image.mpr ⟨n, hn, rfl⟩))

/-- A coefficient supported in the right polynomial belongs to the
two-polynomial coefficient set. -/
theorem henselFactorization_mem_twoPolynomialCoeffFinset_right
    {R : Type*} [Semiring R] {P Q : R[X]} {n : ℕ}
    (hn : n ∈ Q.support) :
    Q.coeff n ∈ henselFactorizationTwoPolynomialCoeffFinset P Q := by
  classical
  unfold henselFactorizationTwoPolynomialCoeffFinset
  exact Finset.mem_union.mpr
    (Or.inr (Finset.mem_image.mpr ⟨n, hn, rfl⟩))

/-- every element of the finite coefficient set is a
nonzero coefficient. -/
theorem henselFactorization_ne_zero_of_mem_twoPolynomialCoeffFinset
    {R : Type*} [Semiring R] {P Q : R[X]} {x : R}
    (hx : x ∈ henselFactorizationTwoPolynomialCoeffFinset P Q) :
    x ≠ 0 := by
  classical
  unfold henselFactorizationTwoPolynomialCoeffFinset at hx
  rw [Finset.mem_union] at hx
  rcases hx with hx | hx
  · rcases Finset.mem_image.mp hx with ⟨n, hn, rfl⟩
    simpa [Polynomial.mem_support_iff] using hn
  · rcases Finset.mem_image.mp hx with ⟨n, hn, rfl⟩
    simpa [Polynomial.mem_support_iff] using hn

/-- if the two-polynomial coefficient set is nonempty, one of
its coefficients divides every coefficient of both polynomials. -/
theorem henselFactorization_exists_coeff_dvd_all_two_polynomials
    {R : Type*} [CommRing R] [PreValuationRing R] {P Q : R[X]}
    (hs : (henselFactorizationTwoPolynomialCoeffFinset P Q).Nonempty) :
    ∃ π ∈ henselFactorizationTwoPolynomialCoeffFinset P Q,
      (∀ n : ℕ, π ∣ P.coeff n) ∧
        (∀ n : ℕ, π ∣ Q.coeff n) := by
  classical
  rcases henselFactorization_exists_mem_finset_dvd_all
      (R := R) (s := henselFactorizationTwoPolynomialCoeffFinset P Q) hs with
    ⟨π, hπ, hπall⟩
  refine ⟨π, hπ, ?_, ?_⟩
  · intro n
    by_cases hn : n ∈ P.support
    · exact hπall (P.coeff n)
        (henselFactorization_mem_twoPolynomialCoeffFinset_left
          (P := P) (Q := Q) hn)
    · rw [Polynomial.notMem_support_iff.mp hn]
      exact dvd_zero π
  · intro n
    by_cases hn : n ∈ Q.support
    · exact hπall (Q.coeff n)
        (henselFactorization_mem_twoPolynomialCoeffFinset_right
          (P := P) (Q := Q) hn)
    · rw [Polynomial.notMem_support_iff.mp hn]
      exact dvd_zero π

/-- if the two polynomials have coefficients in an ideal, the
chosen finite-minimum coefficient lies in the same ideal. -/
theorem henselFactorization_exists_coeff_mem_ideal_dvd_all_two_polynomials
    {R : Type*} [CommRing R] [PreValuationRing R] {I : Ideal R}
    {P Q : R[X]}
    (hP : ∀ n : ℕ, P.coeff n ∈ I)
    (hQ : ∀ n : ℕ, Q.coeff n ∈ I)
    (hs : (henselFactorizationTwoPolynomialCoeffFinset P Q).Nonempty) :
    ∃ π ∈ I,
      π ∈ henselFactorizationTwoPolynomialCoeffFinset P Q ∧
        (∀ n : ℕ, π ∣ P.coeff n) ∧
          (∀ n : ℕ, π ∣ Q.coeff n) := by
  classical
  rcases henselFactorization_exists_coeff_dvd_all_two_polynomials
      (R := R) (P := P) (Q := Q) hs with
    ⟨π, hπcoeff, hπP, hπQ⟩
  have hπI : π ∈ I := by
    unfold henselFactorizationTwoPolynomialCoeffFinset at hπcoeff
    rw [Finset.mem_union] at hπcoeff
    rcases hπcoeff with hπleft | hπright
    · rcases Finset.mem_image.mp hπleft with ⟨n, _hn, hnπ⟩
      rw [← hnπ]
      exact hP n
    · rcases Finset.mem_image.mp hπright with ⟨n, _hn, hnπ⟩
      rw [← hnπ]
      exact hQ n
  exact ⟨π, hπI, hπcoeff, hπP, hπQ⟩

/-- nonempty finite-minimum branch with the ideal
membership retained: if both source polynomials have coefficients in `I`, the
chosen coefficient `π` lies in `I` and simultaneously factors both
polynomials. -/
theorem henselFactorization_exists_coeff_mem_ideal_minimum_factor_two_polynomials
    {R : Type*} [CommRing R] [PreValuationRing R] {I : Ideal R}
    {P Q : R[X]}
    (hP : ∀ n : ℕ, P.coeff n ∈ I)
    (hQ : ∀ n : ℕ, Q.coeff n ∈ I)
    (hs : (henselFactorizationTwoPolynomialCoeffFinset P Q).Nonempty) :
    ∃ π ∈ I,
      π ∈ henselFactorizationTwoPolynomialCoeffFinset P Q ∧
        (∃ P' : R[X], P = Polynomial.C π * P') ∧
          (∃ Q' : R[X], Q = Polynomial.C π * Q') := by
  classical
  rcases henselFactorization_exists_coeff_mem_ideal_dvd_all_two_polynomials
      (R := R) (I := I) (P := P) (Q := Q) hP hQ hs with
    ⟨π, hπI, hπcoeff, hπP, hπQ⟩
  refine ⟨π, hπI, hπcoeff, ?_, ?_⟩
  · exact henselFactorization_exists_factor_of_coeff_mem_span_singleton
      (a := π) (P := P) (by
        intro n
        rw [Ideal.mem_span_singleton]
        exact hπP n)
  · exact henselFactorization_exists_factor_of_coeff_mem_span_singleton
      (a := π) (P := Q) (by
        intro n
        rw [Ideal.mem_span_singleton]
        exact hπQ n)

/-- the first choice of `π` in the nonempty branch:
from the two initial source polynomials
`f - g0*h0` and `a*g0 + b*h0 - 1`, choose a coefficient `π` lying in the
maximal ideal that factors both source polynomials. -/
theorem henselFactorization_exists_pi_factor_initial_errors_of_nonempty
    {R : Type*} [CommRing R] [IsLocalRing R] [PreValuationRing R]
    {f g0 h0 a b : R[X]}
    (herr : ∀ n : ℕ, (f - g0 * h0).coeff n ∈
      IsLocalRing.maximalIdeal R)
    (hbezerr : ∀ n : ℕ, (a * g0 + b * h0 - 1).coeff n ∈
      IsLocalRing.maximalIdeal R)
    (hs :
      (henselFactorizationTwoPolynomialCoeffFinset
        (f - g0 * h0) (a * g0 + b * h0 - 1)).Nonempty) :
    ∃ π ∈ IsLocalRing.maximalIdeal R,
      π ∈ henselFactorizationTwoPolynomialCoeffFinset
        (f - g0 * h0) (a * g0 + b * h0 - 1) ∧
        (∃ f1 : R[X], f - g0 * h0 = Polynomial.C π * f1) ∧
          (∃ e1 : R[X],
            a * g0 + b * h0 - 1 = Polynomial.C π * e1) := by
  exact henselFactorization_exists_coeff_mem_ideal_minimum_factor_two_polynomials
    (R := R) (I := IsLocalRing.maximalIdeal R)
    (P := f - g0 * h0) (Q := a * g0 + b * h0 - 1)
    herr hbezerr hs

/-- residue-factorization form of the first `π`
choice in the nonempty branch.  The two coefficient-in-the-maximal-ideal
inputs are produced from the residue factorization and lifted Bezout
congruence. -/
theorem henselFactorization_exists_pi_factor_initial_errors_of_residue_lifts_of_nonempty
    {R : Type*} [CommRing R] [IsLocalRing R] [PreValuationRing R]
    {f g0 h0 a b : R[X]}
    {gbar hbar : (IsLocalRing.ResidueField R)[X]}
    (hfbar : f.map (IsLocalRing.residue R) = gbar * hbar)
    (hg0 : g0.map (IsLocalRing.residue R) = gbar)
    (hh0 : h0.map (IsLocalRing.residue R) = hbar)
    (hbez : (a * g0 + b * h0).map (IsLocalRing.residue R) = 1)
    (hs :
      (henselFactorizationTwoPolynomialCoeffFinset
        (f - g0 * h0) (a * g0 + b * h0 - 1)).Nonempty) :
    ∃ π ∈ IsLocalRing.maximalIdeal R,
      π ∈ henselFactorizationTwoPolynomialCoeffFinset
        (f - g0 * h0) (a * g0 + b * h0 - 1) ∧
        (∃ f1 : R[X], f - g0 * h0 = Polynomial.C π * f1) ∧
          (∃ e1 : R[X],
            a * g0 + b * h0 - 1 = Polynomial.C π * e1) := by
  exact henselFactorization_exists_pi_factor_initial_errors_of_nonempty
    (R := R) (f := f) (g0 := g0) (h0 := h0) (a := a) (b := b)
    (henselFactorization_coeff_mem_maximalIdeal_sub_mul_of_residue_lifts
      hfbar hg0 hh0)
    (henselFactorization_coeff_mem_maximalIdeal_sub_one_of_bezout_lift hbez)
    hs

/-- if the finite coefficient set is empty, the first
polynomial is zero. -/
theorem henselFactorization_left_eq_zero_of_twoPolynomialCoeffFinset_empty
    {R : Type*} [Semiring R] {P Q : R[X]}
    (h : henselFactorizationTwoPolynomialCoeffFinset P Q = ∅) :
    P = 0 := by
  ext n
  by_cases hn : n ∈ P.support
  · have hmem :
        P.coeff n ∈ henselFactorizationTwoPolynomialCoeffFinset P Q :=
      henselFactorization_mem_twoPolynomialCoeffFinset_left
        (P := P) (Q := Q) hn
    rw [h] at hmem
    simp at hmem
  · exact Polynomial.notMem_support_iff.mp hn

/-- if the finite coefficient set is empty, the second
polynomial is zero. -/
theorem henselFactorization_right_eq_zero_of_twoPolynomialCoeffFinset_empty
    {R : Type*} [Semiring R] {P Q : R[X]}
    (h : henselFactorizationTwoPolynomialCoeffFinset P Q = ∅) :
    Q = 0 := by
  ext n
  by_cases hn : n ∈ Q.support
  · have hmem :
        Q.coeff n ∈ henselFactorizationTwoPolynomialCoeffFinset P Q :=
      henselFactorization_mem_twoPolynomialCoeffFinset_right
        (P := P) (Q := Q) hn
    rw [h] at hmem
    simp at hmem
  · exact Polynomial.notMem_support_iff.mp hn

/-- the empty finite coefficient set is exactly the branch
where both source polynomials are zero. -/
theorem henselFactorization_twoPolynomialCoeffFinset_empty_iff
    {R : Type*} [Semiring R] {P Q : R[X]} :
    henselFactorizationTwoPolynomialCoeffFinset P Q = ∅ ↔ P = 0 ∧ Q = 0 := by
  classical
  constructor
  · intro h
    exact ⟨
      henselFactorization_left_eq_zero_of_twoPolynomialCoeffFinset_empty
        (P := P) (Q := Q) h,
      henselFactorization_right_eq_zero_of_twoPolynomialCoeffFinset_empty
        (P := P) (Q := Q) h⟩
  · rintro ⟨rfl, rfl⟩
    unfold henselFactorizationTwoPolynomialCoeffFinset
    simp

end Valuations
end AlgebraicNumberTheory

end
