/-
Copyright (c) 2026 long-mathematics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher D. Long
-/
module

public import LeanPool.GaussianMomentsCounterexamples.ComplexContractions
public import Mathlib.Algebra.Polynomial.Inductions

/-! Gaussian coefficient contraction for arbitrary univariate polynomials. -/

@[expose] public section

noncomputable section
namespace GaussianMomentsCounterexamples
open MvPolynomial

/-- The coefficient-contraction identity with genuine integration on any canonical
Gaussian space and any two distinct coordinates. -/
theorem expectation_coefficient_contraction {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (a : ℕ) (R : Polynomial ℂ) :
    expectation (normalizedW i j ^ a * R.eval₂ C (normalizedZ i j)) =
      (a.factorial : ℂ) * R.coeff a := by
  induction R using Polynomial.induction_on' with
  | add P Q hP hQ =>
    rw [Polynomial.eval₂_add, mul_add, expectation_add, hP, hQ, Polynomial.coeff_add,
      mul_add]
  | monomial b c =>
    rw [Polynomial.eval₂_monomial]
    have h : normalizedW i j ^ a * (C c * normalizedZ i j ^ b) =
        C c * (normalizedW i j ^ a * normalizedZ i j ^ b) := by ring
    rw [h, expectation_C_mul, expectation_pair hij, Polynomial.coeff_monomial]
    by_cases hab : a = b
    · subst b; simp [mul_comm]
    · simp [hab, Ne.symm hab]

end GaussianMomentsCounterexamples
