/-
Copyright (c) 2026 long-mathematics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher D. Long
-/
module

public import LeanPool.GaussianMomentsCounterexamples.DimensionTwo

/-! Exact radial and two-weight moment formulas in dimension two.
No one-variable Factorial Conjecture or two-dimensional exclusion theorem is assumed. -/

@[expose] public section
noncomputable section
open MvPolynomial Finset
open scoped BigOperators
namespace GaussianMomentsCounterexamples

/-- The linear factorial functional on the polynomial ring in U. -/
def factorialFunctional : Polynomial ℂ →ₗ[ℂ] ℂ :=
  Polynomial.lsum fun j => (LinearMap.ringLmapEquivSelf ℂ ℂ ℂ).symm (j.factorial : ℂ)

@[simp] theorem factorialFunctional_monomial (j : ℕ) (c : ℂ) :
    factorialFunctional (Polynomial.monomial j c) = c * (j.factorial : ℂ) := by
  simp [factorialFunctional, Polynomial.lsum, Polynomial.sum_monomial_index]

@[simp] theorem factorialFunctional_X_pow (j : ℕ) :
    factorialFunctional (Polynomial.X ^ j) = (j.factorial : ℂ) := by
  rw [Polynomial.X_pow_eq_monomial, factorialFunctional_monomial, one_mul]

/-- Substitute U=WZ in a univariate polynomial. -/
def radialLift : Polynomial ℂ →+* MvPolynomial (Fin 2) ℂ :=
  Polynomial.eval₂RingHom C (X 0 * X 1)

@[simp] theorem radialLift_monomial (j : ℕ) (c : ℂ) :
    radialLift (Polynomial.monomial j c) = C c * (X 0 * X 1) ^ j :=
  Polynomial.eval₂_monomial C (X 0 * X 1)

@[simp] theorem radialLift_X : radialLift Polynomial.X = X 0 * X 1 :=
  Polynomial.eval₂_X C (X 0 * X 1)

/-- Gaussian expectation on C[U] is exactly the factorial functional. -/
theorem pairExpectation_radial (A : Polynomial ℂ) :
    pairExpectation (radialLift A) = factorialFunctional A := by
  induction A using Polynomial.induction_on' with
  | add A B hA hB => simp only [map_add, hA, hB]
  | monomial j c =>
    rw [radialLift_monomial, factorialFunctional_monomial]
    simp [X, monomial_pow, monomial_mul_monomial, C_mul_monomial,
      pairMoment, Finsupp.smul_single]

/-- Explicit eval₂ form of the factorial correspondence. -/
theorem pairExpectation_eval_radial (A : Polynomial ℂ) :
    pairExpectation (A.eval₂ C (X 0 * X 1)) = factorialFunctional A :=
  pairExpectation_radial A

lemma pairExpectation_unbalanced_radial (a b : ℕ) (hab : a ≠ b) (A : Polynomial ℂ) :
    pairExpectation (X 0 ^ a * X 1 ^ b * radialLift A) = 0 := by
  induction A using Polynomial.induction_on' with
  | add A B hA hB => simp [map_add, mul_add, hA, hB]
  | monomial j c =>
    rw [radialLift_monomial]
    have hp : (X 0 ^ a * X 1 ^ b * (C c * (X 0 * X 1) ^ j) : MvPolynomial (Fin 2) ℂ) =
        C c * (X 0 ^ (a + j) * X 1 ^ (b + j)) := by ring
    rw [hp]
    simp [X, monomial_pow, monomial_mul_monomial, C_mul_monomial,
      pairMoment, Finsupp.smul_single, hab]

lemma pairExpectation_balanced_radial (a : ℕ) (A : Polynomial ℂ) :
    pairExpectation (X 0 ^ a * X 1 ^ a * radialLift A) =
      factorialFunctional (Polynomial.X ^ a * A) := by
  rw [← pairExpectation_radial]
  simp [mul_pow]

/-- A general two-weight polynomial in the manuscript's natural coordinates. -/
def twoWeightPolynomial (A B : Polynomial ℂ) : MvPolynomial (Fin 2) ℂ :=
  X 1 * radialLift A + X 0 * radialLift B

lemma pairExpectation_C_mul (c : ℂ) (P : MvPolynomial (Fin 2) ℂ) :
    pairExpectation (C c * P) = c * pairExpectation P := by
  simpa only [← smul_eq_C_mul, smul_eq_mul] using pairExpectation.map_smul c P

lemma twoWeight_moment_expansion (A B : Polynomial ℂ) (m : ℕ) :
    pairExpectation (twoWeightPolynomial A B ^ m) =
      ∑ a ∈ range (m + 1), (m.choose a : ℂ) *
        pairExpectation (X 0 ^ (m - a) * X 1 ^ a * radialLift (A ^ a * B ^ (m - a))) := by
  unfold twoWeightPolynomial
  rw [add_pow, map_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [← pairExpectation_C_mul]
  congr 1
  simp only [map_mul, map_pow, map_natCast]
  ring

/-- Every odd moment of ZA(U)+WB(U) vanishes, for arbitrary complex A and B. -/
theorem twoWeight_odd_moment (A B : Polynomial ℂ) (r : ℕ) :
    pairExpectation (twoWeightPolynomial A B ^ (2 * r + 1)) = 0 := by
  rw [twoWeight_moment_expansion]
  apply Finset.sum_eq_zero
  intro a ha
  have ham : a ≤ 2 * r + 1 := by simpa using Finset.mem_range.mp ha
  have hn : 2 * r + 1 - a ≠ a := by omega
  rw [pairExpectation_unbalanced_radial _ _ hn, mul_zero]

/-- The exact even-moment identity displayed in Section 7. -/
theorem twoWeight_even_moment (A B : Polynomial ℂ) (r : ℕ) :
    pairExpectation (twoWeightPolynomial A B ^ (2 * r)) =
      ((2 * r).choose r : ℂ) * factorialFunctional ((Polynomial.X * A * B) ^ r) := by
  rw [twoWeight_moment_expansion, Finset.sum_eq_single r]
  · have hr : 2 * r - r = r := by omega
    rw [hr, pairExpectation_balanced_radial]
    congr 2
    ring
  · intro a ha har
    have ham : a ≤ 2 * r := by simpa using Finset.mem_range.mp ha
    have hn : 2 * r - a ≠ a := by omega
    rw [pairExpectation_unbalanced_radial _ _ hn, mul_zero]
  · intro hr
    exact False.elim (hr (Finset.mem_range.mpr (by omega)))

/-- The odd-moment identity explicitly on the original real Gaussian coordinate space. -/
theorem twoWeight_actual_odd_moment (A B : Polynomial ℂ) (r : ℕ) :
    expectation ((pairSub (twoWeightPolynomial A B)) ^ (2 * r + 1)) = 0 := by
  have h := twoWeight_odd_moment A B r
  change expectation (pairSub (twoWeightPolynomial A B ^ (2 * r + 1))) = 0 at h
  rwa [map_pow] at h

/-- The even-moment identity explicitly on the original real Gaussian coordinate space. -/
theorem twoWeight_actual_even_moment (A B : Polynomial ℂ) (r : ℕ) :
    expectation ((pairSub (twoWeightPolynomial A B)) ^ (2 * r)) =
      ((2 * r).choose r : ℂ) * factorialFunctional ((Polynomial.X * A * B) ^ r) := by
  have h := twoWeight_even_moment A B r
  change expectation (pairSub (twoWeightPolynomial A B ^ (2 * r))) = _ at h
  rwa [map_pow] at h

end GaussianMomentsCounterexamples
