/-
Copyright (c) 2026 long-mathematics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher D. Long
-/
module

public import LeanPool.GaussianMomentsCounterexamples.RealMoments
public import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Tactic.Ring

/-! Polynomial Gaussian integration by parts on the canonical product space. -/

public section
noncomputable section
open MeasureTheory ProbabilityTheory MvPolynomial
open scoped BigOperators
namespace GaussianMomentsCounterexamples

/-- Stein's identity for each real coordinate and every complex polynomial. -/
theorem expectation_X_mul {n : ℕ} (i : Fin n) (P : MvPolynomial (Fin n) ℂ) :
    expectation (X i * P) = expectation (pderiv i P) := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial d c =>
    rw [X, monomial_mul_monomial, one_mul, pderiv_monomial]
    simp only [expectation_monomial]
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
      ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
    simp only [Finsupp.add_apply, Finsupp.single_eq_same, Finsupp.coe_tsub, Pi.sub_apply,
      Finsupp.single_apply]
    simp only [Nat.add_comm 1]
    rw [complex_gaussian_moment_succ]
    have hp : (∏ j ∈ (Finset.univ.erase i : Finset (Fin n)),
        ∫ x : ℝ, (x : ℂ) ^ ((Finsupp.single i 1 + d : Fin n →₀ ℕ) j) ∂gaussianReal 0 1) =
        ∏ j ∈ (Finset.univ.erase i : Finset (Fin n)),
        ∫ x : ℝ, (x : ℂ) ^ ((d - Finsupp.single i 1 : Fin n →₀ ℕ) j) ∂gaussianReal 0 1 := by
      apply Finset.prod_congr rfl
      intro j hj
      have hji := (Finset.mem_erase.mp hj).1
      simp [hji]
    simp only [Finsupp.add_apply, Finsupp.single_apply, Finsupp.coe_tsub, Pi.sub_apply] at hp
    rw [hp]
    ring
  | add P Q hP hQ =>
    rw [mul_add, expectation_add, map_add, expectation_add, hP, hQ]

end GaussianMomentsCounterexamples
