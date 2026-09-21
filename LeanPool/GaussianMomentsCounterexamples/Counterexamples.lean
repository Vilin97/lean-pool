/-
Copyright (c) 2026 long-mathematics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher D. Long
-/
module

public import LeanPool.GaussianMomentsCounterexamples.GaussianBridge
public import LeanPool.GaussianMomentsCounterexamples.DimensionExtension

/-! The unconditional Gaussian counterexamples and genuine failure of GMC in all n ≥ 3. -/

@[expose] public section
noncomputable section
open MvPolynomial
namespace GaussianMomentsCounterexamples

lemma normalizedSub3_polyAt (A : Polynomial ℂ) :
    normalizedSub3 (polyAt 1 A) = A.eval₂ C Q3 := by
  induction A using Polynomial.induction_on' with
  | monomial k c => simp [polyAt_monomial, normalizedSub3, Q3, Polynomial.eval₂_monomial]
  | add A B hA hB => simp only [map_add, Polynomial.eval₂_add, hA, hB]

lemma normalizedSub4_polyAt (A : Polynomial ℂ) :
    normalizedSub4 (polyAt 3 A) = A.eval₂ C Q4 := by
  induction A using Polynomial.induction_on' with
  | monomial k c => simp [polyAt_monomial, normalizedSub4, Q4, Polynomial.eval₂_monomial]
  | add A B hA hB => simp only [map_add, Polynomial.eval₂_add, hA, hB]

/-- Theorem 5.1, full arbitrary-polynomial coefficient identity with actual Gaussian
expectations. -/
theorem master_three (A : Polynomial ℂ) (m : ℕ) (hm : 1 ≤ m) :
    expectation (A.eval₂ C Q3 * P3 ^ m) =
      (m.factorial : ℂ) * (A * (1 + Polynomial.X) ^ (m - 1)).coeff m := by
  rw [← normalizedSub3_polyAt, P3, ← map_pow, ← map_mul,
    expectation_normalizedSub3, naturalMoment3_master A m hm]

/-- Proposition 4.1, full arbitrary-polynomial coefficient identity with actual Gaussian
expectations. -/
theorem master_four (A : Polynomial ℂ) (m : ℕ) (hm : 1 ≤ m) :
    expectation (A.eval₂ C Q4 * P4 ^ m) =
      (m.factorial : ℂ) * (A * (1 + Polynomial.X) ^ (m - 1)).coeff m := by
  rw [← normalizedSub4_polyAt, P4, ← map_pow, ← map_mul,
    expectation_normalizedSub4, naturalMoment4_master A m hm]

theorem P3_moment (m : ℕ) (hm : 1 ≤ m) : expectation (P3 ^ m) = 0 := by
  have h := master_three 1 m hm
  rw [master_coefficient_one m hm, mul_zero] at h
  simpa only [Polynomial.eval₂_one, one_mul] using h

theorem Q3_P3_moment (m : ℕ) (hm : 1 ≤ m) :
    expectation (Q3 * P3 ^ m) = (m.factorial : ℂ) := by
  simpa only [Polynomial.eval₂_X, master_coefficient_X m hm, mul_one]
    using master_three Polynomial.X m hm

theorem P4_moment (m : ℕ) (hm : 1 ≤ m) : expectation (P4 ^ m) = 0 := by
  have h := master_four 1 m hm
  rw [master_coefficient_one m hm, mul_zero] at h
  simpa only [Polynomial.eval₂_one, one_mul] using h

theorem Q4_P4_moment (m : ℕ) (hm : 1 ≤ m) :
    expectation (Q4 * P4 ^ m) = (m.factorial : ℂ) := by
  simpa only [Polynomial.eval₂_X, master_coefficient_X m hm, mul_one]
    using master_four Polynomial.X m hm

theorem Q3_P3_moment_ne_zero (m : ℕ) (hm : 1 ≤ m) :
    expectation (Q3 * P3 ^ m) ≠ 0 := by
  rw [Q3_P3_moment m hm]
  exact_mod_cast m.factorial_ne_zero

theorem Q4_P4_moment_ne_zero (m : ℕ) (hm : 1 ≤ m) :
    expectation (Q4 * P4 ^ m) ≠ 0 := by
  rw [Q4_P4_moment m hm]
  exact_mod_cast m.factorial_ne_zero

theorem Q3_ne_zero : Q3 ≠ 0 := by
  intro h
  have := Q3_P3_moment_ne_zero 1 (by decide)
  simp [h] at this

theorem Q4_ne_zero : Q4 ≠ 0 := by
  intro h
  have := Q4_P4_moment_ne_zero 1 (by decide)
  simp [h] at this

/-- Explicit witnesses violate the eventual-vanishing quantifier of GMC(3). -/
theorem not_GMC_three : ¬ GMC 3 := by
  intro h
  obtain ⟨N, hN⟩ := h P3 P3_moment Q3
  exact Q3_P3_moment_ne_zero (max N 1) (le_max_right _ _) (hN _ (le_max_left _ _))

/-- Corollary 5.2, including all higher-dimensional Gaussian marginal compatibility. -/
theorem not_GMC_of_three_le (n : ℕ) (hn : 3 ≤ n) : ¬ GMC n :=
  not_GMC_of_le hn not_GMC_three

/-- A direct four-variable witness, separately from extending the three-variable example. -/
theorem not_GMC_four : ¬ GMC 4 := by
  intro h
  obtain ⟨N, hN⟩ := h P4 P4_moment Q4
  exact Q4_P4_moment_ne_zero (max N 1) (le_max_right _ _) (hN _ (le_max_left _ _))

/-- This is dimension extension, not a formalization of the Jacobian-reduction route. -/
theorem not_GMC_158 : ¬ GMC 158 := not_GMC_of_three_le 158 (by decide)

end GaussianMomentsCounterexamples
