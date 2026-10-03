/-
Copyright (c) 2026 long-mathematics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher D. Long
-/
module

public import LeanPool.GaussianMomentsCounterexamples.ComplexContractions
public import LeanPool.GaussianMomentsCounterexamples.AlgebraicMoments

/-! Agreement of the natural-coordinate algebraic moment functionals with actual integrals. -/

public section
noncomputable section
open MeasureTheory ProbabilityTheory MvPolynomial
namespace GaussianMomentsCounterexamples

lemma normalizedSub3_monomial (d : Fin 3 →₀ ℕ) (c : ℂ) :
    normalizedSub3 (monomial d c) = C c *
      (normalizedW 0 1 ^ d 0 * normalizedZ 0 1 ^ d 1 * (X 2 : MvPolynomial (Fin 3) ℂ) ^ d 2)
        := by
  simp [normalizedSub3, aeval_monomial, Finsupp.prod_fintype, Fin.prod_univ_succ,
    mul_assoc]

lemma normalizedSub4_monomial (d : Fin 4 →₀ ℕ) (c : ℂ) :
    normalizedSub4 (monomial d c) = C c *
      (normalizedW 0 1 ^ d 0 * normalizedZ 0 1 ^ d 1 *
        (normalizedW 2 3 ^ d 2 * (normalizedZ 2 3 : MvPolynomial (Fin 4) ℂ) ^ d 3)) := by
  simp [normalizedSub4, aeval_monomial, Finsupp.prod_fintype, Fin.prod_univ_succ,
    mul_assoc]

/-- Full agreement, for every polynomial, of the three-coordinate functional and integration. -/
theorem expectation_normalizedSub3 (P : MvPolynomial (Fin 3) ℂ) :
    expectation (normalizedSub3 P) = naturalMoment3 P := by
  induction P using MvPolynomial.induction_on' with
  | monomial d c =>
    rw [normalizedSub3_monomial, expectation_C_mul]
    rw [expectation_pair_mul (by decide : (0 : Fin 3) ≠ 1) (d 0) (d 1) (X 2 ^ d 2)]
    · rw [expectation_X_pow, naturalMoment3_monomial]
      simp only [pairMoment]
    · simp [derivZ, Derivation.leibniz_pow, pderiv_X]
    · simp [derivW, Derivation.leibniz_pow, pderiv_X]
  | add P Q hP hQ => simp only [map_add, expectation_add, hP, hQ]

/-- Full agreement, for every polynomial, of the four-coordinate functional and integration. -/
theorem expectation_normalizedSub4 (P : MvPolynomial (Fin 4) ℂ) :
    expectation (normalizedSub4 P) = naturalMoment4 P := by
  induction P using MvPolynomial.induction_on' with
  | monomial d c =>
    rw [normalizedSub4_monomial, expectation_C_mul]
    rw [expectation_pair_mul (by decide : (0 : Fin 4) ≠ 1) (d 0) (d 1)
      (normalizedW 2 3 ^ d 2 * normalizedZ 2 3 ^ d 3)]
    · rw [expectation_pair (by decide : (2 : Fin 4) ≠ 3), naturalMoment4_monomial]
      simp only [pairMoment]
    · simp [derivZ, normalizedW, normalizedZ, Derivation.leibniz_pow, pderiv_X]
    · simp [derivW, normalizedW, normalizedZ, Derivation.leibniz_pow, pderiv_X]
  | add P Q hP hQ => simp only [map_add, expectation_add, hP, hQ]

end GaussianMomentsCounterexamples
