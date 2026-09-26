/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
module


public import LeanPool.OperatorTheory.Operator.Crouzeix.PolynomialBound
public import LeanPool.OperatorTheory.Operator.NumericalRange.RadiusNormal
public import LeanPool.OperatorTheory.Operator.SpectralSet.Normal

/-!
# Sharp numerical-range bounds for normal operators

For a normal operator, continuous functional calculus improves the general
`1 + sqrt 2` Crouzeix--Palencia constant to `1`.  This file packages that
fact as a polynomial spectral-set theorem, rewrites the norm bound directly
on the numerical range, and obtains the classical identity `w(A) = ‖A‖`.
-/

@[expose] public section

open Complex Set
open scoped InnerProductSpace Polynomial

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

/-- The closed numerical range is a polynomial spectral set with sharp
constant `1` for every normal operator. -/
theorem isPolynomialSpectralSet_closure_numericalRange_of_isStarNormal
    (A : E →L[ℂ] E) [IsStarNormal A] :
    IsPolynomialSpectralSet A (closure (numericalRange A)) := by
  constructor
  · exact spectrum_subset_closure_numericalRange A
  · intro p
    simpa only [one_mul] using
      norm_aeval_le_polynomialSupNorm_of_isStarNormal A
        (isBounded_numericalRange A).isCompact_closure
        (spectrum_subset_closure_numericalRange A) p

/-- The sharp normal-operator polynomial bound, with the supremum taken
directly over the numerical range. -/
theorem norm_aeval_le_polynomialSupNorm_numericalRange_of_isStarNormal
    (A : E →L[ℂ] E) [IsStarNormal A] (p : ℂ[X]) :
    ‖Polynomial.aeval A p‖ ≤ polynomialSupNorm p (numericalRange A) := by
  rw [← polynomialSupNorm_closure_numericalRange A p]
  exact
    norm_aeval_le_polynomialSupNorm_of_isStarNormal A
      (isBounded_numericalRange A).isCompact_closure
      (spectrum_subset_closure_numericalRange A) p

/-- Products in the polynomial functional calculus of a normal operator
satisfy the sharp constant-one bound. -/
theorem norm_aeval_mul_aeval_le_iSup_numericalRange_of_isStarNormal
    (A : E →L[ℂ] E) [IsStarNormal A] (p q : ℂ[X]) :
    ‖Polynomial.aeval A p * Polynomial.aeval A q‖ ≤
      ⨆ z ∈ numericalRange A,
        ‖Polynomial.eval z p * Polynomial.eval z q‖ := by
  have h := norm_aeval_le_polynomialSupNorm_numericalRange_of_isStarNormal
    A (p * q)
  simpa only [map_mul, polynomialSupNorm, Polynomial.eval_mul] using h

/-- Powers in the polynomial functional calculus of a normal operator
satisfy the sharp constant-one bound. -/
theorem norm_aeval_pow_le_iSup_numericalRange_of_isStarNormal
    (A : E →L[ℂ] E) [IsStarNormal A] (p : ℂ[X]) (n : ℕ) :
    ‖Polynomial.aeval A p ^ n‖ ≤
      ⨆ z ∈ numericalRange A, ‖Polynomial.eval z p ^ n‖ := by
  have h := norm_aeval_le_polynomialSupNorm_numericalRange_of_isStarNormal
    A (p ^ n)
  simpa only [map_pow, polynomialSupNorm, Polynomial.eval_pow] using h

/-- Powers of a normal operator are bounded sharply by powers of its
numerical radius. -/
theorem norm_pow_le_numericalRadius_pow_of_isStarNormal
    (A : E →L[ℂ] E) [IsStarNormal A] (n : ℕ) :
    ‖A ^ n‖ ≤ numericalRadius A ^ n := by
  have h := norm_aeval_pow_le_iSup_numericalRange_of_isStarNormal
    A Polynomial.X n
  simp only [Polynomial.aeval_X, Polynomial.eval_X] at h
  exact h.trans (iSup_norm_pow_numericalRange_le_numericalRadius_pow A n)

/-- A normal operator in the numerical-radius unit ball is power-bounded by
one. -/
theorem norm_pow_le_one_of_isStarNormal_of_numericalRadius_le_one
    (A : E →L[ℂ] E) [IsStarNormal A]
    (hA : numericalRadius A ≤ 1) (n : ℕ) :
    ‖A ^ n‖ ≤ 1 := by
  exact (norm_pow_le_numericalRadius_pow_of_isStarNormal A n).trans
    (pow_le_one₀ (numericalRadius_nonneg A) hA)

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
