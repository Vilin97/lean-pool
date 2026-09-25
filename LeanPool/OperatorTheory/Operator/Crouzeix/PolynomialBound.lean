/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
module


public import Mathlib.Analysis.SpecificLimits.Normed
public import LeanPool.OperatorTheory.Operator.Crouzeix.BoundaryMaximum
public import LeanPool.OperatorTheory.Operator.Crouzeix.SmoothSupportDomain

/-!
# Direct polynomial consequences of the Crouzeix--Palencia theorem

The spectral-set statement is naturally formulated on the closed numerical
range because the spectrum need not lie in the numerical range itself.
Polynomial sup norms, however, are unchanged by closing a bounded set.  This
file records the standard norm inequality directly on the numerical range and
specializes it to powers, centered operators, and the numerical radius.
-/

@[expose] public section

open Complex Set
open scoped InnerProductSpace Polynomial

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Closing the numerical range does not alter a polynomial sup norm. -/
theorem polynomialSupNorm_closure_numericalRange
    (A : E →L[ℂ] E) (p : ℂ[X]) :
    polynomialSupNorm p (closure (numericalRange A)) =
      polynomialSupNorm p (numericalRange A) :=
  polynomialSupNorm_closure_of_isBounded p (isBounded_numericalRange A)

/-- The polynomial sup norm of `X` on the numerical range is the numerical
radius. -/
theorem polynomialSupNorm_X_numericalRange (A : E →L[ℂ] E) :
    polynomialSupNorm Polynomial.X (numericalRange A) =
      numericalRadius A := by
  simp only [polynomialSupNorm, Polynomial.eval_X, numericalRadius]

/-- The supremum of the `n`th powers on the numerical range is bounded by
the `n`th power of the numerical radius. -/
theorem iSup_norm_pow_numericalRange_le_numericalRadius_pow
    (A : E →L[ℂ] E) (n : ℕ) :
    (⨆ z ∈ numericalRange A, ‖z ^ n‖) ≤ numericalRadius A ^ n := by
  refine Real.iSup_le (fun z => ?_) (pow_nonneg (numericalRadius_nonneg A) n)
  refine Real.iSup_le (fun hz => ?_) (pow_nonneg (numericalRadius_nonneg A) n)
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg z) (norm_le_numericalRadius A hz) n

variable [CompleteSpace E]

/-- The usual norm form of the Crouzeix--Palencia theorem, with the supremum
taken directly over the numerical range. -/
theorem norm_aeval_le_one_add_sqrt_two_mul_polynomialSupNorm_numericalRange
    (A : E →L[ℂ] E) (p : ℂ[X]) :
    ‖Polynomial.aeval A p‖ ≤
      (1 + Real.sqrt 2) * polynomialSupNorm p (numericalRange A) := by
  rw [← polynomialSupNorm_closure_numericalRange A p]
  exact (crouzeix_palencia A).2 p

/-- The Crouzeix--Palencia numerical-radius bound for an operator. -/
theorem norm_le_one_add_sqrt_two_mul_numericalRadius
    (A : E →L[ℂ] E) :
    ‖A‖ ≤ (1 + Real.sqrt 2) * numericalRadius A := by
  simpa only [Polynomial.aeval_X,
    polynomialSupNorm_X_numericalRange] using
      norm_aeval_le_one_add_sqrt_two_mul_polynomialSupNorm_numericalRange
        A Polynomial.X

/-- The Crouzeix--Palencia numerical-radius bound centered at an arbitrary
scalar operator. -/
theorem norm_sub_smul_one_le_one_add_sqrt_two_mul_numericalRadius
    (A : E →L[ℂ] E) (c : ℂ) :
    ‖A - c • (1 : E →L[ℂ] E)‖ ≤
      (1 + Real.sqrt 2) *
        numericalRadius (A - c • (1 : E →L[ℂ] E)) :=
  norm_le_one_add_sqrt_two_mul_numericalRadius
    (A - c • (1 : E →L[ℂ] E))

/-- Every power of an operator is controlled by the corresponding power on
its numerical range. -/
theorem norm_pow_le_one_add_sqrt_two_mul_iSup_numericalRange
    (A : E →L[ℂ] E) (n : ℕ) :
    ‖A ^ n‖ ≤
      (1 + Real.sqrt 2) * ⨆ z ∈ numericalRange A, ‖z ^ n‖ := by
  simpa only [Polynomial.aeval_X_pow, polynomialSupNorm,
    Polynomial.eval_X_pow] using
      norm_aeval_le_one_add_sqrt_two_mul_polynomialSupNorm_numericalRange
        A (Polynomial.X ^ n)

/-- Every operator power is controlled directly by the corresponding power
of the numerical radius with the Crouzeix--Palencia constant. -/
theorem norm_pow_le_one_add_sqrt_two_mul_numericalRadius_pow
    (A : E →L[ℂ] E) (n : ℕ) :
    ‖A ^ n‖ ≤ (1 + Real.sqrt 2) * numericalRadius A ^ n := by
  exact (norm_pow_le_one_add_sqrt_two_mul_iSup_numericalRange A n).trans
    (mul_le_mul_of_nonneg_left
      (iSup_norm_pow_numericalRange_le_numericalRadius_pow A n) (by positivity))

/-- Every centered operator power is controlled by the corresponding power
of its centered numerical radius. -/
theorem norm_pow_sub_smul_one_le_one_add_sqrt_two_mul_numericalRadius_pow
    (A : E →L[ℂ] E) (c : ℂ) (n : ℕ) :
    ‖(A - c • (1 : E →L[ℂ] E)) ^ n‖ ≤
      (1 + Real.sqrt 2) *
        numericalRadius (A - c • (1 : E →L[ℂ] E)) ^ n :=
  norm_pow_le_one_add_sqrt_two_mul_numericalRadius_pow
    (A - c • (1 : E →L[ℂ] E)) n

/-- Operators in the numerical-radius unit ball are uniformly power-bounded
by the Crouzeix--Palencia constant. -/
theorem norm_pow_le_one_add_sqrt_two_of_numericalRadius_le_one
    (A : E →L[ℂ] E) (hA : numericalRadius A ≤ 1) (n : ℕ) :
    ‖A ^ n‖ ≤ 1 + Real.sqrt 2 := by
  calc
    ‖A ^ n‖ ≤ (1 + Real.sqrt 2) * numericalRadius A ^ n :=
      norm_pow_le_one_add_sqrt_two_mul_numericalRadius_pow A n
    _ ≤ (1 + Real.sqrt 2) * 1 := mul_le_mul_of_nonneg_left
      (pow_le_one₀ (numericalRadius_nonneg A) hA) (by positivity)
    _ = 1 + Real.sqrt 2 := mul_one _

/-- A centered operator in the numerical-radius unit ball is uniformly
power-bounded by the Crouzeix--Palencia constant. -/
theorem norm_pow_sub_smul_one_le_one_add_sqrt_two_of_numericalRadius_le_one
    (A : E →L[ℂ] E) (c : ℂ)
    (hA : numericalRadius (A - c • (1 : E →L[ℂ] E)) ≤ 1) (n : ℕ) :
    ‖(A - c • (1 : E →L[ℂ] E)) ^ n‖ ≤ 1 + Real.sqrt 2 :=
  norm_pow_le_one_add_sqrt_two_of_numericalRadius_le_one
    (A - c • (1 : E →L[ℂ] E)) hA n

/-- If the numerical radius is strictly less than one, the operator powers
converge to zero in operator norm. -/
theorem tendsto_pow_atTop_nhds_zero_of_numericalRadius_lt_one
    (A : E →L[ℂ] E) (hA : numericalRadius A < 1) :
    Filter.Tendsto (fun n : ℕ => A ^ n) Filter.atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun n => norm_nonneg (A ^ n)
  · exact Filter.Eventually.of_forall fun n =>
      norm_pow_le_one_add_sqrt_two_mul_numericalRadius_pow A n
  · have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one
      (numericalRadius_nonneg A) hA
    simpa only [mul_zero] using hpow.const_mul (1 + Real.sqrt 2)

/-- If a centered numerical radius is strictly less than one, the powers of
the centered operator converge to zero in operator norm. -/
theorem tendsto_pow_sub_smul_one_atTop_nhds_zero_of_numericalRadius_lt_one
    (A : E →L[ℂ] E) (c : ℂ)
    (hA : numericalRadius (A - c • (1 : E →L[ℂ] E)) < 1) :
    Filter.Tendsto
      (fun n : ℕ => (A - c • (1 : E →L[ℂ] E)) ^ n)
      Filter.atTop (nhds 0) :=
  tendsto_pow_atTop_nhds_zero_of_numericalRadius_lt_one
    (A - c • (1 : E →L[ℂ] E)) hA

/-- A centered form of the bound: the distance of `A` from a scalar operator
is controlled by the farthest point of its numerical range from that scalar. -/
theorem norm_sub_smul_one_le_one_add_sqrt_two_mul_iSup_numericalRange
    (A : E →L[ℂ] E) (c : ℂ) :
    ‖A - c • (1 : E →L[ℂ] E)‖ ≤
      (1 + Real.sqrt 2) * ⨆ z ∈ numericalRange A, ‖z - c‖ := by
  have h :=
    norm_aeval_le_one_add_sqrt_two_mul_polynomialSupNorm_numericalRange
      A (Polynomial.X - Polynomial.C c)
  have hleft :
      Polynomial.aeval A (Polynomial.X - Polynomial.C c) =
        A - c • (1 : E →L[ℂ] E) := by
    rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C,
      Algebra.algebraMap_eq_smul_one]
  have hright :
      polynomialSupNorm (Polynomial.X - Polynomial.C c)
          (numericalRange A) =
        ⨆ z ∈ numericalRange A, ‖z - c‖ := by
    simp only [polynomialSupNorm, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C]
  rw [hleft, hright] at h
  exact h

/-- A product of two polynomial functional-calculus values is controlled
with a single Crouzeix--Palencia constant. -/
theorem norm_aeval_mul_aeval_le_one_add_sqrt_two_mul_iSup_numericalRange
    (A : E →L[ℂ] E) (p q : ℂ[X]) :
    ‖Polynomial.aeval A p * Polynomial.aeval A q‖ ≤
      (1 + Real.sqrt 2) *
        ⨆ z ∈ numericalRange A,
          ‖Polynomial.eval z p * Polynomial.eval z q‖ := by
  have h :=
    norm_aeval_le_one_add_sqrt_two_mul_polynomialSupNorm_numericalRange
      A (p * q)
  simpa only [map_mul, polynomialSupNorm, Polynomial.eval_mul] using h

/-- Powers of a polynomial functional-calculus value retain a single
Crouzeix--Palencia constant. -/
theorem norm_aeval_pow_le_one_add_sqrt_two_mul_iSup_numericalRange
    (A : E →L[ℂ] E) (p : ℂ[X]) (n : ℕ) :
    ‖Polynomial.aeval A p ^ n‖ ≤
      (1 + Real.sqrt 2) *
        ⨆ z ∈ numericalRange A, ‖Polynomial.eval z p ^ n‖ := by
  have h :=
    norm_aeval_le_one_add_sqrt_two_mul_polynomialSupNorm_numericalRange
      A (p ^ n)
  simpa only [map_pow, polynomialSupNorm, Polynomial.eval_pow] using h

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
