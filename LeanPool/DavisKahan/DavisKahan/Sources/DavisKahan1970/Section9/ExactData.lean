/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/

import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Ext
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Davis--Kahan 1970, Section 9: exact finite data

This file records the exact two-dimensional algebra used by the numerical
example.  It deliberately separates the finite calculations from the analytic
construction of the free-beam fourth-derivative operator.  The real analytic
model in `DavisKahan.Specialized.FreeBeam.BeamSection9Real` discharges this
certificate boundary by proving that the paper's real free-beam realization has
exactly the data defined here.

The primary quantities are kept in radical form.  Decimal values used in the
paper are derived later as rational upper bounds.
-/

namespace TauCeti
namespace DavisKahan1970
namespace Section9

/-- A symmetric real two-by-two matrix, represented by its upper-triangular
entries.  This small record keeps the numerical layer independent of matrix
indexing details. -/
@[ext]
structure SymmetricTwoByTwo where
  /-- The first diagonal entry of the real symmetric two-by-two matrix. -/
  a₀₀ : ℝ
  /-- The common off-diagonal entry of the real symmetric two-by-two matrix. -/
  a₀₁ : ℝ
  /-- The second diagonal entry of the real symmetric two-by-two matrix. -/
  a₁₁ : ℝ

namespace SymmetricTwoByTwo

/-- Trace of a symmetric two-by-two matrix. -/
def trace (M : SymmetricTwoByTwo) : ℝ := M.a₀₀ + M.a₁₁

/-- Determinant of a symmetric two-by-two matrix. -/
def det (M : SymmetricTwoByTwo) : ℝ := M.a₀₀ * M.a₁₁ - M.a₀₁ ^ 2

/-- Characteristic polynomial evaluated at a real scalar. -/
def charAt (M : SymmetricTwoByTwo) (lam : ℝ) : ℝ :=
  (M.a₀₀ - lam) * (M.a₁₁ - lam) - M.a₀₁ ^ 2

end SymmetricTwoByTwo

-- every constant below is built from real division and `Real.sqrt`, both of
-- which are noncomputable
section

/-- The exact coefficient of the lower Ritz value.  We write `sqrt 3 / 3`
instead of `1 / sqrt 3`; the equality is proved below. -/
noncomputable def ritzLowCoefficient : ℝ := (1 - Real.sqrt 3 / 3) / 2

/-- The exact coefficient of the upper Ritz value. -/
noncomputable def ritzHighCoefficient : ℝ := (1 + Real.sqrt 3 / 3) / 2

/-- The two Ritz values in equation (9.5). -/
noncomputable def ritzLow (ε : ℝ) : ℝ := ε * ritzLowCoefficient

/-- The upper Ritz value of equation (9.5).  Stated separately from `ritzLow` so that
each declaration carries its own documentation. -/
noncomputable def ritzHigh (ε : ℝ) : ℝ := ε * ritzHighCoefficient

/-- The residual Gram matrix before Rayleigh--Ritz recentering. -/
noncomputable def residualGram (ε : ℝ) : SymmetricTwoByTwo where
  a₀₀ := ε ^ 2 / 30 * (11 - Real.sqrt 75)
  a₀₁ := -(ε ^ 2 / 30)
  a₁₁ := ε ^ 2 / 30 * (11 + Real.sqrt 75)

/-- The two eigenvalues of the initial residual Gram matrix. -/
noncomputable def residualGramEigenvalueLow (ε : ℝ) : ℝ :=
  ε ^ 2 / 30 * (11 - Real.sqrt 76)

/-- The larger eigenvalue of the initial residual Gram matrix. -/
noncomputable def residualGramEigenvalueHigh (ε : ℝ) : ℝ :=
  ε ^ 2 / 30 * (11 + Real.sqrt 76)

/-- The residual Gram matrix after Rayleigh--Ritz recentering. -/
noncomputable def orthogonalResidualGram (ε : ℝ) : SymmetricTwoByTwo where
  a₀₀ := ε ^ 2 / 30
  a₀₁ := -(ε ^ 2 / 30)
  a₁₁ := ε ^ 2 / 30

/-- Exact largest singular value of the initial residual. -/
noncomputable def residualTopSingularValue (ε : ℝ) : ℝ :=
  |ε| * Real.sqrt ((11 + Real.sqrt 76) / 30)

/-- Exact smaller singular value of the initial residual. -/
noncomputable def residualBottomSingularValue (ε : ℝ) : ℝ :=
  |ε| * Real.sqrt ((11 - Real.sqrt 76) / 30)

/-- Sum of the two singular values of the initial residual. -/
noncomputable def residualKyFanTwo (ε : ℝ) : ℝ :=
  residualTopSingularValue ε + residualBottomSingularValue ε

/-- The unique nonzero singular value of the recentered residual. -/
noncomputable def orthogonalResidualSingularValue (ε : ℝ) : ℝ :=
  |ε| * (Real.sqrt 15 / 15)

/-- The norm of either recentered residual column. -/
noncomputable def orthogonalResidualColumnNorm (ε : ℝ) : ℝ :=
  |ε| * (Real.sqrt 30 / 30)

/-- `(√3)⁻¹ = √3 / 3`.  The radical is kept in the numerator throughout this file, so
this is the normalisation the Ritz coefficients are stated against. -/
lemma inv_sqrt_three_eq : (Real.sqrt 3)⁻¹ = Real.sqrt 3 / 3 := by
  have hs : Real.sqrt (3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt (3 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  apply (eq_div_iff (by norm_num : (3 : ℝ) ≠ 0)).2
  field_simp [hn]
  nlinarith

/-- The two Ritz values sum to `ε`: the pair is centred on `ε / 2`. -/
lemma ritzLow_add_ritzHigh (ε : ℝ) : ritzLow ε + ritzHigh ε = ε := by
  unfold ritzLow ritzHigh ritzLowCoefficient ritzHighCoefficient
  ring

/-- The Ritz gap is `ε · √3 / 3`, i.e. `ε / √3`. -/
lemma ritzHigh_sub_ritzLow (ε : ℝ) :
    ritzHigh ε - ritzLow ε = ε * (Real.sqrt 3 / 3) := by
  unfold ritzLow ritzHigh ritzLowCoefficient ritzHighCoefficient
  ring

/-- Trace of the initial residual Gram matrix: `11 ε² / 15`. -/
lemma residualGram_trace (ε : ℝ) :
    (residualGram ε).trace = 11 * ε ^ 2 / 15 := by
  unfold residualGram SymmetricTwoByTwo.trace
  ring

/-- Determinant of the initial residual Gram matrix: `ε⁴ / 20`. -/
lemma residualGram_det (ε : ℝ) :
    (residualGram ε).det = ε ^ 4 / 20 := by
  have hs : Real.sqrt (75 : ℝ) ^ 2 = 75 := Real.sq_sqrt (by norm_num)
  unfold residualGram SymmetricTwoByTwo.det
  -- `det = ε⁴/900 * (121 - √75²) - ε⁴/900 = ε⁴/900 * 45 = ε⁴/20`
  linear_combination (-(ε ^ 4) / 900) * hs

/-- The lower eigenvalue satisfies the characteristic equation of the residual Gram
matrix. -/
lemma residualGram_eigenvalueLow_charAt (ε : ℝ) :
    (residualGram ε).charAt (residualGramEigenvalueLow ε) = 0 := by
  have h75 : Real.sqrt (75 : ℝ) ^ 2 = 75 := Real.sq_sqrt (by norm_num)
  have h76 : Real.sqrt (76 : ℝ) ^ 2 = 76 := Real.sq_sqrt (by norm_num)
  unfold residualGram residualGramEigenvalueLow SymmetricTwoByTwo.charAt
  -- with `k = ε²/30` the product telescopes to `k²(√76² - √75²) - k²`
  linear_combination (-(ε ^ 4) / 900) * h75 + (ε ^ 4 / 900) * h76

/-- The upper eigenvalue satisfies the characteristic equation of the residual Gram
matrix. -/
lemma residualGram_eigenvalueHigh_charAt (ε : ℝ) :
    (residualGram ε).charAt (residualGramEigenvalueHigh ε) = 0 := by
  have h75 : Real.sqrt (75 : ℝ) ^ 2 = 75 := Real.sq_sqrt (by norm_num)
  have h76 : Real.sqrt (76 : ℝ) ^ 2 = 76 := Real.sq_sqrt (by norm_num)
  unfold residualGram residualGramEigenvalueHigh SymmetricTwoByTwo.charAt
  -- the high root gives the same reduction with both factors negated
  linear_combination (-(ε ^ 4) / 900) * h75 + (ε ^ 4 / 900) * h76

/-- Trace of the orthogonal residual Gram matrix: `ε² / 15`. -/
lemma orthogonalResidualGram_trace (ε : ℝ) :
    (orthogonalResidualGram ε).trace = ε ^ 2 / 15 := by
  unfold orthogonalResidualGram SymmetricTwoByTwo.trace
  ring

/-- The orthogonal residual Gram matrix is singular — its determinant vanishes, so the
residual has rank one. -/
lemma orthogonalResidualGram_det (ε : ℝ) :
    (orthogonalResidualGram ε).det = 0 := by
  unfold orthogonalResidualGram SymmetricTwoByTwo.det
  ring

/-- Zero is an eigenvalue of the orthogonal residual Gram matrix, as its vanishing
determinant requires. -/
lemma orthogonalResidualGram_zero_charAt (ε : ℝ) :
    (orthogonalResidualGram ε).charAt 0 = 0 := by
  unfold orthogonalResidualGram SymmetricTwoByTwo.charAt
  ring

/-- `ε² / 15` is the other eigenvalue: with the zero eigenvalue it accounts for the
whole trace. -/
lemma orthogonalResidualGram_nonzero_charAt (ε : ℝ) :
    (orthogonalResidualGram ε).charAt (ε ^ 2 / 15) = 0 := by
  unfold orthogonalResidualGram SymmetricTwoByTwo.charAt
  ring

/-- `√76 ≤ 11`.  This keeps `11 - √76` nonnegative, which is what makes the lower
residual Gram eigenvalue nonnegative. -/
lemma sqrt76_le_eleven : Real.sqrt 76 ≤ 11 := by
  nlinarith [Real.sqrt_nonneg (76 : ℝ), Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 76)]

/-- The lower residual Gram eigenvalue is nonnegative, so it is the square of a real
singular value. -/
lemma residualGramEigenvalueLow_nonneg (ε : ℝ) :
    0 ≤ residualGramEigenvalueLow ε := by
  unfold residualGramEigenvalueLow
  -- `positivity` cannot see that the second factor is nonnegative
  exact mul_nonneg (by positivity) (by linarith [sqrt76_le_eleven])

/-- The upper residual Gram eigenvalue is nonnegative, so it is the square of a real
singular value. -/
lemma residualGramEigenvalueHigh_nonneg (ε : ℝ) :
    0 ≤ residualGramEigenvalueHigh ε := by
  unfold residualGramEigenvalueHigh
  positivity

/-- The top residual singular value squares to the upper Gram eigenvalue. -/
lemma residualTopSingularValue_sq (ε : ℝ) :
    residualTopSingularValue ε ^ 2 = residualGramEigenvalueHigh ε := by
  have hq : 0 ≤ (11 + Real.sqrt 76) / 30 := by positivity
  unfold residualTopSingularValue residualGramEigenvalueHigh
  rw [mul_pow, sq_abs, Real.sq_sqrt hq]
  ring

/-- The bottom residual singular value squares to the lower Gram eigenvalue. -/
lemma residualBottomSingularValue_sq (ε : ℝ) :
    residualBottomSingularValue ε ^ 2 = residualGramEigenvalueLow ε := by
  have hq : 0 ≤ (11 - Real.sqrt 76) / 30 := by
    have h := sqrt76_le_eleven
    positivity
  unfold residualBottomSingularValue residualGramEigenvalueLow
  rw [mul_pow, sq_abs, Real.sq_sqrt hq]
  ring

/-- The single nonzero orthogonal-residual singular value squares to `ε² / 15`. -/
lemma orthogonalResidualSingularValue_sq (ε : ℝ) :
    orthogonalResidualSingularValue ε ^ 2 = ε ^ 2 / 15 := by
  have hs : Real.sqrt (15 : ℝ) ^ 2 = 15 := Real.sq_sqrt (by norm_num)
  unfold orthogonalResidualSingularValue
  rw [mul_pow, sq_abs]
  nlinarith

/-- Each orthogonal-residual column has squared norm `ε² / 30` — half the nonzero
singular value squared, the two columns splitting it evenly. -/
lemma orthogonalResidualColumnNorm_sq (ε : ℝ) :
    orthogonalResidualColumnNorm ε ^ 2 = ε ^ 2 / 30 := by
  have hs : Real.sqrt (30 : ℝ) ^ 2 = 30 := Real.sq_sqrt (by norm_num)
  unfold orthogonalResidualColumnNorm
  rw [mul_pow, sq_abs]
  nlinarith

end

/-- Exact finite-data package required from an analytic realization of the
Section 9 free-beam example.  The record is a theorem boundary, not an
assumption installed globally: any concrete model must construct a value of
this type. -/
structure FreeBeamFiniteDataCertificate (ε : ℝ) where
  epsilon_pos : 0 < ε
  epsilon_lt_hundred : ε < 100
  /-- The value used in the third-eigenvalue lower-bound certificate. -/
  thirdEigenvalue : ℝ
  third_eigenvalue_gt_five_hundred : 500 < thirdEigenvalue
  /-- The initial two-by-two residual Gram matrix. -/
  initialResidualGram : SymmetricTwoByTwo
  initial_residual_gram_eq : initialResidualGram = residualGram ε
  /-- The lower Ritz value of the finite beam calculation. -/
  ritzLow : ℝ
  /-- The upper Ritz value of the finite beam calculation. -/
  ritzHigh : ℝ
  ritz_low_eq : ritzLow = Section9.ritzLow ε
  ritz_high_eq : ritzHigh = Section9.ritzHigh ε
  /-- The residual Gram matrix after orthogonal recentering. -/
  recenteredResidualGram : SymmetricTwoByTwo
  recentered_residual_gram_eq : recenteredResidualGram = orthogonalResidualGram ε

end Section9
end DavisKahan1970
end TauCeti
