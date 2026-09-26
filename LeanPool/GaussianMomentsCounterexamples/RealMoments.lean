/-
Copyright (c) 2026 long-mathematics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher D. Long
-/
module

public import LeanPool.GaussianMomentsCounterexamples.GaussianMeasure
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

/-! All-order Gaussian moments from integration by parts. -/

public section

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace GaussianMomentsCounterexamples

lemma integrable_pow_mul_density (n : ℕ) :
    Integrable (fun x : ℝ => x ^ n * gaussianPDFReal 0 1 x) := by
  have h := integrable_real_pow n
  rw [gaussianReal_of_var_ne_zero _ (by norm_num : (1 : ℝ≥0) ≠ 0)] at h
  have ht := (integrable_withDensity_iff_integrable_smul'
    (measurable_gaussianPDF 0 1)
    (ae_of_all _ fun x => gaussianPDF_lt_top (μ := 0) (v := 1) (x := x))).mp h
  simpa [gaussianPDF, ENNReal.toReal_ofReal, gaussianPDFReal_nonneg, mul_comm] using ht

lemma hasDerivAt_standardGaussianDensity (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1) (-x * gaussianPDFReal 0 1 x) x := by
  have h := (((hasDerivAt_id x).pow 2).neg.div_const 2).exp.const_mul
    ((Real.sqrt (2 * Real.pi))⁻¹)
  convert h using 1
  · ext y
    simp [gaussianPDFReal]
  · simp [gaussianPDFReal]
    ring

/-- Gaussian integration by parts gives the all-order real moment recurrence. -/
theorem real_gaussian_moment_recurrence (n : ℕ) :
    (∫ x : ℝ, x ^ (n + 2) ∂gaussianReal 0 1) =
      (n + 1 : ℝ) * ∫ x : ℝ, x ^ n ∂gaussianReal 0 1 := by
  have h := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := fun x : ℝ => x ^ (n + 1))
    (u' := fun x : ℝ => (n + 1 : ℝ) * x ^ n)
    (v := gaussianPDFReal 0 1)
    (v' := fun x : ℝ => -x * gaussianPDFReal 0 1 x)
    (fun x _ => by convert hasDerivAt_pow (n + 1) x using 1; simp)
    (fun x _ => hasDerivAt_standardGaussianDensity x)
    (by
      convert (integrable_pow_mul_density (n + 2)).neg using 1
      ext x
      simp [pow_succ]
      ring)
    (by
      change Integrable (fun x : ℝ => (n + 1 : ℝ) * x ^ n * gaussianPDFReal 0 1 x)
      simpa only [mul_assoc] using (integrable_pow_mul_density n).const_mul (n + 1 : ℝ))
    (integrable_pow_mul_density (n + 1))
  simp only [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0),
    smul_eq_mul]
  have heq : (fun x : ℝ => x ^ (n + 1) * (-x * gaussianPDFReal 0 1 x)) =
      fun x => -(gaussianPDFReal 0 1 x * x ^ (n + 2)) := by
    funext x
    simp [pow_succ]
    ring
  rw [heq, integral_neg] at h
  rw [← integral_const_mul]
  have h' := neg_injective h
  convert h' using 1
  congr 1
  funext x
  ring

theorem real_gaussian_moment_zero :
    (∫ x : ℝ, x ^ 0 ∂gaussianReal 0 1) = 1 := by simp

theorem real_gaussian_moment_one :
    (∫ x : ℝ, x ^ 1 ∂gaussianReal 0 1) = 0 := by
  simp [integral_id_gaussianReal]

theorem real_gaussian_odd_moment (n : ℕ) :
    (∫ x : ℝ, x ^ (2 * n + 1) ∂gaussianReal 0 1) = 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by omega,
      real_gaussian_moment_recurrence, ih, mul_zero]

theorem complex_gaussian_moment_eq_real (n : ℕ) :
    (∫ x : ℝ, (x : ℂ) ^ n ∂gaussianReal 0 1) =
      ((∫ x : ℝ, x ^ n ∂gaussianReal 0 1 : ℝ) : ℂ) := by
  rw [← integral_complex_ofReal]
  congr 1
  ext x
  exact (Complex.ofReal_pow x n).symm

/-- The recurrence in the form used for polynomial Gaussian integration by parts. -/
theorem complex_gaussian_moment_succ (k : ℕ) :
    (∫ x : ℝ, (x : ℂ) ^ (k + 1) ∂gaussianReal 0 1) =
      (k : ℂ) * ∫ x : ℝ, (x : ℂ) ^ (k - 1) ∂gaussianReal 0 1 := by
  simp only [complex_gaussian_moment_eq_real]
  cases k with
  | zero => simp
  | succ k =>
    rw [show k.succ + 1 = k + 2 by omega, real_gaussian_moment_recurrence]
    simp

theorem complex_gaussian_odd_moment (n : ℕ) :
    (∫ x : ℝ, (x : ℂ) ^ (2 * n + 1) ∂gaussianReal 0 1) = 0 := by
  rw [complex_gaussian_moment_eq_real, real_gaussian_odd_moment, Complex.ofReal_zero]

/-- The even moments of the standard Gaussian, valid at every order. -/
theorem real_gaussian_even_moment (n : ℕ) :
    (∫ x : ℝ, x ^ (2 * n) ∂gaussianReal 0 1) =
      ((2 * n).factorial : ℝ) / (2 ^ n * (n.factorial : ℝ)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 2 by omega, real_gaussian_moment_recurrence, ih]
    rw [show 2 * n + 2 = (2 * n + 1) + 1 by omega,
      Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ, pow_succ]
    push_cast
    have hn : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
    have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    ring

theorem complex_gaussian_even_moment (n : ℕ) :
    (∫ x : ℝ, (x : ℂ) ^ (2 * n) ∂gaussianReal 0 1) =
      ((2 * n).factorial : ℂ) / (2 ^ n * (n.factorial : ℂ)) := by
  rw [complex_gaussian_moment_eq_real, real_gaussian_even_moment]
  push_cast
  rfl

alias integral_complex_pow_succ := complex_gaussian_moment_succ

end GaussianMomentsCounterexamples
