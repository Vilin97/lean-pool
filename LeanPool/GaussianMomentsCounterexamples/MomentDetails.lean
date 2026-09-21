/-
Copyright (c) 2026 long-mathematics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher D. Long
-/
module

public import LeanPool.GaussianMomentsCounterexamples.RealMoments
public import Mathlib.Data.Nat.Factorial.DoubleFactorial

/-! Factorial and double-factorial expressions for Gaussian moments. -/

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory
namespace GaussianMomentsCounterexamples

/-- The double-factorial version of every even Gaussian moment. At `k = 0`,
truncated natural subtraction gives `0!! = 1`, representing the conventional
value `(-1)!! = 1` in the manuscript. -/
theorem real_gaussian_even_moment_doubleFactorial (k : ℕ) :
    (∫ x : ℝ, x ^ (2*k) ∂gaussianReal 0 1) = ((2*k-1).doubleFactorial : ℝ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) = 2*k+2 by omega, real_gaussian_moment_recurrence, ih]
    rw [show 2*k+2-1=2*k+1 by omega, Nat.doubleFactorial_add_one]
    push_cast
    rfl

/-- The two closed forms of the real Gaussian moment agree, including order zero. -/
theorem gaussian_doubleFactorial_eq_factorial (k : ℕ) :
    ((2*k-1).doubleFactorial : ℝ) = ((2*k).factorial : ℝ) / (2^k * (k.factorial : ℝ)) := by
  rw [← real_gaussian_even_moment_doubleFactorial, real_gaussian_even_moment]

theorem complex_gaussian_even_moment_doubleFactorial (k : ℕ) :
    (∫ x : ℝ, (x : ℂ) ^ (2*k) ∂gaussianReal 0 1) = ((2*k-1).doubleFactorial : ℂ) := by
  rw [complex_gaussian_moment_eq_real, real_gaussian_even_moment_doubleFactorial]
  norm_cast

end GaussianMomentsCounterexamples
