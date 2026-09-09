/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

@[expose] public section

/-! A fixed polynomial has one uniform power bound on the whole range
x ≥ 1. This extracts an actual degree and constant for scalar cost formulas. -/

noncomputable section

namespace EulerPolynomialCost

def coefficientCost (p : Polynomial ℝ) : ℝ := 1+∑ n ∈ p.support, |p.coeff n|

theorem coefficientCost_pos (p : Polynomial ℝ) : 0 < coefficientCost p := by
  unfold coefficientCost
  positivity

theorem eval_bound (p : Polynomial ℝ) (x : ℝ) (hx : 1 ≤ x) :
    |p.eval x| ≤ coefficientCost p*x^p.natDegree := by
  classical
  rw [Polynomial.eval_eq_sum,Polynomial.sum]
  calc
    _ ≤ ∑ n ∈ p.support, |p.coeff n*x^n| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ p.support, |p.coeff n| * x^p.natDegree := by
      apply Finset.sum_le_sum
      intro n hn
      rw [abs_mul,abs_of_nonneg (pow_nonneg (zero_le_one.trans hx) n)]
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ hx (Polynomial.le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp
          hn)))
        (abs_nonneg _)
    _ = (∑ n ∈ p.support, |p.coeff n|)*x^p.natDegree := (Finset.sum_mul ..).symm
    _ ≤ coefficientCost p*x^p.natDegree :=
      mul_le_mul_of_nonneg_right (by unfold coefficientCost; linarith)
        (pow_nonneg (zero_le_one.trans hx) _)

end EulerPolynomialCost
