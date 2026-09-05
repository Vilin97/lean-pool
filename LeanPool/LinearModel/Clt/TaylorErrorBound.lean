/-
Copyright (c) 2026 Patrick Rubin-Delanchy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Rubin-Delanchy, Andrew Jones
-/
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Linear
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus


/-!
# A bound for the Taylor approximation error of exp(ix)

This file provides a bound for the norm of the Taylor approximation error for `exp(ix)` for `x ∈ ℝ`.

The main result is the following:

· `norm_cexp_mul_I_sub_taylor_le` — for all `n ∈ ℕ` and `x ∈ ℝ`,
  `‖exp(ix) - ∑_{k<n} (ix)ᵏ/k!‖ ≤ |x|ⁿ / n!`.
-/

namespace LeanPool.LinearModel

noncomputable section

open Complex Finset intervalIntegral MeasureTheory


section Definitions

/-- The order-`k` Taylor approximation error `Rₙ(x)` of `exp(ix)` at `0`. -/
private def taylorErr (n : ℕ) (x : ℝ) : ℂ :=
  cexp (x * I) - ∑ k ∈ range n, (x * I) ^ k / k.factorial

end Definitions


section IntermediateResults

/-- The map `t ↦ t·I` has derivative `I`. -/
private lemma hasDerivAt_ofReal_mul_I (x : ℝ) :
    HasDerivAt (fun t : ℝ ↦ t * I) I x :=
  (hasDerivAt_mul_const I).comp_ofReal

/-- The error vanishes at `0` for positive order. -/
private lemma taylorErr_succ_zero (n : ℕ) : taylorErr (n + 1) 0 = 0 := by
  simp only [taylorErr, Complex.ofReal_zero, zero_mul, Complex.exp_zero]
  rw [Finset.sum_range_succ']
  simp [zero_pow]

/-- The derivative of `R_{n+1}(x)` is `i · Rₙ(x)`. -/
private lemma hasDerivAt_taylorErr (n : ℕ) (x : ℝ) :
    HasDerivAt (fun t : ℝ => taylorErr (n + 1) t) (I * taylorErr n x) x := by
  -- Derivative of `t ↦ exp(it)` at `x` is `i · exp(ix)`
  have hexp : HasDerivAt (fun t : ℝ => cexp (t * I)) (I * cexp (x * I)) x := by
    have h : HasDerivAt (fun t : ℝ => cexp (t * I)) (cexp (x * I) * I) x :=
      (hasDerivAt_exp _).comp x (hasDerivAt_ofReal_mul_I x)
    rw [mul_comm (cexp (x * I)) I] at h
    exact h
  -- Derivative of the partial sum is `i` times the one-shorter partial sum
  have hsum : HasDerivAt
      (fun t : ℝ => ∑ k ∈ range (n + 1), (t * I) ^ k / (k.factorial))
      (I * ∑ k ∈ range n, (x * I) ^ k / (k.factorial)) x := by
    have hterm : ∀ k ∈ range (n + 1),
        HasDerivAt (fun t : ℝ => (t * I) ^ k / (k.factorial))
          ((k * (x * I) ^ (k - 1) * I) / (k.factorial)) x := by
      intro k _
      exact ((hasDerivAt_ofReal_mul_I x).fun_pow k).div_const (k.factorial)
    have hd := HasDerivAt.fun_sum hterm
    have hsum_eq :
        (∑ k ∈ range (n + 1), (k * (x * I) ^ (k - 1) * I) / (k.factorial))
          = I * ∑ k ∈ range n, (x * I) ^ k / (k.factorial) := by
      rw [Finset.mul_sum, Finset.sum_range_succ']
      simp only [Nat.cast_zero, zero_mul, zero_div, add_zero]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Nat.add_sub_cancel, Nat.factorial_succ]
      push_cast
      field_simp
    rw [← hsum_eq]
    exact hd
  simp only [taylorErr]
  rw [mul_sub]
  exact hexp.sub hsum

/-- FTC representation: `R_{n+1}(x) = ∫₀ˣ i · Rₙ(t) dt`. -/
private lemma ftc_taylorErr (n : ℕ) (x : ℝ) :
    ∫ t in 0..x, I * taylorErr n t = taylorErr (n + 1) x := by
  have hcont : Continuous (fun t : ℝ => I * taylorErr n t) :=
    continuous_const.mul (by unfold taylorErr; fun_prop)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => hasDerivAt_taylorErr n t) (hcont.intervalIntegrable _ _),
    taylorErr_succ_zero, sub_zero]

/-- `|∫₀ˣ |t|ⁿ dt| = |x|^{n+1}/(n+1)`. -/
private lemma abs_intervalIntegral_abs_pow (n : ℕ) (x : ℝ) :
    |∫ t in 0..x, |t| ^ n| = |x| ^ (n + 1) / (n + 1) := by
  rcases le_total 0 x with hx | hx
  · have hcong : (∫ t in 0..x, |t| ^ n) = ∫ t in 0..x, t ^ n :=
      intervalIntegral.integral_congr fun t ht => by
        rw [Set.uIcc_of_le hx] at ht; rw [abs_of_nonneg ht.1]
    rw [hcong, integral_pow, zero_pow (Nat.succ_ne_zero n), sub_zero,
      abs_of_nonneg (by positivity), abs_of_nonneg hx]
  · have hcong : (∫ t in 0..x, |t| ^ n) = ∫ t in 0..x, (-1) ^ n * t ^ n :=
      intervalIntegral.integral_congr fun t ht => by
        rw [Set.uIcc_of_ge hx] at ht; rw [abs_of_nonpos ht.2, neg_pow]
    rw [hcong, intervalIntegral.integral_const_mul, integral_pow,
      zero_pow (Nat.succ_ne_zero n), sub_zero, abs_mul, abs_pow, abs_neg, abs_one,
      one_pow, one_mul, abs_div, abs_pow, abs_of_pos (show (0 : ℝ) < (n : ℝ) + 1 by positivity)]

/-- Taylor approximation error bound for `exp(ix)` (auxiliary form, using `taylorErr`). -/
private lemma norm_taylorErr_le (n : ℕ) (x : ℝ) :
    ‖taylorErr n x‖ ≤ |x| ^ n / n.factorial := by
  induction n generalizing x with
  | zero =>
      simp only [taylorErr, range_zero, Finset.sum_empty, sub_zero, pow_zero,
        Nat.factorial_zero, Nat.cast_one, div_one]
      rw [Complex.norm_exp]
      simp
  | succ n ih =>
      rw [← ftc_taylorErr n x]
      calc ‖∫ t in 0..x, I * taylorErr n t‖
          ≤ |∫ t in 0..x, |t| ^ n / n.factorial| := by
            refine intervalIntegral.norm_integral_le_abs_of_norm_le
              (Filter.Eventually.of_forall fun t => ?_)
              (((continuous_abs.pow n).div_const _).intervalIntegrable _ _)
            rw [norm_mul, Complex.norm_I, one_mul]
            exact ih t
        _ = |x| ^ (n + 1) / (n + 1).factorial := by
            rw [intervalIntegral.integral_div, abs_div,
              abs_of_pos (show 0 < (n.factorial : ℝ) by exact_mod_cast Nat.factorial_pos n),
              abs_intervalIntegral_abs_pow, Nat.factorial_succ]
            push_cast
            field_simp

end IntermediateResults


section MainResults

/-- Taylor remainder bound for `exp(ix)`.  For all `k ∈ ℕ` and `x ∈ ℝ`,
`‖exp(ix) - ∑_{k<n} (ix)ᵏ/k!‖ ≤ |x|ⁿ / n!`. -/
lemma norm_cexp_mul_I_sub_taylor_le (n : ℕ) (x : ℝ) :
    ‖cexp (x * I) - ∑ k ∈ range n, (x * I) ^ k / k.factorial‖
      ≤ |x| ^ n / n.factorial :=
  norm_taylorErr_le n x


end MainResults

end
end LinearModel
end LeanPool
