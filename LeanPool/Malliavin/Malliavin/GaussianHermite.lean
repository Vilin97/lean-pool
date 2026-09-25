/-
Copyright (c) 2026 The lean-malliavin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-malliavin contributors
-/
module

public import LeanPool.Malliavin.Malliavin.BrownianHermite
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Generalized Hermite polynomials under centered Gaussian laws

This file develops the Gaussian moment and orthogonality identities for the variance-parametrized
Hermite polynomials used by the Brownian chaos construction.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal

noncomputable
section

namespace Malliavin.BrownianIteratedConstruction

/-- Centered Gaussian moments satisfy the Stein recurrence. -/
theorem integral_pow_succ_centeredGaussian (variance : ℝ≥0) (n : ℕ) :
    (∫ x : ℝ, x ^ (n + 1) ∂gaussianReal 0 variance) =
      (variance : ℝ) * n * ∫ x : ℝ, x ^ (n - 1) ∂gaussianReal 0 variance := by
  have hmoment (k : ℕ) :
      (∫ x : ℝ, x ^ k ∂gaussianReal 0 variance) =
        iteratedDeriv k (mgf (fun x : ℝ ↦ x) (gaussianReal 0 variance)) 0 := by
    rw [iteratedDeriv_mgf_zero (by simp)]
    rfl
  rw [hmoment (n + 1), hmoment (n - 1), mgf_fun_id_gaussianReal]
  simp only [zero_mul, zero_add]
  have hderiv :
      deriv (fun t : ℝ ↦ Real.exp ((variance : ℝ) * t ^ 2 / 2)) =
        fun t ↦ (variance : ℝ) * t * Real.exp ((variance : ℝ) * t ^ 2 / 2) := by
    funext t
    rw [_root_.deriv_exp (by fun_prop)]
    simp only [deriv_div_const, differentiableAt_const, differentiableAt_fun_id,
      Nat.cast_ofNat, DifferentiableAt.fun_pow, deriv_fun_mul, deriv_const', zero_mul,
      deriv_fun_pow, Nat.add_one_sub_one, pow_one, deriv_id'', mul_one, zero_add]
    ring
  rw [iteratedDeriv_succ', hderiv]
  simp only [mul_assoc]
  rw [iteratedDeriv_const_mul_field]
  apply congrArg (fun z : ℝ ↦ (variance : ℝ) * z)
  have hmul := iteratedDeriv_mul (n := n) (x := (0 : ℝ))
    (f := id) (g := fun t : ℝ ↦ Real.exp ((variance : ℝ) * t ^ 2 / 2))
    (by fun_prop) (by fun_prop)
  change iteratedDeriv n
    (id * fun t : ℝ ↦ Real.exp ((variance : ℝ) * t ^ 2 / 2)) 0 = _
  rw [hmul]
  cases n with
  | zero => simp [iteratedDeriv_id]
  | succ n =>
      rw [Finset.sum_eq_single 1]
      · simp [iteratedDeriv_id]
      · intro b _hb hb1
        simp [iteratedDeriv_id, hb1]
      · simp

/-- The second moment of a centered real Gaussian is its variance. -/
theorem integral_sq_centeredGaussian (variance : ℝ≥0) :
    (∫ x : ℝ, x ^ 2 ∂gaussianReal 0 variance) = (variance : ℝ) := by
  have h := integral_pow_succ_centeredGaussian variance 1
  simpa using h

/-- The fourth moment of a centered real Gaussian is three times the squared variance. -/
theorem integral_pow_four_centeredGaussian (variance : ℝ≥0) :
    (∫ x : ℝ, x ^ 4 ∂gaussianReal 0 variance) = 3 * (variance : ℝ) ^ 2 := by
  rw [show (4 : ℕ) = 3 + 1 by norm_num,
    integral_pow_succ_centeredGaussian, integral_sq_centeredGaussian]
  ring

/-- Every polynomial is integrable under a centered Gaussian law. -/
theorem integrable_polynomial_centeredGaussian (variance : ℝ≥0) (p : Polynomial ℝ) :
    Integrable (fun x : ℝ ↦ p.eval x) (gaussianReal 0 variance) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      exact (hp.add hq).congr <| Filter.Eventually.of_forall fun x ↦ by
        simp only [Pi.add_apply, Polynomial.eval_add]
  | monomial n a =>
      simpa only [Polynomial.eval_monomial] using
        (integrable_pow_of_mem_interior_integrableExpSet
          (X := fun x : ℝ ↦ x) (by simp) n).const_mul a

/-- Gaussian integration by parts for real polynomials. -/
theorem integral_mul_polynomial_centeredGaussian (variance : ℝ≥0) (p : Polynomial ℝ) :
    (∫ x : ℝ, x * p.eval x ∂gaussianReal 0 variance) =
      (variance : ℝ) * ∫ x : ℝ, p.derivative.eval x ∂gaussianReal 0 variance := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      have hxp : Integrable (fun x : ℝ ↦ x * p.eval x)
          (gaussianReal 0 variance) := by
        refine (integrable_polynomial_centeredGaussian variance
          (Polynomial.X * p)).congr <| Filter.Eventually.of_forall fun x ↦ ?_
        simp only [Polynomial.eval_mul, Polynomial.eval_X]
      have hxq : Integrable (fun x : ℝ ↦ x * q.eval x)
          (gaussianReal 0 variance) := by
        refine (integrable_polynomial_centeredGaussian variance
          (Polynomial.X * q)).congr <| Filter.Eventually.of_forall fun x ↦ ?_
        simp only [Polynomial.eval_mul, Polynomial.eval_X]
      simp only [Polynomial.eval_add, mul_add, Polynomial.derivative_add]
      rw [integral_add hxp hxq,
        integral_add (integrable_polynomial_centeredGaussian variance p.derivative)
          (integrable_polynomial_centeredGaussian variance q.derivative), hp, hq]
      ring
  | monomial n a =>
      simp only [Polynomial.eval_monomial, Polynomial.derivative_monomial]
      calc
        (∫ x : ℝ, x * (a * x ^ n) ∂gaussianReal 0 variance) =
            a * ∫ x : ℝ, x ^ (n + 1) ∂gaussianReal 0 variance := by
          rw [← integral_const_mul]
          apply integral_congr_ae
          filter_upwards with x
          rw [pow_succ]
          ring
        _ = a * ((variance : ℝ) * n *
            ∫ x : ℝ, x ^ (n - 1) ∂gaussianReal 0 variance) := by
          rw [integral_pow_succ_centeredGaussian]
        _ = (variance : ℝ) *
            ∫ x : ℝ, a * n * x ^ (n - 1) ∂gaussianReal 0 variance := by
          rw [integral_const_mul]
          ring

/-- Generalized Hermite polynomials of positive order are centered under their matching
centered Gaussian law. -/
theorem integral_varianceHermite_centeredGaussian (variance : ℝ≥0) (n : ℕ) :
    (∫ x : ℝ, (varianceHermite (variance : ℝ) n).eval x
      ∂gaussianReal 0 variance) = if n = 0 then 1 else 0 := by
  cases n with
  | zero => simp [varianceHermite]
  | succ n =>
      simp only [Nat.succ_ne_zero, ite_false]
      rw [varianceHermite_succ]
      simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X,
        Polynomial.eval_C]
      have hx : Integrable (fun x : ℝ ↦ x *
          (varianceHermite (variance : ℝ) n).eval x)
          (gaussianReal 0 variance) := by
        refine (integrable_polynomial_centeredGaussian variance
          (Polynomial.X * varianceHermite (variance : ℝ) n)).congr <|
            Filter.Eventually.of_forall fun x ↦ ?_
        simp only [Polynomial.eval_mul, Polynomial.eval_X]
      have hc : Integrable (fun x : ℝ ↦
          ((variance : ℝ) * n) *
            (varianceHermite (variance : ℝ) (n - 1)).eval x)
          (gaussianReal 0 variance) :=
        (integrable_polynomial_centeredGaussian variance
          (varianceHermite (variance : ℝ) (n - 1))).const_mul _
      rw [integral_sub hx hc, integral_mul_polynomial_centeredGaussian,
        derivative_varianceHermite]
      simp only [Polynomial.eval_mul, Polynomial.eval_C]
      rw [integral_const_mul, integral_const_mul]
      ring

/-- Raising one Hermite order transfers one order to the other factor in Gaussian inner
products. -/
theorem integral_varianceHermite_succ_mul_centeredGaussian
    (variance : ℝ≥0) (m n : ℕ) :
    (∫ x : ℝ, (varianceHermite (variance : ℝ) (m + 1)).eval x *
        (varianceHermite (variance : ℝ) n).eval x ∂gaussianReal 0 variance) =
      (variance : ℝ) * n *
        ∫ x : ℝ, (varianceHermite (variance : ℝ) m).eval x *
          (varianceHermite (variance : ℝ) (n - 1)).eval x
          ∂gaussianReal 0 variance := by
  rw [varianceHermite_succ]
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X,
    Polynomial.eval_C, sub_mul]
  have hfirst : Integrable (fun x : ℝ ↦
      x * (varianceHermite (variance : ℝ) m).eval x *
        (varianceHermite (variance : ℝ) n).eval x)
      (gaussianReal 0 variance) := by
    refine (integrable_polynomial_centeredGaussian variance
      (Polynomial.X * varianceHermite (variance : ℝ) m *
        varianceHermite (variance : ℝ) n)).congr <|
          Filter.Eventually.of_forall fun x ↦ ?_
    simp only [Polynomial.eval_mul, Polynomial.eval_X]
  have hsecond : Integrable (fun x : ℝ ↦
      ((variance : ℝ) * m *
        (varianceHermite (variance : ℝ) (m - 1)).eval x) *
          (varianceHermite (variance : ℝ) n).eval x)
      (gaussianReal 0 variance) := by
    refine (integrable_polynomial_centeredGaussian variance
      (Polynomial.C ((variance : ℝ) * m) *
        varianceHermite (variance : ℝ) (m - 1) *
          varianceHermite (variance : ℝ) n)).congr <|
            Filter.Eventually.of_forall fun x ↦ ?_
    simp only [Polynomial.eval_mul, Polynomial.eval_C]
  rw [integral_sub hfirst hsecond]
  have hstein := integral_mul_polynomial_centeredGaussian variance
    (varianceHermite (variance : ℝ) m * varianceHermite (variance : ℝ) n)
  simp only [Polynomial.eval_mul] at hstein
  have hstein' :
      (∫ x : ℝ, x * (varianceHermite (variance : ℝ) m).eval x *
          (varianceHermite (variance : ℝ) n).eval x
          ∂gaussianReal 0 variance) =
        (variance : ℝ) *
          ∫ x : ℝ, ((varianceHermite (variance : ℝ) m *
            varianceHermite (variance : ℝ) n).derivative).eval x
            ∂gaussianReal 0 variance := by
    calc
      (∫ x : ℝ, x * (varianceHermite (variance : ℝ) m).eval x *
          (varianceHermite (variance : ℝ) n).eval x
          ∂gaussianReal 0 variance) =
          ∫ x : ℝ, x * ((varianceHermite (variance : ℝ) m).eval x *
            (varianceHermite (variance : ℝ) n).eval x)
            ∂gaussianReal 0 variance := by
        apply integral_congr_ae
        filter_upwards with x
        ring
      _ = _ := hstein
  rw [hstein']
  have hderiv :
      (∫ x : ℝ, ((varianceHermite (variance : ℝ) m *
          varianceHermite (variance : ℝ) n).derivative).eval x
          ∂gaussianReal 0 variance) =
        m * (∫ x : ℝ, (varianceHermite (variance : ℝ) (m - 1)).eval x *
          (varianceHermite (variance : ℝ) n).eval x
          ∂gaussianReal 0 variance) +
        n * (∫ x : ℝ, (varianceHermite (variance : ℝ) m).eval x *
          (varianceHermite (variance : ℝ) (n - 1)).eval x
          ∂gaussianReal 0 variance) := by
    rw [Polynomial.derivative_mul, derivative_varianceHermite,
      derivative_varianceHermite]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
    have hleft : Integrable (fun x : ℝ ↦
        (m * (varianceHermite (variance : ℝ) (m - 1)).eval x) *
          (varianceHermite (variance : ℝ) n).eval x)
        (gaussianReal 0 variance) := by
      refine (integrable_polynomial_centeredGaussian variance
        (Polynomial.C (m : ℝ) * varianceHermite (variance : ℝ) (m - 1) *
          varianceHermite (variance : ℝ) n)).congr <|
            Filter.Eventually.of_forall fun x ↦ ?_
      simp only [Polynomial.eval_mul, Polynomial.eval_C]
    have hright : Integrable (fun x : ℝ ↦
        (varianceHermite (variance : ℝ) m).eval x *
          (n * (varianceHermite (variance : ℝ) (n - 1)).eval x))
        (gaussianReal 0 variance) := by
      refine (integrable_polynomial_centeredGaussian variance
        (varianceHermite (variance : ℝ) m * Polynomial.C (n : ℝ) *
          varianceHermite (variance : ℝ) (n - 1))).congr <|
            Filter.Eventually.of_forall fun x ↦ ?_
      simp only [Polynomial.eval_mul, Polynomial.eval_C]
      ring
    rw [integral_add hleft hright]
    have hleftIntegral :
        (∫ x : ℝ, (m * (varianceHermite (variance : ℝ) (m - 1)).eval x) *
            (varianceHermite (variance : ℝ) n).eval x
            ∂gaussianReal 0 variance) =
          m * ∫ x : ℝ, (varianceHermite (variance : ℝ) (m - 1)).eval x *
            (varianceHermite (variance : ℝ) n).eval x
            ∂gaussianReal 0 variance := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      ring
    have hrightIntegral :
        (∫ x : ℝ, (varianceHermite (variance : ℝ) m).eval x *
            (n * (varianceHermite (variance : ℝ) (n - 1)).eval x)
            ∂gaussianReal 0 variance) =
          n * ∫ x : ℝ, (varianceHermite (variance : ℝ) m).eval x *
            (varianceHermite (variance : ℝ) (n - 1)).eval x
            ∂gaussianReal 0 variance := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      ring
    rw [hleftIntegral, hrightIntegral]
  rw [hderiv]
  have hsecondIntegral :
      (∫ x : ℝ, ((variance : ℝ) * m *
          (varianceHermite (variance : ℝ) (m - 1)).eval x) *
            (varianceHermite (variance : ℝ) n).eval x
          ∂gaussianReal 0 variance) =
        (variance : ℝ) * m *
          ∫ x : ℝ, (varianceHermite (variance : ℝ) (m - 1)).eval x *
            (varianceHermite (variance : ℝ) n).eval x
            ∂gaussianReal 0 variance := by
    calc
      (∫ x : ℝ, ((variance : ℝ) * m *
          (varianceHermite (variance : ℝ) (m - 1)).eval x) *
            (varianceHermite (variance : ℝ) n).eval x
          ∂gaussianReal 0 variance) =
          ∫ x : ℝ, ((variance : ℝ) * m) *
            ((varianceHermite (variance : ℝ) (m - 1)).eval x *
              (varianceHermite (variance : ℝ) n).eval x)
            ∂gaussianReal 0 variance := by
        apply integral_congr_ae
        filter_upwards with x
        ring
      _ = _ := by rw [integral_const_mul]
  rw [hsecondIntegral]
  ring

/-- Generalized Hermite polynomials are orthogonal under the centered Gaussian law with their
matching variance, with squared norm `n! variance^n`. -/
theorem integral_varianceHermite_mul_centeredGaussian
    (variance : ℝ≥0) (m n : ℕ) :
    (∫ x : ℝ, (varianceHermite (variance : ℝ) m).eval x *
        (varianceHermite (variance : ℝ) n).eval x ∂gaussianReal 0 variance) =
      if m = n then m.factorial * (variance : ℝ) ^ m else 0 := by
  induction m generalizing n with
  | zero =>
      simp only [varianceHermite, Polynomial.eval_one, one_mul, Nat.factorial_zero,
        Nat.cast_one, one_mul, pow_zero]
      rw [integral_varianceHermite_centeredGaussian]
      by_cases hn : n = 0
      · simp [hn]
      · have hn' : 0 ≠ n := Ne.symm hn
        simp [hn, hn']
  | succ m ih =>
      rw [integral_varianceHermite_succ_mul_centeredGaussian]
      cases n with
      | zero => simp
      | succ n =>
          simp only [Nat.add_sub_cancel]
          rw [ih n]
          by_cases hmn : m = n
          · subst n
            simp [Nat.factorial_succ, pow_succ]
            ring
          · simp [hmn]

/-- The centered square of a centered Gaussian has second moment twice the squared variance. -/
theorem integral_sq_sub_variance_sq_centeredGaussian (variance : ℝ≥0) :
    (∫ x : ℝ, (x ^ 2 - (variance : ℝ)) ^ 2 ∂gaussianReal 0 variance) =
      2 * (variance : ℝ) ^ 2 := by
  calc
    (∫ x : ℝ, (x ^ 2 - (variance : ℝ)) ^ 2 ∂gaussianReal 0 variance) =
        ∫ x : ℝ, (varianceHermite (variance : ℝ) 2).eval x *
          (varianceHermite (variance : ℝ) 2).eval x
          ∂gaussianReal 0 variance := by
      apply integral_congr_ae
      filter_upwards with x
      simp [varianceHermite]
      ring
    _ = 2 * (variance : ℝ) ^ 2 := by
      rw [integral_varianceHermite_mul_centeredGaussian]
      norm_num

end Malliavin.BrownianIteratedConstruction

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
