/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Ring.Basic

/-! # Gaussian identity and Fubini helpers for the logarithmic energy

* `integral_gaussian_sub` : `∫ x, exp (-b (x - c)²) = √(π/b)`;
* `gaussian_conv` : the completing-the-square identity
  `∫ u : ℂ, exp (-2s‖z-u‖²) exp (-2s‖w-u‖²) = π/(4s) exp (-s‖z-w‖²)`;
* `intervalIntegral_swap_of_continuous` : Fubini for interval integrals of continuous functions.
-/

public section

open MeasureTheory Set Real

namespace Zeta5Irrational

lemma integral_gaussian_sub {b : ℝ} (c : ℝ) :
    ∫ x : ℝ, Real.exp (-b * (x - c) ^ 2) = Real.sqrt (π / b) := by
  rw [integral_sub_right_eq_self (fun x => Real.exp (-b * x ^ 2)) c]
  exact integral_gaussian b

lemma integrable_gaussian_sub {b : ℝ} (hb : 0 < b) (c : ℝ) :
    Integrable (fun x : ℝ => Real.exp (-b * (x - c) ^ 2)) := by
  have := (integrable_exp_neg_mul_sq hb).comp_sub_right c
  simpa using this

/-- Completing the square in one variable. -/
lemma sq_add_sq_eq (a b x : ℝ) :
    (a - x) ^ 2 + (b - x) ^ 2 = 2 * (x - (a + b) / 2) ^ 2 + (a - b) ^ 2 / 2 := by ring

lemma gaussian_conv_one (s a b : ℝ) :
    ∫ x : ℝ, Real.exp (-(2 * s) * (a - x) ^ 2) * Real.exp (-(2 * s) * (b - x) ^ 2) =
      Real.sqrt (π / (4 * s)) * Real.exp (-s * (a - b) ^ 2) := by
  have :
    ∀ x : ℝ,
      Real.exp (-(2 * s) * (a - x) ^ 2) * Real.exp (-(2 * s) * (b - x) ^ 2) =
        Real.exp (-(4 * s) * (x - (a + b) / 2) ^ 2) * Real.exp (-s * (a - b) ^ 2) := by
    intro x
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  simp_rw [this]
  rw [integral_mul_const, integral_gaussian_sub]

/-- The norm squared on `ℂ` in terms of real and imaginary parts. -/
lemma normSq_eq (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]; ring

/-- The completing-the-square identity on `ℂ`. -/
lemma gaussian_conv {s : ℝ} (hs : 0 < s) (z w : ℂ) :
    ∫ u : ℂ, Real.exp (-(2 * s) * ‖z - u‖ ^ 2) * Real.exp (-(2 * s) * ‖w - u‖ ^ 2) =
      π / (4 * s) * Real.exp (-s * ‖z - w‖ ^ 2) := by
  have h := Complex.volume_preserving_equiv_real_prod
  have key :
    ∀ u : ℂ,
      Real.exp (-(2 * s) * ‖z - u‖ ^ 2) * Real.exp (-(2 * s) * ‖w - u‖ ^ 2) =
        (Real.exp (-(2 * s) * (z.re - u.re) ^ 2) * Real.exp (-(2 * s) * (w.re - u.re) ^ 2)) *
          (Real.exp (-(2 * s) * (z.im - u.im) ^ 2) * Real.exp (-(2 * s) * (w.im - u.im) ^ 2)) := by
    intro u
    rw [normSq_eq, normSq_eq]
    simp only [Complex.sub_re, Complex.sub_im]
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1; ring
  simp_rw [key]
  have e :=
    h.integral_comp'
      (fun p : ℝ × ℝ =>
        (Real.exp (-(2 * s) * (z.re - p.1) ^ 2) * Real.exp (-(2 * s) * (w.re - p.1) ^ 2)) *
          (Real.exp (-(2 * s) * (z.im - p.2) ^ 2) * Real.exp (-(2 * s) * (w.im - p.2) ^ 2)))
  simp only [Complex.measurableEquivRealProd_apply] at e
  rw [e, Measure.volume_eq_prod]
  rw [integral_prod_mul
      (fun x : ℝ => Real.exp (-(2 * s) * (z.re - x) ^ 2) * Real.exp (-(2 * s) * (w.re - x) ^ 2))
      (fun y : ℝ => Real.exp (-(2 * s) * (z.im - y) ^ 2) * Real.exp (-(2 * s) * (w.im - y) ^ 2)),
    gaussian_conv_one s _ _, gaussian_conv_one s _ _, normSq_eq]
  simp only [Complex.sub_re, Complex.sub_im]
  rw [mul_mul_mul_comm, ← Real.sqrt_mul (by positivity), ← Real.exp_add, ← sq,
    Real.sqrt_sq (by positivity)]
  congr 2
  ring

/-- Fubini for interval integrals of a continuous function of two variables. -/
lemma intervalIntegral_swap_of_continuous {f : ℝ → ℝ → ℝ} (hf : Continuous (Function.uncurry f))
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) :
    ∫ x in a..b, ∫ y in c..d, f x y = ∫ y in c..d, ∫ x in a..b, f x y := by
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hcd]
  simp_rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hcd]
  apply integral_integral_swap
  rw [Measure.prod_restrict]
  refine IntegrableOn.mono_set ?_ (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  exact ContinuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc) hf.continuousOn

end Zeta5Irrational
