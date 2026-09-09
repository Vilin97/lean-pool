/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.ProblemStatement
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-!
# Gaussian moments for Fourier differentiation

The zeroth, first and second norm moments of a Gaussian are integrable.
The only polynomial estimate used here absorbs the square of the norm into
a Gaussian with half the decay rate.
-/

@[expose] public section



noncomputable section

open MeasureTheory

namespace NavierStokesR3.Comparison

open ProblemStatement

/-- A real Gaussian, regarded as a complex-valued function, is integrable. -/
theorem integrable_complex_gaussian {a : ℝ} (ha : 0 < a) :
    Integrable (fun x : Space => (Real.exp (-a * ‖x‖ ^ 2) : ℂ)) := by
  simpa only [zero_mul, add_zero, Complex.ofReal_exp, Complex.ofReal_neg,
    Complex.ofReal_mul, Complex.ofReal_pow] using
    GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
      (b := (a : ℂ)) (by simpa only [Complex.ofReal_re] using ha) 0 (0 : Space)

/-- The ordinary real Gaussian is integrable on three-dimensional space. -/
theorem integrable_gaussian {a : ℝ} (ha : 0 < a) :
    Integrable (fun x : Space => Real.exp (-a * ‖x‖ ^ 2)) := by
  refine (integrable_complex_gaussian ha).norm.congr ?_
  filter_upwards with x
  exact Complex.norm_of_nonneg (Real.exp_nonneg _)

private theorem sq_mul_gaussian_le (a r : ℝ) (ha : 0 < a) :
    r ^ 2 * Real.exp (-a * r ^ 2) ≤
      (2 / a) * Real.exp (-(a / 2) * r ^ 2) := by
  have hlinear : (a / 2) * r ^ 2 ≤ Real.exp ((a / 2) * r ^ 2) := by
    linarith [Real.add_one_le_exp ((a / 2) * r ^ 2)]
  have hmul := mul_le_mul_of_nonneg_right hlinear (Real.exp_nonneg (-a * r ^ 2))
  have he : Real.exp ((a / 2) * r ^ 2) * Real.exp (-a * r ^ 2) =
      Real.exp (-(a / 2) * r ^ 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he] at hmul
  calc
    r ^ 2 * Real.exp (-a * r ^ 2) =
        (2 / a) * (((a / 2) * r ^ 2) * Real.exp (-a * r ^ 2)) := by
      field_simp [ha.ne']
    _ ≤ (2 / a) * Real.exp (-(a / 2) * r ^ 2) :=
      mul_le_mul_of_nonneg_left hmul (by positivity)

/-- The second norm moment of a Gaussian is integrable. -/
theorem integrable_norm_sq_gaussian {a : ℝ} (ha : 0 < a) :
    Integrable (fun x : Space => ‖x‖ ^ 2 * Real.exp (-a * ‖x‖ ^ 2)) := by
  have hc : Continuous (fun x : Space => ‖x‖ ^ 2 * Real.exp (-a * ‖x‖ ^ 2)) := by
    fun_prop
  refine ((integrable_gaussian (a := a / 2) (by positivity)).const_mul (2 / a)).mono'
    hc.aestronglyMeasurable ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact sq_mul_gaussian_le a ‖x‖ ha

/-- The first norm moment follows from the zeroth and second moments. -/
theorem integrable_norm_gaussian {a : ℝ} (ha : 0 < a) :
    Integrable (fun x : Space => ‖x‖ * Real.exp (-a * ‖x‖ ^ 2)) := by
  have hc : Continuous (fun x : Space => ‖x‖ * Real.exp (-a * ‖x‖ ^ 2)) := by
    fun_prop
  refine ((integrable_gaussian ha).add (integrable_norm_sq_gaussian ha)).mono'
    hc.aestronglyMeasurable ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc
    ‖x‖ * Real.exp (-a * ‖x‖ ^ 2) ≤
        (1 + ‖x‖ ^ 2) * Real.exp (-a * ‖x‖ ^ 2) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
      nlinarith [sq_nonneg (‖x‖ - 1 / 2)]
    _ = Real.exp (-a * ‖x‖ ^ 2) + ‖x‖ ^ 2 * Real.exp (-a * ‖x‖ ^ 2) := by ring

end NavierStokesR3.Comparison
