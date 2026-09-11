/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.Foundations.VectorCalculus
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import LeanPool.NavierStokesAndEuler.Euler.MeanHarmonicLaplacian
import LeanPool.NavierStokesAndEuler.Euler.MeanSolenoidalSpace
import Mathlib.Algebra.Order.Star.Real

/-! Quantitative cutoff energy estimates used in the three-dimensional interior bound. -/

@[expose] public section


noncomputable section

namespace EulerMeanHarmonic

open MeasureTheory InnerProductSpace Laplacian EulerSmoothLimit EulerVectorCalculus
  EulerMeanSolenoidal
open scoped ContDiff

theorem integrable_weighted_square (η h : Space → ℝ) (hcη : HasCompactSupport η)
    (hη : Continuous η) (hh : Continuous h) : Integrable (fun x => η x ^ 2 * h x ^ 2) := by
  have hc : HasCompactSupport (fun x => η x ^ 2 * h x ^ 2) :=
    (hcη.comp_left (g := fun s : ℝ => s ^ 2) (by simp)).mul_right
      (f' := fun x => h x ^ 2)
  exact ((hη.pow 2).mul (hh.pow 2)).integrable_of_hasCompactSupport hc

theorem integrable_weighted_gradient_square (η h : Space → ℝ)
    (hcη : HasCompactSupport η) (hη : Continuous η) (hh : ContDiff ℝ ∞ h) :
    Integrable (fun x => η x ^ 2 * ‖gradient h x‖ ^ 2) := by
  have hc : HasCompactSupport (fun x => η x ^ 2 * ‖gradient h x‖ ^ 2) :=
    (hcη.comp_left (g := fun s : ℝ => s ^ 2) (by simp)).mul_right
      (f' := fun x => ‖gradient h x‖ ^ 2)
  exact ((hη.pow 2).mul ((contDiff_gradient hh).continuous.norm.pow
      2)).integrable_of_hasCompactSupport hc

theorem integrable_square_gradient_cutoff (η h : Space → ℝ)
    (hcη : HasCompactSupport η) (hη : ContDiff ℝ ∞ η) (hh : Continuous h) :
    Integrable (fun x => h x ^ 2 * ‖gradient η x‖ ^ 2) := by
  have hc : HasCompactSupport (fun x => h x ^ 2 * ‖gradient η x‖ ^ 2) :=
    ((compactSupport_gradient hcη).comp_left (g := fun v : Space => ‖v‖ ^ 2) (by simp)).mul_left
      (f := fun x => h x ^ 2)
  exact ((hh.pow 2).mul ((contDiff_gradient hη).continuous.norm.pow
      2)).integrable_of_hasCompactSupport hc

theorem gradient_eq_zero_off_support (η : Space → ℝ) {x : Space}
    (hx : x ∉ tsupport η) : gradient η x = 0 := by
  simp only [gradient, fderiv_of_notMem_tsupport ℝ hx, map_zero]

theorem cutoff_gradient_majorant (η ρ : Space → ℝ) (C : ℝ)
    (hC : ∀ x, ‖gradient η x‖ ≤ C) (hρ : ∀ x ∈ tsupport η, ρ x = 1) (x : Space) :
    ‖gradient η x‖ ^ 2 ≤ C ^ 2 * ρ x ^ 2 := by
  by_cases hx : x ∈ tsupport η
  · rw [hρ x hx, one_pow, mul_one]
    exact pow_le_pow_left₀ (norm_nonneg _) (hC x) 2
  · rw [gradient_eq_zero_off_support η hx, norm_zero, zero_pow (by norm_num)]
    positivity

theorem cutoff_square_majorant (η ρ : Space → ℝ)
    (hη : ∀ x, |η x| ≤ 1) (hρ : ∀ x ∈ tsupport η, ρ x = 1) (x : Space) :
    η x ^ 2 ≤ ρ x ^ 2 := by
  by_cases hx : x ∈ tsupport η
  · rw [hρ x hx]
    nlinarith [sq_abs (η x), hη x, abs_nonneg (η x)]
  · rw [image_eq_zero_of_notMem_tsupport hx, zero_pow (by norm_num)]
    positivity

theorem partialDerivative_sq_le_gradient_sq (h : Space → ℝ) (i : Fin 3) (x : Space) :
    partialDerivative h i x ^ 2 ≤ ‖gradient h x‖ ^ 2 := by
  rw [← gradient_coordinate]
  have hb := PiLp.norm_apply_le (gradient h x) i
  have hs := pow_le_pow_left₀ (norm_nonneg _) hb 2
  simpa only [Real.norm_eq_abs, sq_abs] using hs

/-- A cutoff derivative estimate transports Caccioppoli to a larger weight. -/
theorem caccioppoli_weighted_bound (η ρ h : Space → ℝ) (C : ℝ)
    (hcη : HasCompactSupport η) (hη : ContDiff ℝ ∞ η) (hh : ContDiff ℝ ∞ h)
    (hharmonic : ∀ x ∈ tsupport η, Δ h x = 0)
    (hi : Integrable (fun x => ρ x ^ 2 * h x ^ 2))
    (hbound : ∀ x, ‖gradient η x‖ ^ 2 ≤ C ^ 2 * ρ x ^ 2) :
    (∫ x, η x ^ 2 * ‖gradient h x‖ ^ 2) ≤
      4 * C ^ 2 * ∫ x, ρ x ^ 2 * h x ^ 2 := by
  have hmono : (∫ x, h x ^ 2 * ‖gradient η x‖ ^ 2) ≤
      C ^ 2 * ∫ x, ρ x ^ 2 * h x ^ 2 := by
    rw [← integral_const_mul]
    apply integral_mono (integrable_square_gradient_cutoff η h hcη hη hh.continuous)
      (hi.const_mul (C ^ 2))
    intro x
    nlinarith [mul_le_mul_of_nonneg_left (hbound x) (sq_nonneg (h x))]
  have hc := caccioppoli_bound η h hcη hη hh hharmonic
  nlinarith

end EulerMeanHarmonic
