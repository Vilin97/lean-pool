/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.ExplicitFormula.RegularizedTartar
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Regularized Tartar Transform

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/

@[expose] public section

noncomputable section

open Complex Filter MeasureTheory Set
open scoped Topology

namespace NumberField.Odlyzko

theorem mul_abs_le_half_mul_sq_add_sq_div
    {δ : ℝ} (hδ : 0 < δ) (a x : ℝ) :
    a * |x| ≤ δ / 2 * x ^ 2 + a ^ 2 / (2 * δ) := by
  have hsquare : 0 ≤ (δ * |x| - a) ^ 2 := sq_nonneg _
  rw [show δ / 2 * x ^ 2 + a ^ 2 / (2 * δ) =
    a ^ 2 / (2 * δ) + δ / 2 * x ^ 2 by ring]
  rw [← sub_le_iff_le_add,
    le_div_iff₀ (mul_pos (by norm_num) hδ)]
  ring_nf at hsquare ⊢
  rw [sq_abs] at hsquare
  nlinarith

theorem exp_neg_mul_sq_add_mul_le
    {δ : ℝ} (hδ : 0 < δ) (a x : ℝ) :
    Real.exp (-δ * x ^ 2 + a * |x|) ≤
      Real.exp (a ^ 2 / (2 * δ)) *
        Real.exp (-(δ / 2) * x ^ 2) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hyoung := mul_abs_le_half_mul_sq_add_sq_div hδ a x
  linarith

theorem continuous_regularizedScaledTartar (y δ : ℝ) :
    Continuous (regularizedScaledTartar y δ) := by
  unfold regularizedScaledTartar scaledTartarTestFunction
  fun_prop

theorem continuous_poitouTransformIntegrand_regularizedScaledTartar
    (y δ : ℝ) (s : ℂ) :
    Continuous
      (poitouTransformIntegrand (regularizedScaledTartar y δ) s) := by
  change Continuous (fun x : ℝ ↦
    ((regularizedScaledTartar y δ x / Real.cosh (x / 2) : ℝ) : ℂ) *
      Complex.exp ((s - 1 / 2) * x))
  have hquot : Continuous (fun x : ℝ ↦
      regularizedScaledTartar y δ x / Real.cosh (x / 2)) := by
    apply Continuous.div (continuous_regularizedScaledTartar y δ)
      (by fun_prop)
    intro x
    exact (Real.cosh_pos _).ne'
  exact (Complex.continuous_ofReal.comp hquot).mul (by fun_prop)

theorem norm_poitouTransformIntegrand_regularizedScaledTartar_le
    {y δ : ℝ} (hδ : 0 < δ) (s : ℂ) (x : ℝ) :
    ‖poitouTransformIntegrand (regularizedScaledTartar y δ) s x‖ ≤
      Real.exp (|s.re - 1 / 2| ^ 2 / (2 * δ)) *
        Real.exp (-(δ / 2) * x ^ 2) := by
  rw [poitouTransformIntegrand, norm_mul, Complex.norm_real,
    poitouKernel, Real.norm_eq_abs, abs_div]
  have hcosh : 1 ≤ Real.cosh (x / 2) := Real.one_le_cosh _
  have hf :
      |regularizedScaledTartar y δ x| ≤
        Real.exp (-δ * x ^ 2) := by
    rw [abs_of_nonneg (regularizedScaledTartar_nonneg y δ x)]
    unfold regularizedScaledTartar
    calc
      scaledTartarTestFunction y x * Real.exp (-δ * x ^ 2) ≤
          1 * Real.exp (-δ * x ^ 2) := by
        gcongr
        exact tartarTestFunction_le_one _
      _ = _ := one_mul _
  have hquot :
      |regularizedScaledTartar y δ x| / |Real.cosh (x / 2)| ≤
        Real.exp (-δ * x ^ 2) := by
    rw [abs_of_pos (Real.cosh_pos _)]
    exact (div_le_iff₀ (Real.cosh_pos _)).2
      (hf.trans (by
        simpa only [one_mul, mul_one] using
          mul_le_mul_of_nonneg_left hcosh
            (Real.exp_pos (-δ * x ^ 2)).le))
  rw [Complex.norm_exp, mul_re, ofReal_re, ofReal_im, mul_zero,
    sub_zero, sub_re]
  norm_num
  calc
    |regularizedScaledTartar y δ x| / |Real.cosh (x / 2)| *
          Real.exp ((s.re - 1 / 2) * x) ≤
        Real.exp (-δ * x ^ 2) *
          Real.exp ((s.re - 1 / 2) * x) := by
      gcongr
    _ = Real.exp (-δ * x ^ 2 + (s.re - 1 / 2) * x) := by
      rw [← Real.exp_add]
    _ ≤ Real.exp (-δ * x ^ 2 + |s.re - 1 / 2| * |x|) := by
      have hlin := le_abs_self ((s.re - 1 / 2) * x)
      simp_all
    _ ≤ _ := by
      simpa only [sq_abs, neg_mul] using
        exp_neg_mul_sq_add_mul_le hδ |s.re - 1 / 2| x

theorem poitouTransformIntegrand_regularizedScaledTartar_integrable
    {y δ : ℝ} (hδ : 0 < δ) (s : ℂ) :
    Integrable
      (poitouTransformIntegrand (regularizedScaledTartar y δ) s) := by
  have hmajor :
      Integrable (fun x : ℝ ↦
        Real.exp (|s.re - 1 / 2| ^ 2 / (2 * δ)) *
          Real.exp (-(δ / 2) * x ^ 2)) :=
    (integrable_exp_neg_mul_sq (half_pos hδ)).const_mul _
  exact hmajor.mono'
    (continuous_poitouTransformIntegrand_regularizedScaledTartar y δ s
      |>.aestronglyMeasurable)
    (ae_of_all _ (norm_poitouTransformIntegrand_regularizedScaledTartar_le
      hδ s))

private theorem continuous_poitouTransformDerivativeIntegrand_regularizedScaledTartar
    (y δ : ℝ) (s : ℂ) :
    Continuous
      (poitouTransformDerivativeIntegrand
        (regularizedScaledTartar y δ) s) := by
  unfold poitouTransformDerivativeIntegrand
  exact Complex.continuous_ofReal.mul
    (continuous_poitouTransformIntegrand_regularizedScaledTartar y δ s)

theorem norm_poitouTransformDerivativeIntegrand_regularizedScaledTartar_le
    {y δ : ℝ} (hδ : 0 < δ) (s : ℂ) (x : ℝ) :
    ‖poitouTransformDerivativeIntegrand
        (regularizedScaledTartar y δ) s x‖ ≤
      Real.exp (|s.re - 1 / 2| ^ 2 / (2 * δ)) *
        (|x| * Real.exp (-(δ / 2) * x ^ 2)) := by
  rw [poitouTransformDerivativeIntegrand, norm_mul,
    Complex.norm_real, Real.norm_eq_abs]
  calc
    |x| *
        ‖poitouTransformIntegrand
          (regularizedScaledTartar y δ) s x‖ ≤
      |x| * (Real.exp (|s.re - 1 / 2| ^ 2 / (2 * δ)) *
        Real.exp (-(δ / 2) * x ^ 2)) := by
      gcongr
      exact norm_poitouTransformIntegrand_regularizedScaledTartar_le hδ s x
    _ = _ := by ring

theorem hasDerivAt_poitouTransform_regularizedScaledTartar
    {y δ : ℝ} (hδ : 0 < δ) (s : ℂ) :
    HasDerivAt
      (poitouTransform (regularizedScaledTartar y δ))
      (∫ x : ℝ, poitouTransformDerivativeIntegrand
        (regularizedScaledTartar y δ) s x) s := by
  let a : ℝ := |s.re - 1 / 2| + 1
  have hball :
      ∀ z ∈ Metric.ball s 1, |z.re - 1 / 2| ≤ a := by
    intro z hz
    have hzs : ‖z - s‖ < 1 := by
      simpa only [Metric.mem_ball, dist_eq_norm] using hz
    have hre : |z.re - s.re| ≤ ‖z - s‖ := by
      simpa only [sub_re] using Complex.abs_re_le_norm (z - s)
    grind
  have hmoment :
      Integrable (fun x : ℝ ↦
        |x| * Real.exp (-(δ / 2) * x ^ 2)) := by
    have h := (integrable_mul_exp_neg_mul_sq (half_pos hδ)).norm
    simp_all
  have hmajor :
      Integrable (fun x : ℝ ↦
        Real.exp (a ^ 2 / (2 * δ)) *
          (|x| * Real.exp (-(δ / 2) * x ^ 2))) :=
    hmoment.const_mul _
  have hresult :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume) (x₀ := s) (s := Metric.ball s 1)
      (F := fun z x ↦ poitouTransformIntegrand
        (regularizedScaledTartar y δ) z x)
      (F' := fun z x ↦ poitouTransformDerivativeIntegrand
        (regularizedScaledTartar y δ) z x)
      (bound := fun x ↦ Real.exp (a ^ 2 / (2 * δ)) *
        (|x| * Real.exp (-(δ / 2) * x ^ 2)))
      (Metric.ball_mem_nhds s zero_lt_one)
      (by
        filter_upwards [] with z
        exact
          (continuous_poitouTransformIntegrand_regularizedScaledTartar
            y δ z).aestronglyMeasurable)
      (poitouTransformIntegrand_regularizedScaledTartar_integrable hδ s)
      ((continuous_poitouTransformDerivativeIntegrand_regularizedScaledTartar
        y δ s).aestronglyMeasurable)
      (by
        filter_upwards [] with x z hz
        refine (norm_poitouTransformDerivativeIntegrand_regularizedScaledTartar_le
          hδ z x).trans ?_
        gcongr
        simp_all)
      hmajor
      (by
        filter_upwards [] with x z _
        exact hasDerivAt_poitouTransformIntegrand
          (regularizedScaledTartar y δ) z x)
  exact hresult.2

theorem analyticOnNhd_poitouTransform_regularizedScaledTartar
    {y δ : ℝ} (hδ : 0 < δ) :
    AnalyticOnNhd ℂ
      (poitouTransform (regularizedScaledTartar y δ)) univ := by
  apply DifferentiableOn.analyticOnNhd
  · intro s _
    exact (hasDerivAt_poitouTransform_regularizedScaledTartar hδ s)
      |>.differentiableAt.differentiableWithinAt
  · simp

end NumberField.Odlyzko
