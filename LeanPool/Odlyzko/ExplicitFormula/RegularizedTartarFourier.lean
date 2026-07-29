/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.ExplicitFormula.RegularizedTartarLimit
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-!
# Regularized Tartar Fourier

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/

@[expose] public section

noncomputable section

open Complex MeasureTheory Real
open scoped Convolution FourierTransform RealInnerProductSpace

namespace NumberField.Odlyzko

private theorem tartarWeightConvolution_integrable :
    Integrable tartarWeightConvolution := by
  have h := complexTartarWeight_convolution_integrable
  apply h.norm.congr
  filter_upwards [] with x
  rw [complexTartarWeight_convolution_eq, norm_real, Real.norm_eq_abs,
    abs_of_nonneg (tartarWeightConvolution_nonneg x)]

theorem scaledTartarTestFunction_eq_integral_weightConvolution_cos
    (y x : ℝ) :
    scaledTartarTestFunction y x =
      (9 / 16 : ℝ) *
        ∫ v : ℝ, tartarWeightConvolution v * Real.cos (v * y * x) := by
  let Wℂ : ℝ → ℂ :=
    complexTartarWeight ⋆[ContinuousLinearMap.mul ℂ ℂ] complexTartarWeight
  let ξ : ℝ := y * x / (2 * Real.pi)
  have hint :
      Integrable (fun v : ℝ ↦
        Complex.exp (↑(-2 * Real.pi * v * ξ) * I) • Wℂ v) := by
    constructor
    · exact (by fun_prop : Continuous (fun v : ℝ ↦
        Complex.exp (↑(-2 * Real.pi * v * ξ) * I))).aestronglyMeasurable.smul
          complexTartarWeight_convolution_integrable.aestronglyMeasurable
    · apply complexTartarWeight_convolution_integrable.2.congr'
      filter_upwards [] with v
      rw [norm_smul, Complex.norm_exp]
      simp [Wℂ, Complex.mul_re]
  dsimp [Wℂ] at hint
  have hfour := fourier_complexTartarWeight_convolution ξ
  rw [Real.fourier_real_eq_integral_exp_smul] at hfour
  simp only [smul_eq_mul] at hfour
  have hre := congrArg Complex.re hfour
  rw [← RCLike.re_eq_complex_re, ← integral_re hint] at hre
  simp_rw [complexTartarWeight_convolution_eq] at hre
  simp only [RCLike.re_eq_complex_re, Complex.exp_mul_I,
    Complex.mul_re, Complex.add_re, Complex.cos_ofReal_re,
    Complex.sin_ofReal_re, Complex.sin_ofReal_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, mul_one, sub_zero] at hre
  dsimp [ξ] at hre
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  unfold scaledTartarTestFunction
  rw [show (16 / 9 : ℝ) * Tartar.testFunction (2 * Real.pi *
      (y * x / (2 * Real.pi))) =
      (16 / 9 : ℝ) * Tartar.testFunction (y * x) by
        grind] at hre
  have hcos :
      (fun v : ℝ ↦
        Real.cos (-2 * Real.pi * v * (y * x / (2 * Real.pi))) *
          tartarWeightConvolution v) =
      (fun v : ℝ ↦
        tartarWeightConvolution v * Real.cos (v * y * x)) := by
    funext v
    rw [show -2 * Real.pi * v * (y * x / (2 * Real.pi)) =
        -(v * y * x) by grind, Real.cos_neg]
    ring
  simp only [add_zero] at hre
  grind

theorem integral_exp_neg_mul_sq_mul_cos_nonneg
    {δ : ℝ} (hδ : 0 < δ) (a : ℝ) :
    0 ≤ ∫ x : ℝ, Real.exp (-δ * x ^ 2) * Real.cos (a * x) := by
  have hint :
      Integrable (fun x : ℝ ↦
        Complex.exp (I * (a : ℂ) * x) *
          Complex.exp (-(δ : ℂ) * x ^ 2)) :=
    integrable_cexp_quadratic (b := (δ : ℂ)) (by simp_all) (I * a) 0 |>.congr (by
      filter_upwards [] with x
      rw [add_zero, Complex.exp_add, mul_comm])
  have hgauss :=
    fourierIntegral_gaussian (b := (δ : ℂ)) (by simp_all) (a : ℂ)
  have hIa (x : ℝ) :
      I * (a : ℂ) * x = ((a * x : ℝ) : ℂ) * I := by
    push_cast
    ring
  have hrealExp (x : ℝ) :
      Complex.exp (-(δ : ℂ) * x ^ 2) =
        (Real.exp (-δ * x ^ 2) : ℂ) := by simp
  have hq : 0 ≤ Real.pi / δ := (div_pos Real.pi_pos hδ).le
  have hpow :
      ((Real.pi / δ : ℝ) : ℂ) ^ (1 / 2 : ℂ) =
        (((Real.pi / δ : ℝ) ^ (1 / 2 : ℝ) : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_ofNat] using
        (Complex.ofReal_cpow hq (1 / 2)).symm
  have hexp :
      Complex.exp (-(a : ℂ) ^ 2 / (4 * (δ : ℂ))) =
        (Real.exp (-(a ^ 2) / (4 * δ)) : ℂ) := by
    simp
  have hquot :
      (Real.pi : ℂ) / (δ : ℂ) =
        ((Real.pi / δ : ℝ) : ℂ) := by simp
  rw [hquot, hpow, hexp] at hgauss
  have hre := congrArg Complex.re hgauss
  rw [← RCLike.re_eq_complex_re, ← integral_re hint] at hre
  simp_rw [hIa, hrealExp] at hre
  simp only [RCLike.re_eq_complex_re, Complex.exp_mul_I,
    Complex.mul_re, Complex.add_re, Complex.cos_ofReal_re,
    Complex.sin_ofReal_re, Complex.sin_ofReal_im, Complex.I_re,
    Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    mul_one, add_zero, sub_zero] at hre
  rw [show (fun x : ℝ ↦
      Real.cos (a * x) * Real.exp (-δ * x ^ 2)) =
      (fun x : ℝ ↦
        Real.exp (-δ * x ^ 2) * Real.cos (a * x)) by
          funext x
          ring] at hre
  rw [hre]
  positivity

theorem cosineTransform_regularizedScaledTartar_nonneg
    {δ : ℝ} (hδ : 0 < δ) (y t : ℝ) :
    0 ≤ Poitou.cosineTransform (regularizedScaledTartar y δ) t := by
  let F : ℝ → ℝ → ℝ := fun x v ↦
    tartarWeightConvolution v * Real.exp (-δ * x ^ 2) *
      Real.cos (v * y * x) * Real.cos (t * x)
  have hgauss : Integrable (fun x : ℝ ↦ Real.exp (-δ * x ^ 2)) :=
    integrable_exp_neg_mul_sq hδ
  have hmajor :
      Integrable (fun z : ℝ × ℝ ↦
        Real.exp (-δ * z.1 ^ 2) * tartarWeightConvolution z.2) :=
    hgauss.mul_prod tartarWeightConvolution_integrable
  have hWcont : Continuous tartarWeightConvolution := by
    have hc :=
      Complex.continuous_re.comp
        complexTartarWeight_convolution_continuous
    convert hc using 1
    funext x
    change tartarWeightConvolution x =
      ((complexTartarWeight ⋆[ContinuousLinearMap.mul ℂ ℂ]
        complexTartarWeight) x).re
    rw [complexTartarWeight_convolution_eq]
    simp
  have hdouble : Integrable (Function.uncurry F) := by
    apply hmajor.mono'
    · exact (by fun_prop : Continuous (Function.uncurry F))
        |>.aestronglyMeasurable
    · filter_upwards [] with z
      change |F z.1 z.2| ≤
        Real.exp (-δ * z.1 ^ 2) * tartarWeightConvolution z.2
      dsimp [F]
      rw [abs_mul, abs_mul, abs_mul,
        abs_of_nonneg (tartarWeightConvolution_nonneg z.2),
        abs_of_pos (Real.exp_pos _)]
      calc
        tartarWeightConvolution z.2 * Real.exp (-δ * z.1 ^ 2) *
              |Real.cos (z.2 * y * z.1)| * |Real.cos (t * z.1)| ≤
            tartarWeightConvolution z.2 * Real.exp (-δ * z.1 ^ 2) *
              1 * 1 := by
          have hA :
              0 ≤ tartarWeightConvolution z.2 *
                Real.exp (-δ * z.1 ^ 2) :=
            mul_nonneg (tartarWeightConvolution_nonneg z.2)
              (Real.exp_pos _).le
          simpa only [mul_assoc] using
            mul_le_mul_of_nonneg_left
              (mul_le_mul
                (Real.abs_cos_le_one (z.2 * y * z.1))
                (Real.abs_cos_le_one (t * z.1))
                (abs_nonneg (Real.cos (t * z.1))) zero_le_one) hA
        _ = Real.exp (-δ * z.1 ^ 2) *
              tartarWeightConvolution z.2 := by ring
  have hinner (v : ℝ) :
      0 ≤ ∫ x : ℝ, F x v := by
    have hminus :=
      integral_exp_neg_mul_sq_mul_cos_nonneg hδ (v * y - t)
    have hplus :=
      integral_exp_neg_mul_sq_mul_cos_nonneg hδ (v * y + t)
    have hidentity :
        (fun x : ℝ ↦ F x v) =
          (fun x : ℝ ↦ tartarWeightConvolution v *
            ((Real.exp (-δ * x ^ 2) * Real.cos ((v * y - t) * x) +
              Real.exp (-δ * x ^ 2) * Real.cos ((v * y + t) * x)) / 2)) := by
      funext x
      dsimp [F]
      rw [show (v * y - t) * x = v * y * x - t * x by ring,
        show (v * y + t) * x = v * y * x + t * x by ring]
      rw [Real.cos_sub, Real.cos_add]
      ring
    have hminusInt :
        Integrable (fun x : ℝ ↦
          Real.exp (-δ * x ^ 2) * Real.cos ((v * y - t) * x)) :=
      (integrable_exp_neg_mul_sq hδ).mul_bdd
        (by fun_prop)
        (Filter.Eventually.of_forall fun x ↦ by
          simpa [Real.norm_eq_abs] using
            Real.abs_cos_le_one ((v * y - t) * x))
    have hplusInt :
        Integrable (fun x : ℝ ↦
          Real.exp (-δ * x ^ 2) * Real.cos ((v * y + t) * x)) :=
      (integrable_exp_neg_mul_sq hδ).mul_bdd
        (by fun_prop)
        (Filter.Eventually.of_forall fun x ↦ by
          simpa [Real.norm_eq_abs] using
            Real.abs_cos_le_one ((v * y + t) * x))
    rw [hidentity, integral_const_mul, integral_div,
      integral_add hminusInt hplusInt]
    exact mul_nonneg (tartarWeightConvolution_nonneg v)
      (div_nonneg (add_nonneg hminus hplus) (by norm_num))
  have hswap := integral_integral_swap hdouble
  calc
    Poitou.cosineTransform (regularizedScaledTartar y δ) t =
        (9 / 16 : ℝ) * ∫ x : ℝ, ∫ v : ℝ, F x v := by
      unfold Poitou.cosineTransform regularizedScaledTartar
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with x
      rw [scaledTartarTestFunction_eq_integral_weightConvolution_cos]
      rw [show (∫ v : ℝ, F x v) =
          (∫ v : ℝ, tartarWeightConvolution v *
            Real.cos (v * y * x)) *
              (Real.exp (-δ * x ^ 2) * Real.cos (t * x)) by
            rw [← integral_mul_const]
            apply integral_congr_ae
            filter_upwards [] with v
            dsimp [F]
            ring]
      ring
    _ = (9 / 16 : ℝ) * ∫ v : ℝ, ∫ x : ℝ, F x v := by simp_all
    _ ≥ 0 := mul_nonneg (by norm_num) (integral_nonneg hinner)

theorem regularizedScaledTartar_poitouAdmissible
    {y δ : ℝ} (hy : y ≠ 0) (hδ : 0 < δ) :
    Poitou.Admissible (regularizedScaledTartar y δ) where
  continuous := continuous_regularizedScaledTartar y δ
  even := regularizedScaledTartar_even y δ
  value_zero := regularizedScaledTartar_zero y δ
  nonnegative := regularizedScaledTartar_nonneg y δ
  integrable := regularizedScaledTartar_integrable hy hδ.le
  cosineTransform_nonnegative :=
    cosineTransform_regularizedScaledTartar_nonneg hδ y

end NumberField.Odlyzko
