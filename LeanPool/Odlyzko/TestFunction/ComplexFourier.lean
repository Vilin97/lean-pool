/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.TestFunction.Bounds
public import LeanPool.Odlyzko.TestFunction.Continuity
public import LeanPool.Odlyzko.ExplicitFormula.Admissible
public import Mathlib.Analysis.Fourier.Convolution
public import Mathlib.Analysis.Fourier.Inversion

/-! TODO: Add doc-string. -/

@[expose] public section

open MeasureTheory
open scoped ComplexConjugate Convolution FourierTransform RealInnerProductSpace

namespace NumberField.Odlyzko

/-- A complex tartar weight used in the Odlyzko-bound argument. -/
noncomputable def complexTartarWeight (x : ℝ) : ℂ :=
  Tartar.weight x

theorem complexTartarWeight_integrable : Integrable complexTartarWeight := by
  exact tartarWeight_integrable.ofReal

theorem integral_tartarWeight_mul_sin (a : ℝ) :
    ∫ x : ℝ, Tartar.weight x * Real.sin (a * x) = 0 := by
  let f : ℝ → ℝ := fun x ↦ Tartar.weight x * Real.sin (a * x)
  have hodd (x : ℝ) : f (-x) = -f x := by
    simp [f, tartarWeight_neg]
  have h :
      (∫ x : ℝ, f x) = -(∫ x : ℝ, f x) := by
    calc
      (∫ x : ℝ, f x) = ∫ x : ℝ, f (-x) :=
        (integral_neg_eq_self f (volume : Measure ℝ)).symm
      _ = ∫ x : ℝ, -f x := by simp_all
      _ = -(∫ x : ℝ, f x) := integral_neg f
  grind

theorem fourier_complexTartarWeight (ξ : ℝ) :
    𝓕 complexTartarWeight ξ =
      ((4 / 3 : ℝ) * Tartar.amplitude (2 * Real.pi * ξ) : ℂ) := by
  rw [tartarAmplitude_eq_cosineTransform]
  rw [Real.fourier_real_eq_integral_exp_smul]
  have hint :
      Integrable (fun v : ℝ ↦
        Complex.exp (↑(-2 * Real.pi * v * ξ) * Complex.I) • complexTartarWeight v) := by
    constructor
    · exact (by fun_prop : Continuous (fun v : ℝ ↦
        Complex.exp (↑(-2 * Real.pi * v * ξ) * Complex.I))).aestronglyMeasurable.smul
          complexTartarWeight_integrable.aestronglyMeasurable
    · apply complexTartarWeight_integrable.2.congr'
      filter_upwards [] with v
      rw [norm_smul, Complex.norm_exp]
      simp [Complex.mul_re]
  apply Complex.ext
  · rw [← RCLike.re_eq_complex_re, ← integral_re]
    · simp only [RCLike.re_eq_complex_re, smul_eq_mul, Complex.exp_mul_I,
        complexTartarWeight, Complex.mul_re,
        Complex.add_re, Complex.cos_ofReal_re,
        Complex.sin_ofReal_re, Complex.sin_ofReal_im, Complex.I_re,
        Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, mul_one, sub_zero,
        ]
      ring_nf
      apply integral_congr_ae
      filter_upwards [] with x
      rw [mul_comm]
      ring_nf
      simp
    · simp_all
  · rw [← RCLike.im_eq_complex_im, ← integral_im]
    · simp only [RCLike.im_eq_complex_im, smul_eq_mul, Complex.exp_mul_I,
        complexTartarWeight, Complex.mul_im,
        Complex.add_im, Complex.cos_ofReal_im,
        Complex.sin_ofReal_re, Complex.sin_ofReal_im, Complex.I_re,
        Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, mul_one, add_zero,
        ]
      simp only [zero_add, zero_mul]
      calc
        (∫ x : ℝ, Real.sin (-2 * Real.pi * x * ξ) * Tartar.weight x)
            = -(∫ x : ℝ, Tartar.weight x * Real.sin ((2 * Real.pi * ξ) * x)) := by
              rw [← integral_neg]
              apply integral_congr_ae
              filter_upwards [] with x
              rw [show -2 * Real.pi * x * ξ = -(2 * Real.pi * ξ * x) by ring,
                Real.sin_neg]
              ring
        _ = 0 := by rw [integral_tartarWeight_mul_sin, neg_zero]
    · simp_all

/-- A tartar weight convolution used in the Odlyzko-bound argument. -/
noncomputable def tartarWeightConvolution (x : ℝ) : ℝ :=
  ∫ t : ℝ, Tartar.weight t * Tartar.weight (x - t)

theorem tartarWeightConvolution_nonneg (x : ℝ) :
    0 ≤ tartarWeightConvolution x := by
  apply integral_nonneg
  intro t
  exact mul_nonneg (tartarWeight_nonneg t) (tartarWeight_nonneg (x - t))

theorem complexTartarWeight_convolution_eq (x : ℝ) :
    (complexTartarWeight ⋆[ContinuousLinearMap.mul ℂ ℂ] complexTartarWeight) x =
      tartarWeightConvolution x := by
  rw [MeasureTheory.convolution, tartarWeightConvolution, ← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards [] with t
  simp [complexTartarWeight]

theorem complexTartarWeight_convolution_integrable :
    Integrable (complexTartarWeight ⋆[ContinuousLinearMap.mul ℂ ℂ] complexTartarWeight) :=
  complexTartarWeight_integrable.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ)
    complexTartarWeight_integrable

theorem complexTartarWeight_convolution_continuous :
    Continuous (complexTartarWeight ⋆[ContinuousLinearMap.mul ℂ ℂ] complexTartarWeight) := by
  have hc : HasCompactSupport complexTartarWeight := by
    change HasCompactSupport (Complex.ofRealCLM ∘ Tartar.weight)
    exact tartarWeight_hasCompactSupport.comp_left rfl
  apply hc.continuous_convolution_right
    (ContinuousLinearMap.mul ℂ ℂ)
    complexTartarWeight_integrable.locallyIntegrable
  exact RCLike.continuous_ofReal.comp tartarWeight_continuous

theorem fourier_complexTartarWeight_convolution (ξ : ℝ) :
    𝓕 (complexTartarWeight ⋆[ContinuousLinearMap.mul ℂ ℂ] complexTartarWeight) ξ =
      ((16 / 9 : ℝ) * Tartar.testFunction (2 * Real.pi * ξ) : ℂ) := by
  -- v4.32's `fourier_mul_convolution_eq` also asks for continuity of both
  -- factors; v4.33 dropped those hypotheses.
  rw [Real.fourier_mul_convolution_eq complexTartarWeight_integrable
    complexTartarWeight_integrable
    (RCLike.continuous_ofReal.comp tartarWeight_continuous)
    (RCLike.continuous_ofReal.comp tartarWeight_continuous),
    fourier_complexTartarWeight]
  simp only [Tartar.testFunction, Complex.ofReal_pow]
  push_cast
  ring

theorem fourier_complexTartarWeight_convolution_integrable :
    Integrable (𝓕
      (complexTartarWeight ⋆[ContinuousLinearMap.mul ℂ ℂ] complexTartarWeight)) := by
  have hscale :
      Integrable (fun ξ : ℝ ↦ Tartar.testFunction (2 * Real.pi * ξ)) :=
    tartarTestFunction_integrable.comp_mul_left'
      (mul_ne_zero (by norm_num) Real.pi_ne_zero)
  have hcomplex := hscale.ofReal.const_mul ((16 / 9 : ℝ) : ℂ)
  apply hcomplex.congr
  filter_upwards [] with ξ
  rw [fourier_complexTartarWeight_convolution]
  simp

theorem fourierInv_fourier_complexTartarWeight_convolution :
    𝓕⁻ (𝓕 (complexTartarWeight ⋆[ContinuousLinearMap.mul ℂ ℂ] complexTartarWeight)) =
      (complexTartarWeight ⋆[ContinuousLinearMap.mul ℂ ℂ] complexTartarWeight) :=
  complexTartarWeight_convolution_continuous.fourierInv_fourier_eq
    complexTartarWeight_convolution_integrable
    fourier_complexTartarWeight_convolution_integrable

theorem cosineTransform_tartarTestFunction (t : ℝ) :
    Poitou.cosineTransform Tartar.testFunction t =
      9 * Real.pi / 8 * tartarWeightConvolution t := by
  have hinv := congrFun fourierInv_fourier_complexTartarWeight_convolution t
  rw [Real.fourierInv_eq_fourier_neg, Real.fourier_real_eq_integral_exp_smul,
    complexTartarWeight_convolution_eq] at hinv
  simp_rw [fourier_complexTartarWeight_convolution] at hinv
  have hre := congrArg Complex.re hinv
  have hscaledReal :
      Integrable (fun v : ℝ ↦ Tartar.testFunction (2 * Real.pi * v)) :=
    tartarTestFunction_integrable.comp_mul_left'
      (mul_ne_zero (by norm_num) Real.pi_ne_zero)
  have hscaledComplex :
      Integrable (fun v : ℝ ↦
        (((16 / 9 : ℝ) : ℂ) *
          (Tartar.testFunction (2 * Real.pi * v) : ℂ))) :=
    hscaledReal.ofReal.const_mul ((16 / 9 : ℝ) : ℂ)
  have hint :
      Integrable (fun v : ℝ ↦
        Complex.exp (↑(-2 * Real.pi * v * -t) * Complex.I) •
          (((16 / 9 : ℝ) : ℂ) *
            (Tartar.testFunction (2 * Real.pi * v) : ℂ))) := by
    constructor
    · exact (by fun_prop : Continuous (fun v : ℝ ↦
        Complex.exp (↑(-2 * Real.pi * v * -t) * Complex.I))).aestronglyMeasurable.smul
          hscaledComplex.aestronglyMeasurable
    · apply hscaledComplex.2.congr'
      filter_upwards [] with v
      rw [norm_smul, Complex.norm_exp]
      simp [Complex.mul_re]
  rw [← RCLike.re_eq_complex_re, ← integral_re hint] at hre
  simp only [RCLike.re_eq_complex_re, smul_eq_mul, Complex.exp_mul_I,
    Complex.mul_re, Complex.add_re, Complex.cos_ofReal_re,
    Complex.sin_ofReal_re, Complex.sin_ofReal_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, mul_one, sub_zero] at hre
  ring_nf at hre
  have hchange := Measure.integral_comp_mul_left
    (g := fun x : ℝ ↦ Tartar.testFunction x * Real.cos (t * x))
    (2 * Real.pi)
  have habs : |(2 * Real.pi)⁻¹| = (2 * Real.pi)⁻¹ := by
    rw [abs_of_pos]
    positivity
  rw [habs] at hchange
  have hleft :
      (∫ v : ℝ, Tartar.testFunction (2 * Real.pi * v) *
          Real.cos (2 * Real.pi * v * t)) =
        (2 * Real.pi)⁻¹ * Poitou.cosineTransform Tartar.testFunction t := by
    rw [Poitou.cosineTransform]
    convert hchange using 1
    · apply integral_congr_ae
      filter_upwards [] with v
      grind
    · simp
  have hre' :
      (16 / 9 : ℝ) *
          (∫ v : ℝ, Tartar.testFunction (2 * Real.pi * v) *
            Real.cos (2 * Real.pi * v * t)) =
        tartarWeightConvolution t := by
    rw [← integral_const_mul]
    convert hre using 1
    apply integral_congr_ae
    filter_upwards [] with v
    simp only [Complex.mul_im, Complex.add_im, Complex.cos_ofReal_im,
      Complex.sin_ofReal_re, Complex.sin_ofReal_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, mul_one, add_zero]
    ring_nf
  rw [hleft] at hre'
  have hp : 0 < Real.pi := Real.pi_pos
  grind

theorem integral_tartarWeight_sq :
    ∫ x : ℝ, Tartar.weight x ^ 2 = 16 / 15 := by
  rw [tartarWeight_eq_indicator]
  have hind :
      (fun x : ℝ ↦ ((Set.Icc (-1 : ℝ) 1).indicator (fun u ↦ 1 - u ^ 2) x) ^ 2) =
      (Set.Icc (-1 : ℝ) 1).indicator (fun x ↦ (1 - x ^ 2) ^ 2) := by
    funext x
    simp only [Set.indicator]
    simp
  rw [hind, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  have h1 : IntervalIntegrable (fun _ : ℝ ↦ (1 : ℝ)) volume (-1) 1 :=
    (by fun_prop : Continuous (fun _ : ℝ ↦ (1 : ℝ))).intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun x : ℝ ↦ 2 * x ^ 2) volume (-1) 1 :=
    (by fun_prop : Continuous (fun x : ℝ ↦ 2 * x ^ 2)).intervalIntegrable _ _
  have h4 : IntervalIntegrable (fun x : ℝ ↦ x ^ 4) volume (-1) 1 :=
    (by fun_prop : Continuous (fun x : ℝ ↦ x ^ 4)).intervalIntegrable _ _
  rw [show (fun x : ℝ ↦ (1 - x ^ 2) ^ 2) =
      (fun x : ℝ ↦ 1 - 2 * x ^ 2 + x ^ 4) by grind,
    intervalIntegral.integral_add (h1.sub h2) h4,
    intervalIntegral.integral_sub h1 h2,
    intervalIntegral.integral_const,
    intervalIntegral.integral_const_mul,
    integral_pow, integral_pow]
  norm_num

@[simp]
theorem tartarWeightConvolution_zero :
    tartarWeightConvolution 0 = 16 / 15 := by
  rw [tartarWeightConvolution]
  have h :
      (fun t : ℝ ↦ Tartar.weight t * Tartar.weight (0 - t)) =
        (fun t : ℝ ↦ Tartar.weight t ^ 2) := by
    funext t
    rw [zero_sub, tartarWeight_neg, pow_two]
  rw [h, integral_tartarWeight_sq]

theorem integral_tartarTestFunction :
    ∫ x : ℝ, Tartar.testFunction x = 6 * Real.pi / 5 := by
  have h := cosineTransform_tartarTestFunction 0
  simp only [Poitou.cosineTransform, zero_mul, Real.cos_zero, mul_one,
    tartarWeightConvolution_zero] at h
  grind

end NumberField.Odlyzko
