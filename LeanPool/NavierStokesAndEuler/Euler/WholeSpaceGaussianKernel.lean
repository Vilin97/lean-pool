/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.WholeSpaceGaussian
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-! Actual first and second Gaussian kernels and their integrable bounds. -/

@[expose] public section


noncomputable section

namespace EulerWholeSpaceGaussian

open MeasureTheory InnerProductSpace EulerSmoothLimit Filter
open scoped ContDiff ENNReal RealInnerProductSpace

/-- Wide kernel, given by `normalization t * Real.exp (-(2*t)⁻¹*‖x‖^2)`. -/
def wideKernel (t : ℝ) (x : Space) : ℝ :=
  normalization t * Real.exp (-(2*t)⁻¹*‖x‖^2)

/-- First kernel, given by `(-2*t⁻¹*⟪x,a⟫_ℝ) * kernel t x`. -/
def firstKernel (t : ℝ) (a x : Space) : ℝ :=
  (-2*t⁻¹*⟪x,a⟫_ℝ) * kernel t x

/-- Second kernel, given by `(4*t⁻¹^2*⟪x,a⟫_ℝ*⟪x,b⟫_ℝ - 2*t⁻¹*⟪a,b⟫_ℝ) * kernel t x`. -/
def secondKernel (t : ℝ) (a b x : Space) : ℝ :=
  (4*t⁻¹^2*⟪x,a⟫_ℝ*⟪x,b⟫_ℝ - 2*t⁻¹*⟪a,b⟫_ℝ) * kernel t x

theorem firstKernel_smooth (t : ℝ) (a : Space) : ContDiff ℝ ∞ (firstKernel t a) := by
  unfold firstKernel
  exact (contDiff_const.mul (contDiff_id.inner ℝ contDiff_const)).mul (kernel_smooth t)

theorem secondKernel_smooth (t : ℝ) (a b : Space) :
    ContDiff ℝ ∞ (secondKernel t a b) := by
  unfold secondKernel
  exact (((contDiff_const.mul (contDiff_id.inner ℝ contDiff_const)).mul
    (contDiff_id.inner ℝ contDiff_const)).sub contDiff_const).mul (kernel_smooth t)

theorem kernel_fderiv (t : ℝ) (a x : Space) :
    fderiv ℝ (kernel t) x a = firstKernel t a x := by
  have h := (((hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_mul (-t⁻¹)).exp).const_mul
    (normalization t)
  have he := congrArg (fun A : Space →L[ℝ] ℝ => A a) h.fderiv
  change fderiv ℝ (kernel t) x a = _ at he
  rw [he]
  simp only [smul_apply, innerSL_apply_apply, smul_eq_mul, firstKernel, kernel]
  ring

theorem firstKernel_fderiv (t : ℝ) (a b x : Space) :
    fderiv ℝ (firstKernel t a) x b = secondKernel t a b x := by
  have hi : HasFDerivAt (fun y : Space => ⟪y,a⟫_ℝ) (innerSL ℝ a) x := by
    have h0 : HasFDerivAt (fun y : Space => ⟪a,y⟫_ℝ) (innerSL ℝ a) x :=
      (innerSL ℝ a).hasFDerivAt
    simpa only [real_inner_comm a] using h0
  have h := (hi.const_mul (-2*t⁻¹)).mul ((kernel_smooth t).differentiable (by simp) x).hasFDerivAt
  have he := congrArg (fun A : Space →L[ℝ] ℝ => A b) h.fderiv
  change fderiv ℝ (firstKernel t a) x b = _ at he
  rw [he]
  simp only [add_apply, smul_apply, innerSL_apply_apply,
    smul_eq_mul, kernel_fderiv, firstKernel, secondKernel]
  ring

theorem wideKernel_nonneg {t : ℝ} (ht : 0 < t) (x : Space) : 0 ≤ wideKernel t x :=
  mul_nonneg (normalization_pos ht).le (Real.exp_pos _).le

theorem wideKernel_integrable {t : ℝ} (ht : 0 < t) : Integrable (wideKernel t) :=
  (exp_integrable (inv_pos.mpr (by positivity : 0 < 2*t))).const_mul _

theorem integral_wideKernel {t : ℝ} (ht : 0 < t) :
    (∫ x : Space, wideKernel t x) = (2:ℝ)^((3:ℝ)/2) := by
  have hdim : Module.finrank ℝ Space = 3 := by simp [Space]
  simp only [wideKernel]
  rw [integral_const_mul, GaussianFourier.integral_rexp_neg_mul_sq_norm
    (inv_pos.mpr (by positivity : 0 < 2*t)), hdim]
  simp only [Nat.cast_ofNat, div_inv_eq_mul]
  rw [show Real.pi*(2*t) = 2*(Real.pi*t) by ring,
    Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (mul_pos Real.pi_pos ht).le]
  unfold normalization
  rw [mul_left_comm, ← Real.rpow_add (mul_pos Real.pi_pos ht)]
  norm_num

theorem kernel_le_wideKernel {t : ℝ} (ht : 0 < t) (x : Space) :
    kernel t x ≤ wideKernel t x := by
  apply mul_le_mul_of_nonneg_left _ (normalization_pos ht).le
  apply Real.exp_le_exp.mpr
  have hi : (2*t)⁻¹ ≤ t⁻¹ := by apply inv_anti₀ ht; linarith
  nlinarith [sq_nonneg ‖x‖]

/-- A Gaussian absorbs its quadratic factor at twice the spatial variance. -/
theorem norm_sq_kernel_le {t : ℝ} (ht : 0 < t) (x : Space) :
    ‖x‖^2 * kernel t x ≤ 2*t * wideKernel t x := by
  let s : ℝ := (2*t)⁻¹*‖x‖^2
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have hse : s ≤ Real.exp s := le_trans (by linarith) (Real.add_one_le_exp s)
  have he : s*Real.exp (-2*s) ≤ Real.exp (-s) := by
    calc
      _ ≤ Real.exp s * Real.exp (-2*s) := mul_le_mul_of_nonneg_right hse (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have h0 : 2*t*s = ‖x‖^2 := by dsimp [s]; field_simp
  have h1 : -t⁻¹*‖x‖^2 = -2*s := by dsimp [s]; field_simp
  have h := mul_le_mul_of_nonneg_left he (mul_nonneg (by positivity : 0 ≤ 2*t)
    (normalization_pos ht).le)
  calc
    _ = (2*t*normalization t)*(s*Real.exp (-2*s)) := by
      unfold kernel
      rw [h1, ← h0]
      ring
    _ ≤ (2*t*normalization t)*Real.exp (-s) := h
    _ = _ := by unfold wideKernel; dsimp [s]; ring_nf

theorem norm_kernel_le {t : ℝ} (ht : 0 < t) (x : Space) :
    ‖x‖ * kernel t x ≤ (1+2*t)*wideKernel t x := by
  have h : ‖x‖ ≤ 1+‖x‖^2 := by nlinarith [sq_nonneg (‖x‖-1)]
  calc
    _ ≤ (1+‖x‖^2)*kernel t x := mul_le_mul_of_nonneg_right h (kernel_nonneg ht x)
    _ = kernel t x + ‖x‖^2*kernel t x := by ring
    _ ≤ wideKernel t x + 2*t*wideKernel t x :=
      add_le_add (kernel_le_wideKernel ht x) (norm_sq_kernel_le ht x)
    _ = _ := by ring

theorem firstKernel_bound {t : ℝ} (ht : 0 < t) (a x : Space) :
    ‖firstKernel t a x‖ ≤ (2*t⁻¹*(1+2*t)*‖a‖)*wideKernel t x := by
  have h : ‖⟪x,a⟫_ℝ‖ ≤ ‖x‖*‖a‖ := norm_inner_le_norm x a
  calc
    _ = 2*t⁻¹*‖⟪x,a⟫_ℝ‖*kernel t x := by
      simp only [firstKernel, norm_mul, norm_neg, Real.norm_ofNat,
        Real.norm_of_nonneg (inv_pos.mpr ht).le, Real.norm_of_nonneg (kernel_nonneg ht x)]
    _ ≤ 2*t⁻¹*(‖x‖*‖a‖)*kernel t x :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h (by positivity))
        (kernel_nonneg ht x)
    _ = (2*t⁻¹*‖a‖)*(‖x‖*kernel t x) := by ring
    _ ≤ (2*t⁻¹*‖a‖)*((1+2*t)*wideKernel t x) :=
      mul_le_mul_of_nonneg_left (norm_kernel_le ht x) (by positivity)
    _ = _ := by ring

theorem secondKernel_bound {t : ℝ} (ht : 0 < t) (a b x : Space) :
    ‖secondKernel t a b x‖ ≤ (10*t⁻¹*‖a‖*‖b‖)*wideKernel t x := by
  have hab : ‖⟪a,b⟫_ℝ‖ ≤ ‖a‖*‖b‖ := norm_inner_le_norm a b
  have hxa : ‖⟪x,a⟫_ℝ‖ ≤ ‖x‖*‖a‖ := norm_inner_le_norm x a
  have hxb : ‖⟪x,b⟫_ℝ‖ ≤ ‖x‖*‖b‖ := norm_inner_le_norm x b
  have hpoly : ‖4*t⁻¹^2*⟪x,a⟫_ℝ*⟪x,b⟫_ℝ - 2*t⁻¹*⟪a,b⟫_ℝ‖ ≤
      4*t⁻¹^2*‖x‖^2*‖a‖*‖b‖ + 2*t⁻¹*‖a‖*‖b‖ := by
    apply (norm_sub_le _ _).trans
    simp only [norm_mul, norm_pow, Real.norm_ofNat,
      Real.norm_of_nonneg (inv_pos.mpr ht).le]
    calc
      _ = 4*t⁻¹^2*(‖⟪x,a⟫_ℝ‖*‖⟪x,b⟫_ℝ‖) + 2*t⁻¹*‖⟪a,b⟫_ℝ‖ := by ring
      _ ≤ 4*t⁻¹^2*((‖x‖*‖a‖)*(‖x‖*‖b‖)) + 2*t⁻¹*(‖a‖*‖b‖) :=
        add_le_add (mul_le_mul_of_nonneg_left
          (mul_le_mul hxa hxb (norm_nonneg _) (by positivity)) (by positivity))
          (mul_le_mul_of_nonneg_left hab (by positivity))
      _ = _ := by ring
  calc
    _ ≤ (4*t⁻¹^2*‖x‖^2*‖a‖*‖b‖ + 2*t⁻¹*‖a‖*‖b‖)*kernel t x := by
      rw [secondKernel, norm_mul, Real.norm_of_nonneg (kernel_nonneg ht x)]
      exact mul_le_mul_of_nonneg_right hpoly (kernel_nonneg ht x)
    _ = (4*t⁻¹^2*‖a‖*‖b‖)*(‖x‖^2*kernel t x) +
        (2*t⁻¹*‖a‖*‖b‖)*kernel t x := by ring
    _ ≤ (4*t⁻¹^2*‖a‖*‖b‖)*(2*t*wideKernel t x) +
        (2*t⁻¹*‖a‖*‖b‖)*wideKernel t x :=
      add_le_add (mul_le_mul_of_nonneg_left (norm_sq_kernel_le ht x) (by positivity))
        (mul_le_mul_of_nonneg_left (kernel_le_wideKernel ht x) (by positivity))
    _ = _ := by field_simp; ring

theorem firstKernel_integrable {t : ℝ} (ht : 0 < t) (a : Space) :
    Integrable (firstKernel t a) := by
  apply ((wideKernel_integrable ht).const_mul (2*t⁻¹*(1+2*t)*‖a‖)).mono'
    (firstKernel_smooth t a).continuous.aestronglyMeasurable
  exact Eventually.of_forall (firstKernel_bound ht a)

theorem secondKernel_integrable {t : ℝ} (ht : 0 < t) (a b : Space) :
    Integrable (secondKernel t a b) := by
  apply ((wideKernel_integrable ht).const_mul (10*t⁻¹*‖a‖*‖b‖)).mono'
    (secondKernel_smooth t a b).continuous.aestronglyMeasurable
  exact Eventually.of_forall (secondKernel_bound ht a b)

/-- The actual two-derivative Gaussian kernel has the essential 1/t L¹ bound. -/
theorem secondKernel_L1_bound {t : ℝ} (ht : 0 < t) (a b : Space) :
    (∫ x : Space, ‖secondKernel t a b x‖) ≤
      (10*(2:ℝ)^((3:ℝ)/2))*t⁻¹*‖a‖*‖b‖ := by
  calc
    _ ≤ ∫ x : Space, (10*t⁻¹*‖a‖*‖b‖)*wideKernel t x :=
      integral_mono (secondKernel_integrable ht a b).norm
        ((wideKernel_integrable ht).const_mul _) (secondKernel_bound ht a b)
    _ = _ := by rw [integral_const_mul, integral_wideKernel ht]; ring

end EulerWholeSpaceGaussian
