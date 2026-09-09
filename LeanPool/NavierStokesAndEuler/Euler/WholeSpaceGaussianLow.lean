/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.WholeSpaceGaussianKernel
import LeanPool.NavierStokesAndEuler.Euler.WholeSpaceGaussianIntegration
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Function.L2Space

/-! The low-frequency derivative of the true Gaussian average is controlled
by the ordinary L² norm of the original field. -/

@[expose] public section


noncomputable section

namespace EulerWholeSpaceGaussian

open MeasureTheory InnerProductSpace EulerSmoothLimit Filter
open scoped ContDiff ENNReal RealInnerProductSpace

theorem firstKernel_sq_bound {t : ℝ} (ht : 0 < t) (a y : Space) :
    ‖firstKernel t a y‖^2 ≤
      (8*t⁻¹*normalization t*‖a‖^2)*wideKernel t y := by
  have hi : ‖⟪y,a⟫_ℝ‖^2 ≤ ‖y‖^2*‖a‖^2 := by
    have h : ‖⟪y,a⟫_ℝ‖ ≤ ‖y‖*‖a‖ := norm_inner_le_norm y a
    simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg ⟪y,a⟫_ℝ) h 2
  have hk : kernel t y ^ 2 ≤ normalization t * kernel t y := by
    rw [pow_two]
    exact mul_le_mul_of_nonneg_right (kernel_le_normalization ht y) (kernel_nonneg ht y)
  calc
    _ = 4*t⁻¹^2*‖⟪y,a⟫_ℝ‖^2*(kernel t y)^2 := by
      simp only [firstKernel, norm_mul, norm_neg, Real.norm_ofNat,
        Real.norm_of_nonneg (inv_pos.mpr ht).le, Real.norm_of_nonneg (kernel_nonneg ht y)]
      ring
    _ ≤ 4*t⁻¹^2*(‖y‖^2*‖a‖^2)*(normalization t*kernel t y) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hi (by positivity)
      · exact hk
      · positivity
      · positivity
    _ = (4*t⁻¹^2*normalization t*‖a‖^2)*(‖y‖^2*kernel t y) := by ring
    _ ≤ (4*t⁻¹^2*normalization t*‖a‖^2)*(2*t*wideKernel t y) :=
      mul_le_mul_of_nonneg_left (norm_sq_kernel_le ht y)
        (by have := (normalization_pos ht).le; positivity)
    _ = _ := by field_simp; ring

theorem firstKernel_memLp {t : ℝ} (ht : 0 < t) (a : Space) :
    MemLp (firstKernel t a) 2 volume := by
  apply (memLp_two_iff_integrable_sq_norm
    (firstKernel_smooth t a).continuous.aestronglyMeasurable).2
  apply ((wideKernel_integrable ht).const_mul
    (8*t⁻¹*normalization t*‖a‖^2)).mono'
    (((firstKernel_smooth t a).continuous.norm).pow 2).aestronglyMeasurable
  exact Eventually.of_forall (fun y => by
    change ‖‖firstKernel t a y‖^2‖ ≤ _
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact firstKernel_sq_bound ht a y)

theorem integral_firstKernel_sq_bound {t : ℝ} (ht : 0 < t) (a : Space) :
    (∫ y : Space, ‖firstKernel t a y‖^2) ≤
      (8*normalization t*(2:ℝ)^((3:ℝ)/2))*t⁻¹*‖a‖^2 := by
  calc
    _ ≤ ∫ y : Space, (8*t⁻¹*normalization t*‖a‖^2)*wideKernel t y :=
      integral_mono ((memLp_two_iff_integrable_sq_norm
        (firstKernel_smooth t a).continuous.aestronglyMeasurable).1 (firstKernel_memLp ht a))
        ((wideKernel_integrable ht).const_mul _) (firstKernel_sq_bound ht a)
    _ = _ := by rw [integral_const_mul, integral_wideKernel ht]; ring

/-- Low cost, given by `Real.sqrt (8*normalization 1*(2:ℝ)^((3:ℝ)/2))`. -/
def lowCost : ℝ := Real.sqrt (8*normalization 1*(2:ℝ)^((3:ℝ)/2))

theorem lowCost_nonneg : 0 ≤ lowCost := Real.sqrt_nonneg _

theorem firstKernel_one_L2_bound (a : Space) :
    Real.sqrt (∫ y : Space, ‖firstKernel 1 a y‖^2) ≤ lowCost*‖a‖ := by
  have h := Real.sqrt_le_sqrt (integral_firstKernel_sq_bound (by norm_num : (0:ℝ)<1) a)
  simpa only [inv_one, mul_one, Real.sqrt_mul (by
    have := normalization_pos (by norm_num : (0:ℝ)<1)
    positivity : 0 ≤ 8*normalization 1*(2:ℝ)^((3:ℝ)/2)),
    Real.sqrt_sq (norm_nonneg a), lowCost] using h

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem average_first_L2_bound (f : Space → V) (hf : ContDiff ℝ ∞ f)
    (hLp : MemLp f 2 volume) (C₀ C₁ : ℝ)
    (h₀ : ∀ x, ‖f x‖ ≤ C₀) (h₁ : ∀ x, ‖fderiv ℝ f x‖ ≤ C₁) (a x : Space) :
    ‖average 1 (fun y => fderiv ℝ f y a) x‖ ≤
      lowCost*‖a‖*(eLpNorm f 2 volume).toReal := by
  rw [average_first_identity (by norm_num : (0:ℝ)<1) f hf C₀ C₁ h₀ h₁ a x, norm_neg]
  have hmp := measurePreserving_add_left (volume : Measure Space) x
  have hs : MemLp (fun y : Space => f (x+y)) 2 volume := hLp.comp_measurePreserving hmp
  have he : eLpNorm (fun y : Space => f (x+y)) 2 volume = eLpNorm f 2 volume :=
    eLpNorm_comp_measurePreserving hLp.aestronglyMeasurable hmp
  have h := norm_integral_smul_le (firstKernel 1 a) (fun y : Space => f (x+y))
    (firstKernel_memLp (by norm_num : (0:ℝ)<1) a) hs
  rw [he] at h
  exact h.trans (mul_le_mul_of_nonneg_right (firstKernel_one_L2_bound a) ENNReal.toReal_nonneg)

end EulerWholeSpaceGaussian
