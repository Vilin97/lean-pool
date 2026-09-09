/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.WholeSpaceGaussian
import LeanPool.NavierStokesAndEuler.Euler.WholeSpaceGaussianKernel
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! The same Gaussian average as a continuous dilation of a fixed kernel. -/

@[expose] public section


noncomputable section

namespace EulerWholeSpaceGaussian

open MeasureTheory InnerProductSpace EulerSmoothLimit Filter Set
open scoped ContDiff ENNReal RealInnerProductSpace Topology

theorem normalization_sq {c : ℝ} (hc : 0 < c) :
    normalization (c^2) = (c^3)⁻¹*normalization 1 := by
  unfold normalization
  rw [mul_one, Real.mul_rpow Real.pi_pos.le (sq_nonneg c)]
  have h : (c^2)^(-(3:ℝ)/2) = (c^3)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hc.le]
    norm_num [Real.rpow_neg, Real.rpow_natCast]
  rw [h, mul_comm]

theorem kernel_sq_smul {c : ℝ} (hc : 0 < c) (y : Space) :
    kernel (c^2) (c • y) = (c^3)⁻¹*kernel 1 y := by
  unfold kernel
  rw [normalization_sq hc, norm_smul, Real.norm_of_nonneg hc.le, mul_pow]
  have he : -(c^2)⁻¹*(c^2*‖y‖^2) = -(1:ℝ)⁻¹*‖y‖^2 := by field_simp
  rw [he]
  ring

theorem norm_mul_kernel_integrable {t : ℝ} (ht : 0 < t) :
    Integrable (fun y : Space => ‖y‖*kernel t y) := by
  apply ((wideKernel_integrable ht).const_mul (1+2*t)).mono'
    (continuous_norm.mul (kernel_smooth t).continuous).aestronglyMeasurable
  exact Eventually.of_forall (fun y => by
    change ‖‖y‖*kernel t y‖ ≤ (1+2*t)*wideKernel t y
    rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (kernel_nonneg ht y))]
    exact norm_kernel_le ht y)

section Averaging

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- This formula continues the actual heat average to t=0 by dilation. -/
def scaledAverage (t : ℝ) (f : Space → V) (x : Space) : V :=
  ∫ y : Space, kernel 1 y • f (x+Real.sqrt t • y)

theorem scaledAverage_eq {t : ℝ} (ht : 0 < t) (f : Space → V) (x : Space) :
    scaledAverage t f x = average t f x := by
  have hc : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have he (y : Space) : kernel t (Real.sqrt t • y) =
      (Real.sqrt t ^ 3)⁻¹*kernel 1 y := by
    simpa only [Real.sq_sqrt ht.le] using kernel_sq_smul hc y
  have h := Measure.integral_comp_smul_of_nonneg (volume : Measure Space)
    (fun y : Space => kernel t y • f (x+y)) (Real.sqrt t) (hR := hc.le)
  have hdim : Module.finrank ℝ Space = 3 := by simp [Space]
  simp only [he, mul_smul, integral_smul, hdim] at h
  change (Real.sqrt t ^ 3)⁻¹ • scaledAverage t f x =
    (Real.sqrt t ^ 3)⁻¹ • average t f x at h
  exact (smul_right_injective V (inv_ne_zero (pow_ne_zero 3 hc.ne'))).eq_iff.mp h

theorem scaledAverage_zero [CompleteSpace V] (f : Space → V) (x : Space) : scaledAverage 0 f x = f
    x := by
  simp only [scaledAverage, Real.sqrt_zero, zero_smul, add_zero, integral_smul_const,
    integral_kernel (by norm_num : (0:ℝ) < 1), one_smul]

theorem scaledAverage_continuous (f : Space → V) (hf : Continuous f)
    (C : ℝ) (hb : ∀ x, ‖f x‖ ≤ C) (x : Space) :
    Continuous (fun t : ℝ => scaledAverage t f x) := by
  apply continuous_of_dominated (bound := fun y : Space => kernel 1 y*C)
  · intro t
    exact ((kernel_smooth 1).continuous.smul
      (hf.comp (show Continuous (fun y : Space => x+Real.sqrt t • y) by
          fun_prop))).aestronglyMeasurable
  · intro t
    exact Eventually.of_forall (fun y => by
      rw [norm_smul, Real.norm_of_nonneg (kernel_nonneg (by norm_num) y)]
      exact mul_le_mul_of_nonneg_left (hb _) (kernel_nonneg (by norm_num) y))
  · exact (kernel_integrable (by norm_num : (0:ℝ)<1)).mul_const C
  · exact Eventually.of_forall (fun y =>
      continuous_const.smul (hf.comp
        (show Continuous (fun t : ℝ => x+Real.sqrt t • y) by fun_prop)))

theorem average_tendsto_zero [CompleteSpace V] (f : Space → V) (hf : Continuous f)
    (C : ℝ) (hb : ∀ x, ‖f x‖ ≤ C) (x : Space) :
    Tendsto (fun t : ℝ => average t f x) (𝓝[>] 0) (𝓝 (f x)) := by
  have h : Tendsto (fun t : ℝ => scaledAverage t f x) (𝓝[>] 0)
      (𝓝 (scaledAverage 0 f x)) :=
    (scaledAverage_continuous f hf C hb x).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  rw [scaledAverage_zero] at h
  exact h.congr' (eventually_nhdsWithin_of_forall (fun t ht => scaledAverage_eq ht f x))

end Averaging
end EulerWholeSpaceGaussian
