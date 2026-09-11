/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.WholeSpaceGaussianEvolution
public import LeanPool.NavierStokesAndEuler.Euler.WholeSpaceGaussianLow
public import LeanPool.NavierStokesAndEuler.Euler.MeanSobolevBoundedField
public import LeanPool.NavierStokesAndEuler.Euler.OrdinarySmoothWords
import LeanPool.NavierStokesAndEuler.Euler.MeanHarmonicLaplacian
import LeanPool.NavierStokesAndEuler.Euler.WholeSpaceGaussianIntegration
public import LeanPool.NavierStokesAndEuler.Euler.WholeSpaceGaussian
import LeanPool.NavierStokesAndEuler.Euler.WholeSpaceGaussianKernel
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! The heat estimates specialized to genuine ordinary smooth L² fields. -/

section

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

end
end

end

@[expose] public section

noncomputable section

namespace EulerWholeSpaceGaussian

open MeasureTheory InnerProductSpace EulerSmoothLimit Filter Set ContinuousLinearMap
  EulerLpTranslation EulerLpTranslation.SmoothL2Field EulerMeanSobolevBoundedField
  EulerOrdinarySobolev EulerVectorCalculus EulerMeanHarmonic Laplacian
open scoped ContDiff ENNReal RealInnerProductSpace Topology

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem average_integrable_of_memLp {t : ℝ} (ht : 0 < t)
    (f : Space → V) (hf : MemLp f 2 volume) (x : Space) :
    Integrable (fun y : Space => kernel t y • f (x+y)) := by
  have hs : MemLp (fun y : Space => f (x+y)) 2 volume :=
    hf.comp_measurePreserving (measurePreserving_add_left (volume : Measure Space) x)
  exact memLp_one_iff_integrable.mp (hs.smul (kernel_memLp ht))

theorem average_sub {t : ℝ} (ht : 0 < t) (f g : Space → V)
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) (x : Space) :
    average t (fun y => f y-g y) x = average t f x-average t g x := by
  simp only [average, smul_sub]
  exact integral_sub (average_integrable_of_memLp ht f hf x) (average_integrable_of_memLp ht g hg x)

theorem average_sum {t : ℝ} (ht : 0 < t) (f : Fin 3 → Space → V)
    (hf : ∀ i, MemLp (f i) 2 volume) (x : Space) :
    average t (fun y => ∑ i : Fin 3, f i y) x = ∑ i : Fin 3, average t (f i) x := by
  simp only [average, Finset.smul_sum]
  exact integral_finsetSum Finset.univ (fun i _ => average_integrable_of_memLp ht (f i) (hf i) x)

theorem secondAverage_directional_bound {t : ℝ} (ht : 0 < t)
    (A : SmoothL2Field V) (j : Fin 3) (x : Space) :
    ‖secondAverage t (A.directionalField (axis j)).field x‖ ≤
      3*t^(-(3:ℝ)/4)*‖A.jetLp 3‖ := by
  let w (i : Fin 3) : Fin 3 → Fin 3 := ![i,i,j]
  have he (i : Fin 3) : (wordField A (w i)).field =
      fun z => fderiv ℝ (fun y => fderiv ℝ (A.directionalField (axis j)).field y
        (EuclideanSpace.single i 1)) z (EuclideanSpace.single i 1) := by
    rfl
  have h (i : Fin 3) : ‖average t (wordField A (w i)).field x‖ ≤
      t^(-(3:ℝ)/4)*‖A.jetLp 3‖ :=
    (average_smoothField_norm ht (wordField A (w i)) x).trans
      (mul_le_mul_of_nonneg_left (wordField_toLp_norm_le A (w i)) (Real.rpow_nonneg ht.le _))
  unfold secondAverage
  calc
    _ ≤ ∑ i : Fin 3, ‖average t (wordField A (w i)).field x‖ := by
      simpa only [he] using norm_sum_le Finset.univ (fun i : Fin 3 => average t (wordField A (w
          i)).field x)
    _ ≤ ∑ _i : Fin 3, t^(-(3:ℝ)/4)*‖A.jetLp 3‖ := Finset.sum_le_sum (fun i _ => h i)
    _ = _ := by simp; ring

section Bounded

variable [FiniteDimensional ℝ V]

theorem field_sup_bound (A : SmoothL2Field V) (x : Space) :
    ‖A.field x‖ ≤ ‖finiteField A‖ := by
  simpa only [finiteField_apply] using (finiteField A).norm_coe_le_norm x

theorem average_field_hasDerivAt {t : ℝ} (ht : 0 < t) (A : SmoothL2Field V) (x : Space) :
    HasDerivAt (fun s : ℝ => average s A.field x) ((1/4:ℝ) • secondAverage t A.field x) t :=
  average_hasDerivAt ht A.field A.smooth ‖finiteField A‖ ‖finiteField A.derivative‖
    ‖finiteField A.derivative.derivative‖ (field_sup_bound A)
    (field_sup_bound A.derivative) (field_sup_bound A.derivative.derivative) x

theorem scaledAverage_field_hasDerivAt {t : ℝ} (ht : 0 < t) (A : SmoothL2Field V) (x : Space) :
    HasDerivAt (fun s : ℝ => scaledAverage s A.field x) ((1/4:ℝ) • secondAverage t A.field x) t :=
        by
  apply (average_field_hasDerivAt ht A x).congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ht] with s hs
  exact scaledAverage_eq hs A.field x

theorem average_field_first_bound (A : SmoothL2Field V) (a x : Space) :
    ‖average 1 (fun y => fderiv ℝ A.field y a) x‖ ≤ lowCost*‖a‖*‖A.toLp‖ := by
  simpa only [field_norm] using average_first_L2_bound A.field A.smooth A.memLp
    ‖finiteField A‖ ‖finiteField A.derivative‖ (field_sup_bound A) (field_sup_bound A.derivative) a
        x

theorem average_field_second_bound {t : ℝ} (ht : 0 < t)
    (A : SmoothL2Field V) (W : ℝ) (hW : ∀ x, ‖A.field x‖ ≤ W) (a b x : Space) :
    ‖average t (fun z => fderiv ℝ (fun y => fderiv ℝ A.field y b) z a) x‖ ≤
      (10*(2:ℝ)^((3:ℝ)/2))*t⁻¹*‖a‖*‖b‖*W :=
  average_second_bound ht A.field A.smooth W ‖finiteField A.derivative‖
    ‖finiteField A.derivative.derivative‖ hW (field_sup_bound A.derivative)
    (field_sup_bound A.derivative.derivative) a b x

end Bounded

theorem secondAverage_eq_laplacian {t : ℝ} (ht : 0 < t)
    (A : SmoothL2Field ℝ) (x : Space) :
    secondAverage t A.field x = average t (Δ A.field) x := by
  have he : (Δ A.field) = fun y => ∑ i : Fin 3,
      ((A.directionalField (axis i)).directionalField (axis i)).field y := by
    funext y
    exact laplacian_eq_coordinate_sum A.field A.smooth y
  rw [he, average_sum ht _ (fun i => ((A.directionalField (axis i)).directionalField (axis
      i)).memLp)]
  rfl

end EulerWholeSpaceGaussian
