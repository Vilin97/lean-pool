/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.WholeSpaceGaussianKernel
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! The literal time derivative of the Gaussian density and local domination. -/

@[expose] public section


noncomputable section

namespace EulerWholeSpaceGaussian

open MeasureTheory InnerProductSpace EulerSmoothLimit Filter Set
open scoped ContDiff ENNReal RealInnerProductSpace Topology

/-- Time kernel, given by `(t⁻¹^2*‖y‖^2-(3/2:ℝ)*t⁻¹)*kernel t y`. -/
def timeKernel (t : ℝ) (y : Space) : ℝ :=
  (t⁻¹^2*‖y‖^2-(3/2:ℝ)*t⁻¹)*kernel t y

theorem normalization_hasDerivAt {t : ℝ} (ht : 0 < t) :
    HasDerivAt normalization (-(3/2:ℝ)*t⁻¹*normalization t) t := by
  have h := ((hasDerivAt_id t).const_mul Real.pi).rpow_const
    (p := -(3:ℝ)/2) (Or.inl (mul_pos Real.pi_pos ht).ne')
  change HasDerivAt normalization _ t at h
  convert h using 1
  simp only [id_eq, mul_one]
  rw [Real.rpow_sub_one (mul_pos Real.pi_pos ht).ne']
  unfold normalization
  field_simp

theorem kernel_hasDerivAt {t : ℝ} (ht : 0 < t) (y : Space) :
    HasDerivAt (fun s : ℝ => kernel s y) (timeKernel t y) t := by
  have h := (normalization_hasDerivAt ht).mul
    (((hasDerivAt_inv ht.ne').neg.mul_const (‖y‖^2)).exp)
  change HasDerivAt (fun s : ℝ => kernel s y) _ t at h
  convert h using 1
  simp only [timeKernel, kernel, inv_pow, Pi.neg_apply, neg_neg]
  ring

theorem timeKernel_continuous (t : ℝ) : Continuous (timeKernel t) := by
  unfold timeKernel
  exact ((continuous_const.mul (continuous_norm.pow 2)).sub continuous_const).mul
    (kernel_smooth t).continuous

theorem timeKernel_second_sum (t : ℝ) (y : Space) :
    timeKernel t y = (1/4:ℝ) * ∑ i : Fin 3,
      secondKernel t (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) y := by
  simp [timeKernel, secondKernel, EuclideanSpace.inner_single_right,
    EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
  ring

theorem timeKernel_bound {t : ℝ} (ht : 0 < t) (y : Space) :
    ‖timeKernel t y‖ ≤ ((15/2:ℝ)*t⁻¹)*wideKernel t y := by
  rw [timeKernel_second_sum, norm_mul, Real.norm_of_nonneg (by norm_num : (0:ℝ) ≤ 1/4)]
  apply (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by norm_num : (0:ℝ) ≤ 1/4)).trans
  have h (i : Fin 3) :
      ‖secondKernel t (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) y‖ ≤
        10*t⁻¹*wideKernel t y := by
    simpa only [PiLp.norm_single, norm_one, mul_one] using
      secondKernel_bound ht (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) y
  have hb := Finset.sum_le_sum (fun i (_hi : i ∈ (Finset.univ : Finset (Fin 3))) => h i)
  have hc := mul_le_mul_of_nonneg_left hb (by norm_num : (0:ℝ) ≤ 1/4)
  apply hc.trans_eq
  simp only [Fin.sum_univ_three]
  ring

theorem timeKernel_integrable {t : ℝ} (ht : 0 < t) : Integrable (timeKernel t) := by
  apply ((wideKernel_integrable ht).const_mul ((15/2:ℝ)*t⁻¹)).mono'
    (timeKernel_continuous t).aestronglyMeasurable
  exact Eventually.of_forall (timeKernel_bound ht)

/-- Time envelope, given by `(15*t⁻¹*normalization (t/2))*Real.exp (-(4*t)⁻¹*‖y‖^2)`. -/
def timeEnvelope (t : ℝ) (y : Space) : ℝ :=
  (15*t⁻¹*normalization (t/2))*Real.exp (-(4*t)⁻¹*‖y‖^2)

theorem timeEnvelope_integrable {t : ℝ} (ht : 0 < t) : Integrable (timeEnvelope t) :=
  (exp_integrable (inv_pos.mpr (by positivity : 0 < 4*t))).const_mul _

theorem normalization_antitone {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) :
    normalization t ≤ normalization s := by
  apply Real.rpow_le_rpow_of_nonpos (mul_pos Real.pi_pos hs)
  · exact mul_le_mul_of_nonneg_left hst Real.pi_pos.le
  · norm_num

theorem timeKernel_local_bound {t : ℝ} (ht : 0 < t) (s : ℝ)
    (hs : s ∈ Ioo (t / 2) (2 * t)) (y : Space) :
    ‖timeKernel s y‖ ≤ timeEnvelope t y := by
  have hhalf : 0 < t/2 := by positivity
  have hspos : 0 < s := hhalf.trans hs.1
  have hn : normalization s ≤ normalization (t/2) := normalization_antitone hhalf hs.1.le
  have hi : s⁻¹ ≤ (t/2)⁻¹ := inv_anti₀ hhalf hs.1.le
  have hei : (4*t)⁻¹ ≤ (2*s)⁻¹ := inv_anti₀ (by positivity) (by linarith [hs.2])
  have he : Real.exp (-(2*s)⁻¹*‖y‖^2) ≤ Real.exp (-(4*t)⁻¹*‖y‖^2) := by
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg ‖y‖]
  apply (timeKernel_bound hspos y).trans
  change ((15/2:ℝ)*s⁻¹)*(normalization s*Real.exp (-(2*s)⁻¹*‖y‖^2)) ≤ _
  calc
    _ ≤ ((15/2:ℝ)*(t/2)⁻¹)*(normalization (t/2)*Real.exp (-(4*t)⁻¹*‖y‖^2)) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hi (by norm_num)
      · exact mul_le_mul hn he (Real.exp_pos _).le (normalization_pos hhalf).le
      · exact mul_nonneg (normalization_pos hspos).le (Real.exp_pos _).le
      · positivity
    _ = _ := by unfold timeEnvelope; field_simp

end EulerWholeSpaceGaussian
