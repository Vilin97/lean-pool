/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

import LeanPool.NavierStokesAndEuler.ForMathlib.StronglyMeasurable
import LeanPool.NavierStokesAndEuler.Euler.WholeSpaceGaussianIntegration
import Mathlib.Analysis.Calculus.ParametricIntegral
public import LeanPool.NavierStokesAndEuler.Euler.WholeSpaceGaussianKernel
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Function.L2Space

/-! Related estimates used together by the same construction modules. -/

section

/-! The true heat-time evolution of Gaussian averaging on ordinary space. -/

section

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
    (timeKernel_continuous t).aestronglyMeasurable_of_secondCountable
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

end
end

end

@[expose] public section

noncomputable section

namespace EulerWholeSpaceGaussian

open MeasureTheory InnerProductSpace EulerSmoothLimit Filter Set ContinuousLinearMap
open scoped ContDiff ENNReal RealInnerProductSpace Topology

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Differentiating the explicit kernel under its ordinary Bochner integral. -/
theorem average_hasDerivAt_kernel {t : ℝ} (ht : 0 < t)
    (f : Space → V) (hf : Continuous f) (C₀ : ℝ)
    (h₀ : ∀ x, ‖f x‖ ≤ C₀) (x : Space) :
    HasDerivAt (fun s : ℝ => average s f x)
      (∫ y : Space, timeKernel t y • f (x+y)) t := by
  have hC₀ : 0 ≤ C₀ := (norm_nonneg (f x)).trans (h₀ x)
  let F : ℝ → Space → V := fun s y => kernel s y • f (x+y)
  let F' : ℝ → Space → V := fun s y => timeKernel s y • f (x+y)
  have hF (s : ℝ) : AEStronglyMeasurable (F s) volume :=
    ((kernel_smooth s).continuous.smul (hf.comp (continuous_const.add
        continuous_id))).aestronglyMeasurable_of_secondCountable
  have hFd : AEStronglyMeasurable (F' t) volume :=
    ((timeKernel_continuous t).smul (hf.comp (continuous_const.add
        continuous_id))).aestronglyMeasurable_of_secondCountable
  have hb (y : Space) (s : ℝ) (hs : s ∈ Ioo (t/2) (2*t)) :
      ‖F' s y‖ ≤ timeEnvelope t y*C₀ := by
    change ‖timeKernel s y • f (x+y)‖ ≤ _
    rw [norm_smul]
    apply mul_le_mul (timeKernel_local_bound ht s hs y) (h₀ (x+y)) (norm_nonneg _)
    unfold timeEnvelope
    have hp := normalization_pos (by positivity : 0 < t/2)
    positivity
  have hd (y : Space) (s : ℝ) (hs : s ∈ Ioo (t/2) (2*t)) :
      HasDerivAt (fun r => F r y) (F' s y) s :=
    (kernel_hasDerivAt (by linarith [hs.1] : 0 < s) y).smul_const (f (x+y))
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (bound := fun y : Space => timeEnvelope t y*C₀)
    (Ioo_mem_nhds (by linarith : t/2 < t) (by linarith : t < 2*t))
    (Eventually.of_forall hF) (average_integrable_of_bound ht f hf C₀ h₀ x) hFd
    (Eventually.of_forall hb) ((timeEnvelope_integrable ht).mul_const C₀)
    (Eventually.of_forall hd)
  exact h.2

/-- Second average, given by `∑ i : Fin 3, average t (fun z => fderiv ℝ (fun y => fderiv ℝ f y
(EuclideanSpace.single i 1)) z (EuclideanSpace.single i 1)) x`. -/
def secondAverage (t : ℝ) (f : Space → V) (x : Space) : V :=
  ∑ i : Fin 3, average t (fun z =>
    fderiv ℝ (fun y => fderiv ℝ f y (EuclideanSpace.single i 1)) z
      (EuclideanSpace.single i 1)) x

/-- The explicit time-kernel integral equals one quarter of the sum of
the actual second spatial derivatives averaged against the same Gaussian. -/
theorem timeIntegral_eq_secondAverage {t : ℝ} (ht : 0 < t)
    (f : Space → V) (hf : ContDiff ℝ ∞ f) (C₀ C₁ C₂ : ℝ)
    (h₀ : ∀ x, ‖f x‖ ≤ C₀) (h₁ : ∀ x, ‖fderiv ℝ f x‖ ≤ C₁)
    (h₂ : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ C₂) (x : Space) :
    (∫ y : Space, timeKernel t y • f (x+y)) = (1/4:ℝ) • secondAverage t f x := by
  have hi (i : Fin 3) : Integrable (fun y : Space =>
      secondKernel t (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) y • f (x+y)) :=
    integrable_kernel_smul _ (secondKernel_integrable ht _ _) _
      (hf.continuous.comp (continuous_const.add continuous_id)) C₀ (fun y => h₀ (x+y))
  simp_rw [timeKernel_second_sum, mul_smul, Finset.sum_smul]
  rw [integral_smul, integral_finsetSum Finset.univ (fun i _ => hi i)]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact (average_second_identity ht f hf C₀ C₁ C₂ h₀ h₁ h₂ _ _ x).symm

theorem average_hasDerivAt {t : ℝ} (ht : 0 < t)
    (f : Space → V) (hf : ContDiff ℝ ∞ f) (C₀ C₁ C₂ : ℝ)
    (h₀ : ∀ x, ‖f x‖ ≤ C₀) (h₁ : ∀ x, ‖fderiv ℝ f x‖ ≤ C₁)
    (h₂ : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ C₂) (x : Space) :
    HasDerivAt (fun s : ℝ => average s f x) ((1/4:ℝ) • secondAverage t f x) t := by
  rw [← timeIntegral_eq_secondAverage ht f hf C₀ C₁ C₂ h₀ h₁ h₂ x]
  exact average_hasDerivAt_kernel ht f hf.continuous C₀ h₀ x

end EulerWholeSpaceGaussian

end
end

end

section

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

end
end

end
