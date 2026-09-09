/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.WholeSpaceGaussianTimeKernel
public import LeanPool.NavierStokesAndEuler.Euler.WholeSpaceGaussianIntegration
public import LeanPool.NavierStokesAndEuler.Euler.WholeSpaceGaussianScale

@[expose] public section

/-! The true heat-time evolution of Gaussian averaging on ordinary space. -/

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
      continuous_id))).aestronglyMeasurable
  have hFd : AEStronglyMeasurable (F' t) volume :=
    ((timeKernel_continuous t).smul (hf.comp (continuous_const.add
      continuous_id))).aestronglyMeasurable
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
