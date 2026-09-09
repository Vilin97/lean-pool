/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.WholeSpaceGaussianKernel
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-! Integration by parts for the literal whole-space Gaussian average. -/

@[expose] public section


noncomputable section

namespace EulerWholeSpaceGaussian

open MeasureTheory InnerProductSpace EulerSmoothLimit Filter Set ContinuousLinearMap
open scoped ContDiff ENNReal RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem integrable_kernel_smul (k : Space → ℝ) (hk : Integrable k)
    (f : Space → V) (hf : Continuous f) (C : ℝ) (hb : ∀ x, ‖f x‖ ≤ C) :
    Integrable (fun x : Space => k x • f x) := by
  apply (hk.norm.mul_const C).mono' (hk.aestronglyMeasurable.smul hf.aestronglyMeasurable)
  exact Eventually.of_forall (fun x => by
    change ‖k x • f x‖ ≤ ‖k x‖ * C
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (hb x) (norm_nonneg _))

theorem fderiv_translate (f : Space → V) (hf : Differentiable ℝ f) (x y : Space) :
    fderiv ℝ (fun z : Space => f (x+z)) y = fderiv ℝ f (x+y) := by
  have h := (hf (x+y)).hasFDerivAt.comp y ((hasFDerivAt_id y).const_add x)
  change HasFDerivAt (fun z : Space => f (x+z)) _ y at h
  simpa only [ContinuousLinearMap.comp_id] using h.fderiv

/-- Integration by parts uses genuine spatial derivatives and only the
ordinary integrability of the scalar kernel and its derivative. -/
theorem integration_by_parts (k : Space → ℝ) (hk : Differentiable ℝ k)
    (hki : Integrable k) (a : Space)
    (hkai : Integrable (fun x => fderiv ℝ k x a))
    (f : Space → V) (hf : ContDiff ℝ ∞ f) (C₀ C₁ : ℝ)
    (h₀ : ∀ x, ‖f x‖ ≤ C₀) (h₁ : ∀ x, ‖fderiv ℝ f x‖ ≤ C₁) (x : Space) :
    (∫ y : Space, k y • fderiv ℝ f (x+y) a) =
      -(∫ y : Space, fderiv ℝ k y a • f (x+y)) := by
  have hfc : Continuous (fun y : Space => f (x+y)) := hf.continuous.comp (continuous_const.add
      continuous_id)
  have hfd : Continuous (fun y : Space => fderiv ℝ f (x+y) a) :=
    ((hf.fderiv_right (m := ∞) (by simp)).continuous.comp
      (continuous_const.add continuous_id)).clm_apply continuous_const
  have hfb (y : Space) : ‖fderiv ℝ f (x+y) a‖ ≤ C₁*‖a‖ :=
    (le_opNorm _ _).trans (mul_le_mul_of_nonneg_right (h₁ _) (norm_nonneg a))
  have hleft := integrable_kernel_smul _ hkai _ hfc C₀ (fun y => h₀ (x+y))
  have hright := integrable_kernel_smul k hki _ hfd (C₁*‖a‖) hfb
  have hbase := integrable_kernel_smul k hki _ hfc C₀ (fun y => h₀ (x+y))
  have h := integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable
    (μ := (volume : Measure Space)) (f := k) (g := fun y : Space => f (x+y)) (v := a)
    hleft (by simpa only [fderiv_translate f (hf.differentiable (by simp))] using hright)
    hbase (fun y _ => hk y)
    (fun y _ => (hf.differentiable (by simp)).differentiableAt.comp y
      ((differentiableAt_const x).add differentiableAt_id))
  simpa only [fderiv_translate f (hf.differentiable (by simp))] using h

theorem average_first_identity {t : ℝ} (ht : 0 < t)
    (f : Space → V) (hf : ContDiff ℝ ∞ f) (C₀ C₁ : ℝ)
    (h₀ : ∀ x, ‖f x‖ ≤ C₀) (h₁ : ∀ x, ‖fderiv ℝ f x‖ ≤ C₁) (a x : Space) :
    average t (fun y => fderiv ℝ f y a) x =
      -(∫ y : Space, firstKernel t a y • f (x+y)) := by
  have hi : Integrable (fun y : Space => fderiv ℝ (kernel t) y a) := by
    simpa only [kernel_fderiv] using firstKernel_integrable ht a
  simpa only [average, kernel_fderiv] using
    integration_by_parts (kernel t) ((kernel_smooth t).differentiable (by simp))
      (kernel_integrable ht) a hi f hf C₀ C₁ h₀ h₁ x

theorem directional_smooth (f : Space → V) (hf : ContDiff ℝ ∞ f) (a : Space) :
    ContDiff ℝ ∞ (fun x => fderiv ℝ f x a) :=
  (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem directional_fderiv (f : Space → V) (hf : ContDiff ℝ ∞ f) (a x b : Space) :
    fderiv ℝ (fun y => fderiv ℝ f y a) x b = fderiv ℝ (fderiv ℝ f) x b a := by
  rw [fderiv_clm_apply ((hf.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x)
    (differentiableAt_const _)]
  simp

theorem directional_fderiv_bound (f : Space → V) (hf : ContDiff ℝ ∞ f)
    (C₂ : ℝ) (h₂ : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ C₂) (a x : Space) :
    ‖fderiv ℝ (fun y => fderiv ℝ f y a) x‖ ≤ C₂*‖a‖ := by
  have hC₂ : 0 ≤ C₂ := (norm_nonneg (fderiv ℝ (fderiv ℝ f) x)).trans (h₂ x)
  apply opNorm_le_bound _ (mul_nonneg hC₂ (norm_nonneg a))
  intro b
  rw [directional_fderiv f hf a x b]
  calc
    _ ≤ ‖fderiv ℝ (fderiv ℝ f) x b‖*‖a‖ := le_opNorm _ _
    _ ≤ (C₂*‖b‖)*‖a‖ := by
      gcongr
      exact (le_opNorm _ _).trans (mul_le_mul_of_nonneg_right (h₂ x) (norm_nonneg b))
    _ = _ := by ring

/-- Both spatial derivatives are transferred to the actual Gaussian kernel. -/
theorem average_second_identity {t : ℝ} (ht : 0 < t)
    (f : Space → V) (hf : ContDiff ℝ ∞ f) (C₀ C₁ C₂ : ℝ)
    (h₀ : ∀ x, ‖f x‖ ≤ C₀) (h₁ : ∀ x, ‖fderiv ℝ f x‖ ≤ C₁)
    (h₂ : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ C₂) (a b x : Space) :
    average t (fun z => fderiv ℝ (fun y => fderiv ℝ f y b) z a) x =
      ∫ y : Space, secondKernel t a b y • f (x+y) := by
  have hdir (y : Space) : ‖fderiv ℝ f y b‖ ≤ C₁*‖b‖ :=
    (le_opNorm _ _).trans (mul_le_mul_of_nonneg_right (h₁ y) (norm_nonneg b))
  rw [average_first_identity ht _ (directional_smooth f hf b) (C₁*‖b‖) (C₂*‖b‖)
    hdir (directional_fderiv_bound f hf C₂ h₂ b) a x]
  have hi : Integrable (fun y : Space => fderiv ℝ (firstKernel t a) y b) := by
    simpa only [firstKernel_fderiv] using secondKernel_integrable ht a b
  have h := integration_by_parts (firstKernel t a) ((firstKernel_smooth t a).differentiable (by
      simp))
    (firstKernel_integrable ht a) b hi f hf C₀ C₁ h₀ h₁ x
  simp only [firstKernel_fderiv] at h
  rw [h, neg_neg]

/-- The genuine smoothed second derivative has a 1/t bound controlled
only by the size of the original field. Bounds on its derivatives are
used to justify integration by parts and do not enter the estimate. -/
theorem average_second_bound {t : ℝ} (ht : 0 < t)
    (f : Space → V) (hf : ContDiff ℝ ∞ f) (C₀ C₁ C₂ : ℝ)
    (h₀ : ∀ x, ‖f x‖ ≤ C₀) (h₁ : ∀ x, ‖fderiv ℝ f x‖ ≤ C₁)
    (h₂ : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ C₂) (a b x : Space) :
    ‖average t (fun z => fderiv ℝ (fun y => fderiv ℝ f y b) z a) x‖ ≤
      (10*(2:ℝ)^((3:ℝ)/2))*t⁻¹*‖a‖*‖b‖*C₀ := by
  rw [average_second_identity ht f hf C₀ C₁ C₂ h₀ h₁ h₂ a b x]
  have hC₀ : 0 ≤ C₀ := (norm_nonneg _).trans (h₀ x)
  have hb := norm_integral_le_of_norm_le ((secondKernel_integrable ht a b).norm.mul_const C₀)
    (f := fun y : Space => secondKernel t a b y • f (x+y))
    (Eventually.of_forall (fun y => by
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (h₀ (x+y)) (norm_nonneg _)))
  rw [integral_mul_const] at hb
  exact hb.trans (mul_le_mul_of_nonneg_right (secondKernel_L1_bound ht a b) hC₀)

end EulerWholeSpaceGaussian
