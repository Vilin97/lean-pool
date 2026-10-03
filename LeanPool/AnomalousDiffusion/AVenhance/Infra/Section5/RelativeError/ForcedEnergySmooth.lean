/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.WeakUniqueness.WeakAlgebra
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Classical.PeriodicCalculus
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.IsPeriodicH1With

/-!
# Smooth periodic functions are periodic `H¹`

A `C¹` periodic function is in the periodic `H¹` class with its classical gradient.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open Homogenization

namespace AVenhance.Infra.Section5.RelativeError

open AVenhance.Infra.Parabolic.WeakUniqueness

/-- Coordinates of the classical gradient of a `C¹` function are continuous. -/
theorem spaceGrad_continuous_of_contDiff {f : Vec 2 → ℝ} (hf : ContDiff ℝ 1 f) (i : Fin 2) :
    Continuous (fun x => AVenhance.spaceGrad f x i) :=
  (hf.continuous_fderiv (by simp)).clm_apply continuous_const

/-- A `C¹` periodic function is periodic `H¹` with its classical gradient. -/
theorem isPeriodicH1With_of_contDiff {f : Vec 2 → ℝ} (hf : ContDiff ℝ 1 f)
    (hp : AVenhance.IsZ2Periodic f) :
    AVenhance.IsPeriodicH1With f (fun x => AVenhance.spaceGrad f x) := by
  refine ⟨hp, ?_, weak_continuous_memL2On hf.continuous, ?_, ?_⟩
  · intro n x
    funext i
    exact AVenhance.Infra.Classical.periodic_spaceGrad_component hp i n x
  · intro i
    exact weak_continuous_memL2On (spaceGrad_continuous_of_contDiff hf i)
  · intro i φ hφ hφc _
    have hφd : Differentiable ℝ φ := hφ.differentiable (by simp)
    have hfd : Differentiable ℝ f := hf.differentiable (by simp)
    have hφ' : Continuous (fun x => fderiv ℝ φ x (basisVec i)) :=
      ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const)
    have hφ'c : HasCompactSupport (fun x => fderiv ℝ φ x (basisVec i)) :=
      hφc.fderiv_apply (𝕜 := ℝ) (basisVec i)
    have hf' : Continuous (fun x => fderiv ℝ f x (basisVec i)) :=
      ((hf.continuous_fderiv (by simp)).clm_apply continuous_const)
    have h1 : Integrable (fun x => fderiv ℝ f x (basisVec i) * φ x) volume :=
      (hf'.mul hφ.continuous).integrable_of_hasCompactSupport hφc.mul_left
    have h2 : Integrable (fun x => f x * fderiv ℝ φ x (basisVec i)) volume :=
      (hf.continuous.mul hφ').integrable_of_hasCompactSupport hφ'c.mul_left
    have h3 : Integrable (fun x => f x * φ x) volume :=
      (hf.continuous.mul hφ.continuous).integrable_of_hasCompactSupport hφc.mul_left
    have := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume) (f := f) (g := φ)
      (v := basisVec i) h1 h2 h3 (fun x _ => hfd x) (fun x _ => hφd x)
    simpa [AVenhance.spaceGrad, setIntegral_univ] using this

end AVenhance.Infra.Section5.RelativeError

end
