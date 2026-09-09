/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderPhysicalTensor
import LeanPool.NavierStokesAndEuler.Euler.CylinderPhysicalTensorLp
import LeanPool.NavierStokesAndEuler.Euler.Foundations.MollifierUniform
import LeanPool.NavierStokesAndEuler.ForMathlib.SmoothnessOrder

/-! The physical tensor estimate controls differences of actual L²
representatives, which supplies time continuity without a domination premise. -/

@[expose] public section


noncomputable section

namespace EulerCylinderPhysicalTensor

open Set MeasureTheory EulerLiftedGradientSpace EulerCylinderSobolev
  EulerGraphPressurePotential EulerMetricTransport
open scoped ContDiff

variable (P k : ℝ) (m : Vector3)

theorem physicalTensor_norm_le_of_ae (f : LiftDomain P → Vector3)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift P f x)) (n : ℕ)
    (u : (Fin n → Fin 4) → Lp Vector3 2 (volume : Measure Vector3))
    (hu : ∀ w, (u w : Vector3 → Vector3) =ᵐ[volume]
      fun x => iteratedFieldDerivative P w f (cylinderGraph P k m x))
    (v : Lp (Vector3 [×n]→L[ℝ] Vector3) 2 (volume : Measure Vector3))
    (hv : (v : Vector3 → (Vector3 [×n]→L[ℝ] Vector3)) =ᵐ[volume]
      iteratedFDeriv ℝ n (physicalField P k m f)) :
    ‖v‖ ≤ frequencyFactor k m^n * ∑ w, ‖u w‖ := by
  have he : v = physicalTensorLp P k m f hf n u hu :=
    Lp.ext (hv.trans (physicalTensorLp_ae P k m f hf n u hu).symm)
  rw [he]
  exact physicalTensorLp_norm_le P k m f hf n u hu

theorem physicalTensor_difference_norm_le (f g : LiftDomain P → Vector3)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift P f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift P g x)) (n : ℕ)
    (u v : (Fin n → Fin 4) → Lp Vector3 2 (volume : Measure Vector3))
    (hu : ∀ w, (u w : Vector3 → Vector3) =ᵐ[volume]
      fun x => iteratedFieldDerivative P w f (cylinderGraph P k m x))
    (hv : ∀ w, (v w : Vector3 → Vector3) =ᵐ[volume]
      fun x => iteratedFieldDerivative P w g (cylinderGraph P k m x))
    (F G : Lp (Vector3 [×n]→L[ℝ] Vector3) 2 (volume : Measure Vector3))
    (hF : (F : Vector3 → (Vector3 [×n]→L[ℝ] Vector3)) =ᵐ[volume]
      iteratedFDeriv ℝ n (physicalField P k m f))
    (hG : (G : Vector3 → (Vector3 [×n]→L[ℝ] Vector3)) =ᵐ[volume]
      iteratedFDeriv ℝ n (physicalField P k m g)) :
    ‖F-G‖ ≤ frequencyFactor k m^n * ∑ w, ‖u w-v w‖ := by
  refine physicalTensor_norm_le_of_ae P k m (fun x => f x-g x)
    (fun x => (hf x).sub (hg x)) n (fun w => u w-v w) ?_ (F-G) ?_
  · intro w
    filter_upwards [Lp.coeFn_sub (u w) (v w),hu w,hv w] with x hs hx hy
    exact hs.trans ((congrArg₂ (·-·) hx hy).trans
      (congrFun (EulerMollifierUniform.word_sub P w f g hf hg) (cylinderGraph P k m x)).symm)
  · filter_upwards [Lp.coeFn_sub F G,hF,hG] with x hs hx hy
    have hd := iteratedFDeriv_sub_apply (x := x)
      ((physicalField_contDiff P k m f hf).of_le (by simp : (n : ℕ∞ω) ≤ ∞)).contDiffAt
      ((physicalField_contDiff P k m g hg).of_le (by simp : (n : ℕ∞ω) ≤ ∞)).contDiffAt
    exact hs.trans ((congrArg₂ (·-·) hx hy).trans hd.symm)

end EulerCylinderPhysicalTensor
