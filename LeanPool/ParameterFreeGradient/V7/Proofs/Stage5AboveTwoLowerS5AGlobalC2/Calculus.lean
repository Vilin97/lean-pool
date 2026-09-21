/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/

import LeanPool.ParameterFreeGradient.V7.Proofs.Stage5AboveTwoLowerS5AGlobalC2.Continuity

/-!
The power smoothing kernel is twice continuously Fréchet differentiable globally.
-/

namespace V7.Stage5AboveTwoLower.S5AGlobalC2

open S5ARepair

/-- The derivative of the kernel's Fréchet derivative, obtained from its Hessian. -/
noncomputable def kernelFDerivDerivative (r theta : ℝ) (x : Point d) :
    Point d →L[ℝ] (Point d →L[ℝ] ℝ) :=
  (ContinuousLinearMap.compL ℝ (Point d) (Point d) (Point d →L[ℝ] ℝ))
    (pairingCLMCLM (d := d)) (kernelHessian r theta x)

lemma continuous_kernelFDerivDerivative {r theta : ℝ}
    (hr : 2 < r) (htheta : 1 < theta) (htr : 2 * theta < r) {d : ℕ} :
    Continuous (kernelFDerivDerivative (d := d) r theta) := by
  exact ((ContinuousLinearMap.compL ℝ (Point d) (Point d) (Point d →L[ℝ] ℝ))
    (pairingCLMCLM (d := d))).continuous.comp
      (continuous_kernelHessian hr htheta htr)

lemma hasFDerivAt_kernelFDeriv {r theta : ℝ}
    (hr : 2 < r) (htheta : 1 < theta) (htr : 2 * theta < r) {d : ℕ}
    (x : Point d) :
    HasFDerivAt (kernelFDeriv r theta)
      (kernelFDerivDerivative r theta x) x := by
  have hc := (pairingCLMCLM (d := d)).hasFDerivAt.comp x
    (hasFDerivAt_kernelGradientVector hr htheta htr x)
  rw [show kernelFDeriv (d := d) r theta =
      (pairingCLMCLM (d := d)) ∘ kernelGradientVector r theta by
    funext y
    exact pairingCLMCLM_apply _]
  change HasFDerivAt ((pairingCLMCLM (d := d)) ∘ kernelGradientVector r theta)
    ((pairingCLMCLM (d := d)).comp (kernelHessian r theta x)) x
  exact hc

theorem contDiff_one_kernelFDeriv {r theta : ℝ}
    (hr : 2 < r) (htheta : 1 < theta) (htr : 2 * theta < r) {d : ℕ} :
    ContDiff ℝ 1 (kernelFDeriv (d := d) r theta) := by
  apply contDiff_one_iff_hasFDerivAt.mpr
  exact ⟨kernelFDerivDerivative r theta,
    continuous_kernelFDerivDerivative hr htheta htr,
    hasFDerivAt_kernelFDeriv hr htheta htr⟩

/-- Genuine global `C²` closure for the fixed scalar smoothing kernel. -/
theorem contDiff_two_lowerKernelPhi {r theta : ℝ}
    (hr : 2 < r) (htheta : 1 < theta) (htr : 2 * theta < r) {d : ℕ} :
    ContDiff ℝ 2 (lowerKernelPhi (d := d) r theta) := by
  have hsucc : ContDiff ℝ (1 + 1 : ℕ) (lowerKernelPhi (d := d) r theta) := by
    apply contDiff_succ_iff_hasFDerivAt.mpr
    exact ⟨kernelFDeriv r theta,
      contDiff_one_kernelFDeriv hr htheta htr,
      hasFDerivAt_lowerKernelPhi hr htheta htr⟩
  norm_num at hsucc ⊢
  exact hsucc

end V7.Stage5AboveTwoLower.S5AGlobalC2
