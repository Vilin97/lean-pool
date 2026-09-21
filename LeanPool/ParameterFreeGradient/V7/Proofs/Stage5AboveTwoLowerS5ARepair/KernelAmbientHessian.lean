/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/

import LeanPool.ParameterFreeGradient.V7.Proofs.Stage5AboveTwoLowerS5ARepair.KernelAmbientNonzero

namespace V7.Stage5AboveTwoLower.S5ARepair

noncomputable def kernelHessianCoord (r theta : ℝ) (x : Point d) (i : Fin d) :
    Point d →L[ℝ] ℝ :=
  (4 * theta * O3.Experimental.scalarJ r (x i)) •
      ((2 * theta / r - 1) *
        (O3.lpPower r x) ^ (2 * theta / r - 2)) • lpPowerFDeriv r x +
    (4 * theta * (O3.lpPower r x) ^ (2 * theta / r - 1)) •
      ((r - 1) * |x i| ^ (r - 2)) •
        (ContinuousLinearMap.proj i : Point d →L[ℝ] ℝ)

noncomputable def kernelHessian (r theta : ℝ) (x : Point d) :
    Point d →L[ℝ] Point d :=
  ContinuousLinearMap.pi (fun i ↦ kernelHessianCoord r theta x i)

@[simp] lemma kernelHessian_apply (r theta : ℝ) (x h : Point d)
    (i : Fin d) :
    kernelHessian r theta x h i = kernelHessianCoord r theta x i h := by
  simp [kernelHessian]

lemma hasFDerivAt_kernelGradientVector_of_ne_zero {r theta : ℝ}
    (hr : 2 < r) (x : Point d) (hx : x ≠ 0) :
    HasFDerivAt (kernelGradientVector r theta)
      (kernelHessian r theta x) x := by
  have hS : O3.lpPower r x ≠ 0 := (O3.lpPower_pos_of_ne_zero hx).ne'
  have hpow := (hasFDerivAt_lpPower (by linarith : 1 < r) x).rpow_const
    (Or.inl hS) (p := 2 * theta / r - 1)
  change HasFDerivAt
    (fun y : Point d ↦
      (4 * theta * (O3.lpPower r y) ^ (2 * theta / r - 1)) •
        O3.powerDualityMap r y)
    (ContinuousLinearMap.pi (fun i ↦ kernelHessianCoord r theta x i)) x
  rw [hasFDerivAt_pi]
  intro i
  have hscalar : HasFDerivAt
      (fun y : Point d ↦ O3.Experimental.scalarJ r (y i))
      (((r - 1) * |x i| ^ (r - 2)) •
        (ContinuousLinearMap.proj i : Point d →L[ℝ] ℝ)) x := by
    have hs := (O3.Stage2RouteA.hasDerivAt_scalarJ_above_two hr (u := x i)).hasFDerivAt
    have hc := hs.comp x
      (ContinuousLinearMap.proj i : Point d →L[ℝ] ℝ).hasFDerivAt
    apply hc.congr_fderiv
    ext h
    simp [ContinuousLinearMap.toSpanSingleton_apply]
    ring
  have hprod := hpow.mul hscalar
  have hscaled := hprod.const_mul (4 * theta)
  change HasFDerivAt
    (fun y : Point d ↦
      (4 * theta * (O3.lpPower r y) ^ (2 * theta / r - 1)) *
        O3.Experimental.scalarJ r (y i))
    (ContinuousLinearMap.proj i ∘L kernelHessian r theta x) x
  have hfun :
      (fun y : Point d ↦
        (4 * theta * O3.lpPower r y ^ (2 * theta / r - 1)) *
          O3.Experimental.scalarJ r (y i)) =
      fun y : Point d ↦ 4 * theta *
        (((fun z : Point d ↦ O3.lpPower r z ^ (2 * theta / r - 1)) *
          fun z : Point d ↦ O3.Experimental.scalarJ r (z i)) y) := by
    funext y
    change (4 * theta * O3.lpPower r y ^ (2 * theta / r - 1)) *
      O3.Experimental.scalarJ r (y i) =
      4 * theta * (O3.lpPower r y ^ (2 * theta / r - 1) *
        O3.Experimental.scalarJ r (y i))
    ring
  rw [hfun]
  apply hscaled.congr_fderiv
  ext h
  simp [kernelHessian, kernelHessianCoord]
  ring

lemma kernelGradientVector_fderiv_of_ne_zero {r theta : ℝ}
    (hr : 2 < r) (x : Point d) (hx : x ≠ 0) :
    fderiv ℝ (kernelGradientVector r theta) x = kernelHessian r theta x :=
  (hasFDerivAt_kernelGradientVector_of_ne_zero hr x hx).fderiv

end V7.Stage5AboveTwoLower.S5ARepair
