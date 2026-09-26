/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/
module


public import LeanPool.ParameterFreeGradient.V7.Proofs.Stage5AboveTwoLowerS5ARepair.KernelLineCalculus

/-!
The ambient Fréchet derivative and coordinate gradient of the power kernel away from zero.
-/

@[expose] public section

open scoped BigOperators

namespace V7.Stage5AboveTwoLower.S5ARepair

/-- The continuous linear functional given by pairing with a fixed vector. -/
noncomputable def pairingCLM (g : Point d) : Point d →L[ℝ] ℝ :=
  ∑ i : Fin d, (g i) • ContinuousLinearMap.proj i

@[simp] lemma pairingCLM_apply (g h : Point d) :
    pairingCLM g h = O3.pairing g h := by
  simp [pairingCLM, O3.pairing]

/-- The Fréchet derivative formula for the sum of coordinate absolute powers. -/
noncomputable def lpPowerFDeriv (r : ℝ) (x : Point d) : Point d →L[ℝ] ℝ :=
  r • pairingCLM (O3.powerDualityMap r x)

lemma hasFDerivAt_lpPower {r : ℝ} (hr : 1 < r) (x : Point d) :
    HasFDerivAt (O3.lpPower r) (lpPowerFDeriv r x) x := by
  let coordDeriv (i : Fin d) : Point d →L[ℝ] ℝ :=
    (ContinuousLinearMap.toSpanSingleton ℝ
      (r * O3.Experimental.scalarJ r (x i))).comp
        (ContinuousLinearMap.proj i : Point d →L[ℝ] ℝ)
  have hcoord (i : Fin d) : HasFDerivAt
      (fun y : Point d ↦ |y i| ^ r) (coordDeriv i) x := by
    have hs := hasDerivAt_abs_rpow (x i) hr
    have hs' : HasDerivAt (fun u : ℝ ↦ |u| ^ r)
        (r * O3.Experimental.scalarJ r (x i)) (x i) := by
      apply hs.congr_deriv
      unfold O3.Experimental.scalarJ
      ring
    exact hs'.hasFDerivAt.comp x
      (ContinuousLinearMap.proj i : Point d →L[ℝ] ℝ).hasFDerivAt
  have hsum : HasFDerivAt (fun y : Point d ↦ ∑ i, |y i| ^ r)
      (∑ i : Fin d, coordDeriv i) x :=
    HasFDerivAt.fun_sum (fun i _ ↦ hcoord i)
  change HasFDerivAt (fun y : Point d ↦ ∑ i, |y i| ^ r)
    (lpPowerFDeriv r x) x
  apply hsum.congr_fderiv
  ext h
  simp only [O3.Experimental.scalarJ, sum_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul,
    lpPowerFDeriv, pairingCLM, O3.powerDualityMap, smul_apply, Finset.mul_sum, coordDeriv]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The explicit coordinate gradient of the power smoothing kernel. -/
noncomputable def kernelGradientVector (r theta : ℝ) (x : Point d) : Point d :=
  (4 * theta * (O3.lpPower r x) ^ (2 * theta / r - 1)) •
    O3.powerDualityMap r x

/-- The kernel gradient represented as a continuous linear functional. -/
noncomputable def kernelFDeriv (r theta : ℝ) (x : Point d) :
    Point d →L[ℝ] ℝ := pairingCLM (kernelGradientVector r theta x)

lemma hasFDerivAt_lowerKernelPhi_of_ne_zero {r theta : ℝ}
    (hr : 1 < r) (x : Point d) (hx : x ≠ 0) :
    HasFDerivAt (lowerKernelPhi r theta) (kernelFDeriv r theta x) x := by
  have hr0 : r ≠ 0 := by linarith
  have hS : O3.lpPower r x ≠ 0 := (O3.lpPower_pos_of_ne_zero hx).ne'
  have hp := (hasFDerivAt_lpPower hr x).rpow_const
    (Or.inl hS) (p := 2 * theta / r)
  have hscaled := hp.const_mul 2
  apply hscaled.congr_fderiv
  ext h
  simp only [kernelFDeriv, pairingCLM_apply, kernelGradientVector,
    O3.pairing, Pi.smul_apply, smul_eq_mul]
  rw [lpPowerFDeriv]
  simp only [smul_apply, smul_eq_mul, pairingCLM_apply]
  rw [O3.pairing]
  field_simp
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma lowerKernelPhi_coordinate_gradient_of_ne_zero {r theta : ℝ}
    (hr : 1 < r) (x : Point d) (hx : x ≠ 0) :
    fderiv ℝ (lowerKernelPhi r theta) x = kernelFDeriv r theta x :=
  (hasFDerivAt_lowerKernelPhi_of_ne_zero hr x hx).fderiv

end V7.Stage5AboveTwoLower.S5ARepair
