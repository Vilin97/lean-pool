/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/
module


public import LeanPool.ParameterFreeGradient.V7.Proofs.Stage5AboveTwoLowerS5AGlobalC2.Core

/-!
Continuity of the assembled kernel Hessian at all points.
-/

@[expose] public section

open scoped BigOperators

namespace V7.Stage5AboveTwoLower.S5AGlobalC2

open S5ARepair S5AFinalRepair S5AHessianContinuity

/-- The linear map sending a vector to its continuous pairing functional. -/
noncomputable def pairingCLMLinear {d : ℕ} :
    Point d →ₗ[ℝ] (Point d →L[ℝ] ℝ) where
  toFun := pairingCLM
  map_add' g k := by
    ext h
    simp only [add_apply, pairingCLM_apply, O3.pairing, Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  map_smul' c g := by
    ext h
    simp only [smul_apply, pairingCLM_apply, O3.pairing, Pi.smul_apply,
      smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

/-- The continuous linear map sending a vector to its pairing functional. -/
noncomputable def pairingCLMCLM {d : ℕ} :
    Point d →L[ℝ] (Point d →L[ℝ] ℝ) :=
  LinearMap.toContinuousLinearMap (pairingCLMLinear (d := d))

@[simp] lemma pairingCLMCLM_apply {d : ℕ} (g : Point d) :
    pairingCLMCLM g = pairingCLM g := rfl

lemma continuous_powerDualityMap {r : ℝ} (hr : 2 < r) {d : ℕ} :
    Continuous (O3.powerDualityMap (d := d) r) := by
  apply continuous_pi
  intro i
  change Continuous (fun x : Point d ↦ O3.Experimental.scalarJ r (x i))
  exact (O3.Experimental.continuous_scalarJ hr).comp (continuous_apply i)

lemma continuous_lpPowerFDeriv {r : ℝ} (hr : 2 < r) {d : ℕ} :
    Continuous (lpPowerFDeriv (d := d) r) := by
  have hdual : Continuous
      (fun x : Point d ↦ pairingCLMCLM (O3.powerDualityMap r x)) :=
    (pairingCLMCLM (d := d)).continuous.comp (continuous_powerDualityMap hr)
  have hscaled := hdual.const_smul r
  change Continuous (r • fun x : Point d ↦ pairingCLM (O3.powerDualityMap r x))
  exact hscaled

lemma continuous_lpPower {r : ℝ} (hr : 2 < r) {d : ℕ} :
    Continuous (O3.lpPower (d := d) r) := by
  have hd : Differentiable ℝ (O3.lpPower (d := d) r) :=
    fun x ↦ (hasFDerivAt_lpPower (by linarith : 1 < r) x).differentiableAt
  exact hd.continuous

lemma continuousAt_kernelHessianCoord_of_ne_zero {r theta : ℝ}
    (hr : 2 < r) {d : ℕ} (x : Point d) (hx : x ≠ 0) (i : Fin d) :
    ContinuousAt (fun y ↦ kernelHessianCoord r theta y i) x := by
  have hS : O3.lpPower r x ≠ 0 := (O3.lpPower_pos_of_ne_zero hx).ne'
  have hpower2 : ContinuousAt
      (fun y : Point d ↦ O3.lpPower r y ^ (2 * theta / r - 2)) x :=
    (continuous_lpPower hr).continuousAt.rpow_const (Or.inl hS)
  have hpower1 : ContinuousAt
      (fun y : Point d ↦ O3.lpPower r y ^ (2 * theta / r - 1)) x :=
    (continuous_lpPower hr).continuousAt.rpow_const (Or.inl hS)
  have hscalar : ContinuousAt
      (fun y : Point d ↦ O3.Experimental.scalarJ r (y i)) x :=
    ((O3.Experimental.continuous_scalarJ hr).comp (continuous_apply i)).continuousAt
  have hcoord : ContinuousAt (fun y : Point d ↦ |y i| ^ (r - 2)) x :=
    ((continuous_apply i).abs.rpow_const
      (fun _ ↦ Or.inr (by linarith : 0 ≤ r - 2))).continuousAt
  have hfd : ContinuousAt (lpPowerFDeriv (d := d) r) x :=
    (continuous_lpPowerFDeriv hr).continuousAt
  have hfirst : ContinuousAt (fun y : Point d ↦
      (4 * theta * O3.Experimental.scalarJ r (y i)) •
        ((2 * theta / r - 1) * O3.lpPower r y ^ (2 * theta / r - 2)) •
          lpPowerFDeriv r y) x := by
    exact (continuousAt_const.mul hscalar).smul
      ((continuousAt_const.mul hpower2).smul hfd)
  have hsecond : ContinuousAt (fun y : Point d ↦
      (4 * theta * O3.lpPower r y ^ (2 * theta / r - 1)) •
        ((r - 1) * |y i| ^ (r - 2)) •
          (ContinuousLinearMap.proj i : Point d →L[ℝ] ℝ)) x := by
    exact (continuousAt_const.mul hpower1).smul
      ((continuousAt_const.mul hcoord).smul continuousAt_const)
  change ContinuousAt
    ((fun y : Point d ↦
      (4 * theta * O3.Experimental.scalarJ r (y i)) •
        ((2 * theta / r - 1) * O3.lpPower r y ^ (2 * theta / r - 2)) •
          lpPowerFDeriv r y) +
    (fun y : Point d ↦
      (4 * theta * O3.lpPower r y ^ (2 * theta / r - 1)) •
        ((r - 1) * |y i| ^ (r - 2)) •
          (ContinuousLinearMap.proj i : Point d →L[ℝ] ℝ))) x
  exact hfirst.add hsecond

/-- The linear assembly of coordinate functionals into a vector-valued continuous linear map. -/
noncomputable def assemblePiLinear {d : ℕ} :
    ((i : Fin d) → Point d →L[ℝ] ℝ) →ₗ[ℝ] (Point d →L[ℝ] Point d) where
  toFun := ContinuousLinearMap.pi
  map_add' f g := by
    ext h i
    simp
  map_smul' c f := by
    ext h i
    simp

/-- The continuous linear assembly of coordinate functionals into a vector-valued derivative. -/
noncomputable def assemblePiCLM {d : ℕ} :
    ((i : Fin d) → Point d →L[ℝ] ℝ) →L[ℝ] (Point d →L[ℝ] Point d) :=
  LinearMap.toContinuousLinearMap (assemblePiLinear (d := d))

@[simp] lemma assemblePiCLM_apply {d : ℕ}
    (f : (i : Fin d) → Point d →L[ℝ] ℝ) :
    assemblePiCLM f = ContinuousLinearMap.pi f := rfl

lemma continuousAt_kernelHessian_of_ne_zero {r theta : ℝ}
    (hr : 2 < r) {d : ℕ} (x : Point d) (hx : x ≠ 0) :
    ContinuousAt (kernelHessian (d := d) r theta) x := by
  have hcoords : ContinuousAt
      (fun y : Point d ↦ fun i ↦ kernelHessianCoord r theta y i) x :=
    continuousAt_pi.mpr fun i ↦ continuousAt_kernelHessianCoord_of_ne_zero hr x hx i
  have h := (assemblePiCLM (d := d)).continuous.continuousAt.comp' hcoords
  change ContinuousAt
    (fun y : Point d ↦ ContinuousLinearMap.pi
      (fun i ↦ kernelHessianCoord r theta y i)) x
  exact h

/-- The exact concrete Hessian is globally continuous in CLM operator norm. -/
theorem continuous_kernelHessian {r theta : ℝ}
    (hr : 2 < r) (htheta : 1 < theta) (htr : 2 * theta < r) {d : ℕ} :
    Continuous (kernelHessian (d := d) r theta) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x = 0
  · subst x
    exact continuousAt_kernelHessian_zero hr htheta htr
  · exact continuousAt_kernelHessian_of_ne_zero hr x hx

end V7.Stage5AboveTwoLower.S5AGlobalC2
