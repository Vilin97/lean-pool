/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/

import LeanPool.ParameterFreeGradient.V7.Proofs.Stage5AboveTwoLowerS5AHessianContinuity.HessianContinuity
import LeanPool.ParameterFreeGradient.O3.Stage2RouteD

open scoped BigOperators
open Asymptotics

namespace V7.Stage5AboveTwoLower.S5AGlobalC2

open S5ARepair S5AFinalRepair S5AHessianContinuity

lemma kernelGradientVector_zero {r theta : ℝ}
    (_hr : 2 < r) (htheta : 1 < theta) (htr : 2 * theta < r) {d : ℕ} :
    kernelGradientVector r theta (0 : Point d) = 0 := by
  have he : 2 * theta / r - 1 ≠ 0 := by
    have hr0 : 0 < r := by linarith
    rw [ne_eq, sub_eq_zero, div_eq_one_iff_eq (ne_of_gt hr0)]
    linarith
  simp [kernelGradientVector, O3.lpPower_zero (by linarith : r ≠ 0),
    Real.zero_rpow he]

lemma kernelFDeriv_zero {r theta : ℝ}
    (hr : 2 < r) (htheta : 1 < theta) (htr : 2 * theta < r) {d : ℕ} :
    kernelFDeriv r theta (0 : Point d) = 0 := by
  rw [kernelFDeriv, kernelGradientVector_zero hr htheta htr]
  ext h
  simp [pairingCLM_apply, O3.pairing]

/-- The scalar kernel itself has the exact current derivative at the origin. -/
theorem hasFDerivAt_lowerKernelPhi_zero {r theta : ℝ}
    (hr : 2 < r) (htheta : 1 < theta) (htr : 2 * theta < r) {d : ℕ} :
    HasFDerivAt (lowerKernelPhi (d := d) r theta)
      (kernelFDeriv r theta 0) 0 := by
  rw [kernelFDeriv_zero hr htheta htr]
  have ha : 1 < 2 * theta := by linarith
  have hbig :
      (lowerKernelPhi (d := d) r theta) =O[nhds 0]
        (fun x : Point d ↦ ‖x‖ ^ (2 * theta)) :=
    IsBigO.of_bound (2 * lpAmbientConstant r d ^ (2 * theta))
      (Filter.Eventually.of_forall fun x : Point d ↦ by
        have hlp := lpNorm_le_ambientConstant (d := d)
          (by linarith : 1 ≤ r) x
        have hrpow := Real.rpow_le_rpow (O3.lpNorm_nonneg r x) hlp
          (by linarith : 0 ≤ 2 * theta)
        rw [Real.norm_eq_abs,
          abs_of_nonneg (Stage5AboveTwoLower.lowerKernelPhi_nonneg x),
          Stage5AboveTwoLower.lowerKernelPhi_eq_norm_power (by linarith : r ≠ 0)]
        calc
          2 * O3.lpNorm r x ^ (2 * theta) ≤
              2 * (lpAmbientConstant r d * ‖x‖) ^ (2 * theta) := by gcongr
          _ = (2 * lpAmbientConstant r d ^ (2 * theta)) *
              ‖x‖ ^ (2 * theta) := by
            rw [Real.mul_rpow (lpAmbientConstant_nonneg r d) (norm_nonneg x)]
            ring
          _ = (2 * lpAmbientConstant r d ^ (2 * theta)) *
              ‖‖x‖ ^ (2 * theta)‖ := by
            rw [Real.norm_rpow_of_nonneg (norm_nonneg x), norm_norm])
  have hlittle :
      (lowerKernelPhi (d := d) r theta) =o[nhds 0]
        (fun x : Point d ↦ x) :=
    hbig.trans_isLittleO (norm_rpow_isLittleO_id (E := Point d) ha)
  apply HasFDerivAt.of_isLittleO
  simpa [Stage5AboveTwoLower.lowerKernelPhi_zero (d := d)
    (by linarith : 0 < r) (by linarith : 0 < theta)] using hlittle

/-- Exact first derivative of the frozen scalar kernel at every point. -/
theorem hasFDerivAt_lowerKernelPhi {r theta : ℝ}
    (hr : 2 < r) (htheta : 1 < theta) (htr : 2 * theta < r) {d : ℕ}
    (x : Point d) :
    HasFDerivAt (lowerKernelPhi r theta) (kernelFDeriv r theta x) x := by
  by_cases hx : x = 0
  · subst x
    exact hasFDerivAt_lowerKernelPhi_zero hr htheta htr
  · exact hasFDerivAt_lowerKernelPhi_of_ne_zero (by linarith : 1 < r) x hx

/-- Literal coordinate-gradient interface required by the frozen kernel data. -/
theorem lowerKernelPhi_coordinateGradient {r theta : ℝ}
    (hr : 2 < r) (htheta : 1 < theta) (htr : 2 * theta < r) {d : ℕ} :
    O3.IsCoordinateGradient (lowerKernelPhi (d := d) r theta)
      (kernelGradientVector r theta) := by
  intro x
  have hd := hasFDerivAt_lowerKernelPhi hr htheta htr x
  refine ⟨hd.differentiableAt, fun h ↦ ?_⟩
  rw [hd.fderiv]
  exact pairingCLM_apply _ _

/-- Exact derivative of the current gradient by the current Hessian globally. -/
theorem hasFDerivAt_kernelGradientVector {r theta : ℝ}
    (hr : 2 < r) (htheta : 1 < theta) (htr : 2 * theta < r) {d : ℕ}
    (x : Point d) :
    HasFDerivAt (kernelGradientVector r theta)
      (kernelHessian r theta x) x := by
  by_cases hx : x = 0
  · subst x
    exact hasFDerivAt_kernelGradientVector_zero hr htheta htr
  · exact hasFDerivAt_kernelGradientVector_of_ne_zero hr x hx

end V7.Stage5AboveTwoLower.S5AGlobalC2
