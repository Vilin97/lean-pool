/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/

import LeanPool.ParameterFreeGradient.V7.Proofs.Stage5AboveTwoLower.Parameters
import LeanPool.ParameterFreeGradient.O3.GeometryExperimental

/-!
Elementary positivity, normalization, and norm-power identities for the smoothing kernel.
-/

namespace V7.Stage5AboveTwoLower

lemma lowerKernelPhi_eq_norm_power {r0 theta : ℝ} (hr0 : r0 ≠ 0)
    (x : Point d) :
    lowerKernelPhi r0 theta x =
      2 * (lpNorm r0 x) ^ (2 * theta) := by
  change 2 * (O3.lpPower r0 x) ^ (2 * theta / r0) = _
  rw [← O3.Experimental.lpNorm_rpow_eq_lpPower hr0]
  rw [← Real.rpow_mul (O3.lpNorm_nonneg r0 x)]
  congr 2
  field_simp

lemma lowerKernelPhi_nonneg {r0 theta : ℝ} (x : Point d) :
    0 ≤ lowerKernelPhi r0 theta x := by
  unfold lowerKernelPhi
  positivity

lemma lowerKernelPhi_zero {r0 theta : ℝ} (hr0 : 0 < r0) (htheta : 0 < theta) :
    lowerKernelPhi (d := d) r0 theta 0 = 0 := by
  rw [lowerKernelPhi_eq_norm_power (by linarith)]
  rw [show lpNorm r0 (0 : Point d) = 0 by
    simpa only [lpNorm] using O3.lpNorm_zero (d := d) hr0]
  rw [Real.zero_rpow (by positivity : 2 * theta ≠ 0)]
  ring

lemma lowerKernelPhi_strict_of_one_lt_norm_power {r0 theta : ℝ}
    (hr0 : 0 < r0) (x : Point d)
    (hx : 1 < (lpNorm r0 x) ^ (2 * theta)) :
    1 < lowerKernelPhi r0 theta x := by
  rw [lowerKernelPhi_eq_norm_power (by linarith)]
  nlinarith

end V7.Stage5AboveTwoLower
