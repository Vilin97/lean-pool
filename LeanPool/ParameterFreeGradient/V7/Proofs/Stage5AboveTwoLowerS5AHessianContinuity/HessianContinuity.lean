/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/

import LeanPool.ParameterFreeGradient.V7.Proofs.Stage5AboveTwoLowerS5AFinalRepair.OriginFrechet

open scoped BigOperators

namespace V7.Stage5AboveTwoLower.S5AHessianContinuity

open S5ARepair S5AFinalRepair

lemma kernelHessian_zero {r theta : ℝ}
    (_hr : 2 < r) (htheta : 1 < theta) (htr : 2 * theta < r) {d : ℕ} :
    kernelHessian r theta (0 : Point d) = 0 := by
  have he1 : 2 * theta / r - 1 ≠ 0 := by
    have hr0 : 0 < r := by linarith
    rw [ne_eq, sub_eq_zero, div_eq_one_iff_eq (ne_of_gt hr0)]
    linarith
  have he2 : r - 2 ≠ 0 := by linarith
  ext h i
  simp [kernelHessian, kernelHessianCoord, lpPowerFDeriv,
    pairingCLM, O3.lpPower_zero (by linarith : r ≠ 0),
    O3.Experimental.scalarJ, Real.zero_rpow he1, Real.zero_rpow he2]

lemma lpPower_rpow_eq_lpNorm_rpow_of_ne_zero {r a : ℝ}
    (hr : r ≠ 0) {d : ℕ} (x : Point d) (hx : x ≠ 0) :
    O3.lpPower r x ^ a = O3.lpNorm r x ^ (r * a) := by
  have hn : 0 < O3.lpNorm r x := O3.lpNorm_pos_of_ne_zero hx
  have hp := O3.Stage2RouteB.lpNorm_rpow_eq_lpPower (p := r) hr x
  rw [← hp, ← Real.rpow_mul hn.le]

lemma abs_scalarJ_eq {r a : ℝ} (hr : 1 < r) :
    |O3.Experimental.scalarJ r a| = |a| ^ (r - 1) := by
  exact O3.Stage2RouteB.abs_powerDuality_coordinate (a := a) hr

lemma abs_lpPowerFDeriv_apply_le {r : ℝ} (hr : 2 < r) {d : ℕ}
    (x h : Point d) :
    |lpPowerFDeriv r x h| ≤
      r * O3.lpNorm r x ^ (r - 1) * lpAmbientConstant r d * ‖h‖ := by
  have hp : r.HolderConjugate (O3.conjugateExponent r) :=
    O3.holderConjugate_conjugateExponent (by linarith : 1 < r)
  have hholder := O3.abs_pairing_le_lpNorm_mul hp.symm
    (O3.powerDualityMap r x) h
  have hdual := lpNorm_powerDualityMap (d := d) (by linarith : 1 < r) x
  have hamb := lpNorm_le_ambientConstant (d := d) (by linarith : 1 ≤ r) h
  rw [lpPowerFDeriv, smul_apply, pairingCLM_apply]
  change |r * O3.pairing (O3.powerDualityMap r x) h| ≤ _
  rw [abs_mul, abs_of_pos (by linarith : 0 < r)]
  rw [hdual] at hholder
  have hpow0 : 0 ≤ O3.lpNorm r x ^ (r - 1) := Real.rpow_nonneg
    (O3.lpNorm_nonneg r x) _
  calc
    r * |O3.pairing (O3.powerDualityMap r x) h| ≤
        r * (O3.lpNorm r x ^ (r - 1) * O3.lpNorm r h) := by gcongr
    _ ≤ r * (O3.lpNorm r x ^ (r - 1) *
        (lpAmbientConstant r d * ‖h‖)) := by gcongr
    _ = r * O3.lpNorm r x ^ (r - 1) * lpAmbientConstant r d * ‖h‖ := by ring

noncomputable def hessianCoordConstant (r theta : ℝ) (d : ℕ) : ℝ :=
  4 * theta *
    (|2 * theta / r - 1| * r * lpAmbientConstant r d + (r - 1))

lemma hessianCoordConstant_nonneg {r theta : ℝ}
    (hr : 2 < r) (htheta : 1 < theta) {d : ℕ} :
    0 ≤ hessianCoordConstant r theta d := by
  unfold hessianCoordConstant
  refine mul_nonneg (mul_nonneg (by norm_num) (by linarith)) ?_
  exact add_nonneg
    (mul_nonneg (mul_nonneg (abs_nonneg _) (by linarith))
      (lpAmbientConstant_nonneg r d))
    (by linarith)

lemma abs_kernelHessianCoord_first_apply_le {r theta : ℝ}
    (hr : 2 < r) (htheta : 1 < theta) {d : ℕ}
    (x h : Point d) (hx : x ≠ 0) (i : Fin d) :
    |((4 * theta * O3.Experimental.scalarJ r (x i)) •
      ((2 * theta / r - 1) * O3.lpPower r x ^ (2 * theta / r - 2)) •
        lpPowerFDeriv r x) h| ≤
      (4 * theta * |2 * theta / r - 1| * r * lpAmbientConstant r d) *
        O3.lpNorm r x ^ (2 * theta - 2) * ‖h‖ := by
  have hn : 0 < O3.lpNorm r x := O3.lpNorm_pos_of_ne_zero hx
  have hxi := norm_apply_le_lpNorm (d := d) (by linarith : 1 ≤ r) x i
  have hcoord : |x i| ^ (r - 1) ≤ O3.lpNorm r x ^ (r - 1) :=
    Real.rpow_le_rpow (abs_nonneg _) hxi (by linarith)
  have hpower : O3.lpPower r x ^ (2 * theta / r - 2) =
      O3.lpNorm r x ^ (r * (2 * theta / r - 2)) :=
    lpPower_rpow_eq_lpNorm_rpow_of_ne_zero (by linarith : r ≠ 0) x hx
  have hderiv := abs_lpPowerFDeriv_apply_le hr x h
  simp only [smul_apply, smul_eq_mul, abs_mul]
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 4),
    abs_of_pos (by linarith : 0 < theta), abs_scalarJ_eq (by linarith : 1 < r),
    abs_of_nonneg (Real.rpow_nonneg (O3.lpPower_nonneg r x) _), hpower]
  rw [show
    4 * theta * |x i| ^ (r - 1) *
        (|2 * theta / r - 1| * O3.lpNorm r x ^ (r * (2 * theta / r - 2)) *
          |lpPowerFDeriv r x h|) =
      4 * theta * |x i| ^ (r - 1) * |2 * theta / r - 1| *
        O3.lpNorm r x ^ (r * (2 * theta / r - 2)) *
        |lpPowerFDeriv r x h| by ring]
  calc
    4 * theta * |x i| ^ (r - 1) * |2 * theta / r - 1| *
          O3.lpNorm r x ^ (r * (2 * theta / r - 2)) *
          |lpPowerFDeriv r x h| ≤
        4 * theta * O3.lpNorm r x ^ (r - 1) * |2 * theta / r - 1| *
          O3.lpNorm r x ^ (r * (2 * theta / r - 2)) *
          (r * O3.lpNorm r x ^ (r - 1) * lpAmbientConstant r d * ‖h‖) := by
            gcongr
    _ = (4 * theta * |2 * theta / r - 1| * r * lpAmbientConstant r d) *
          O3.lpNorm r x ^ (2 * theta - 2) * ‖h‖ := by
      rw [show
        4 * theta * O3.lpNorm r x ^ (r - 1) * |2 * theta / r - 1| *
            O3.lpNorm r x ^ (r * (2 * theta / r - 2)) *
            (r * O3.lpNorm r x ^ (r - 1) * lpAmbientConstant r d * ‖h‖) =
          (4 * theta * |2 * theta / r - 1| * r * lpAmbientConstant r d) *
            (O3.lpNorm r x ^ (r - 1) *
              O3.lpNorm r x ^ (r * (2 * theta / r - 2)) *
              O3.lpNorm r x ^ (r - 1)) * ‖h‖ by ring]
      rw [← Real.rpow_add hn, ← Real.rpow_add hn]
      congr 2
      field_simp [ne_of_gt (by linarith : 0 < r)]
      ring

lemma abs_kernelHessianCoord_second_apply_le {r theta : ℝ}
    (hr : 2 < r) (htheta : 1 < theta) {d : ℕ}
    (x h : Point d) (hx : x ≠ 0) (i : Fin d) :
    |((4 * theta * O3.lpPower r x ^ (2 * theta / r - 1)) •
      ((r - 1) * |x i| ^ (r - 2)) •
        (ContinuousLinearMap.proj i : Point d →L[ℝ] ℝ)) h| ≤
      (4 * theta * (r - 1)) * O3.lpNorm r x ^ (2 * theta - 2) * ‖h‖ := by
  have hn : 0 < O3.lpNorm r x := O3.lpNorm_pos_of_ne_zero hx
  have hxi := norm_apply_le_lpNorm (d := d) (by linarith : 1 ≤ r) x i
  have hcoord : |x i| ^ (r - 2) ≤ O3.lpNorm r x ^ (r - 2) :=
    Real.rpow_le_rpow (abs_nonneg _) hxi (by linarith)
  have hpower : O3.lpPower r x ^ (2 * theta / r - 1) =
      O3.lpNorm r x ^ (r * (2 * theta / r - 1)) :=
    lpPower_rpow_eq_lpNorm_rpow_of_ne_zero (by linarith : r ≠ 0) x hx
  have hhi : |h i| ≤ ‖h‖ := by
    simpa [Real.norm_eq_abs] using norm_le_pi_norm h i
  have hcoef0 : 0 ≤ 4 * theta * (r - 1) :=
    mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (by linarith)
  have hpow10 : 0 ≤ O3.lpNorm r x ^ (r * (2 * theta / r - 1)) :=
    Real.rpow_nonneg (O3.lpNorm_nonneg r x) _
  have hpow20 : 0 ≤ O3.lpNorm r x ^ (r - 2) :=
    Real.rpow_nonneg (O3.lpNorm_nonneg r x) _
  simp only [smul_apply, smul_eq_mul, ContinuousLinearMap.proj_apply,
    abs_mul]
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 4),
    abs_of_pos (by linarith : 0 < theta),
    abs_of_nonneg (Real.rpow_nonneg (O3.lpPower_nonneg r x) _), hpower,
    abs_of_pos (by linarith : 0 < r - 1),
    abs_of_nonneg (Real.rpow_nonneg (abs_nonneg (x i)) _)]
  rw [show
    4 * theta * O3.lpNorm r x ^ (r * (2 * theta / r - 1)) *
        ((r - 1) * |x i| ^ (r - 2) * |h i|) =
      4 * theta * (r - 1) * O3.lpNorm r x ^ (r * (2 * theta / r - 1)) *
        |x i| ^ (r - 2) * |h i| by ring]
  calc
    4 * theta * (r - 1) * O3.lpNorm r x ^ (r * (2 * theta / r - 1)) *
          |x i| ^ (r - 2) * |h i| ≤
        4 * theta * (r - 1) * O3.lpNorm r x ^ (r * (2 * theta / r - 1)) *
          O3.lpNorm r x ^ (r - 2) * ‖h‖ := by gcongr
    _ = (4 * theta * (r - 1)) * O3.lpNorm r x ^ (2 * theta - 2) * ‖h‖ := by
      rw [show
        4 * theta * (r - 1) * O3.lpNorm r x ^ (r * (2 * theta / r - 1)) *
            O3.lpNorm r x ^ (r - 2) * ‖h‖ =
          (4 * theta * (r - 1)) *
            (O3.lpNorm r x ^ (r * (2 * theta / r - 1)) *
              O3.lpNorm r x ^ (r - 2)) * ‖h‖ by ring]
      rw [← Real.rpow_add hn]
      congr 2
      field_simp [ne_of_gt (by linarith : 0 < r)]
      ring

lemma abs_kernelHessianCoord_apply_le {r theta : ℝ}
    (hr : 2 < r) (htheta : 1 < theta) {d : ℕ}
    (x h : Point d) (hx : x ≠ 0) (i : Fin d) :
    |kernelHessianCoord r theta x i h| ≤
      hessianCoordConstant r theta d * O3.lpNorm r x ^ (2 * theta - 2) * ‖h‖ := by
  have hfirst := abs_kernelHessianCoord_first_apply_le hr htheta x h hx i
  have hsecond := abs_kernelHessianCoord_second_apply_le hr htheta x h hx i
  rw [kernelHessianCoord, add_apply]
  calc
    |_ + _| ≤
        |((4 * theta * O3.Experimental.scalarJ r (x i)) •
          ((2 * theta / r - 1) * O3.lpPower r x ^ (2 * theta / r - 2)) •
            lpPowerFDeriv r x) h| +
        |((4 * theta * O3.lpPower r x ^ (2 * theta / r - 1)) •
          ((r - 1) * |x i| ^ (r - 2)) •
            (ContinuousLinearMap.proj i : Point d →L[ℝ] ℝ)) h| := abs_add_le _ _
    _ ≤ (4 * theta * |2 * theta / r - 1| * r * lpAmbientConstant r d) *
          O3.lpNorm r x ^ (2 * theta - 2) * ‖h‖ +
        (4 * theta * (r - 1)) * O3.lpNorm r x ^ (2 * theta - 2) * ‖h‖ :=
      add_le_add hfirst hsecond
    _ = hessianCoordConstant r theta d *
          O3.lpNorm r x ^ (2 * theta - 2) * ‖h‖ := by
      unfold hessianCoordConstant
      ring

lemma norm_kernelHessian_le_lpNorm_rpow {r theta : ℝ}
    (hr : 2 < r) (htheta : 1 < theta) (htr : 2 * theta < r) {d : ℕ}
    (x : Point d) :
    ‖kernelHessian r theta x‖ ≤
      hessianCoordConstant r theta d * O3.lpNorm r x ^ (2 * theta - 2) := by
  by_cases hx : x = 0
  · subst x
    rw [kernelHessian_zero hr htheta htr]
    simp [O3.lpNorm_zero (by linarith : 0 < r),
      Real.zero_rpow (by linarith : 2 * theta - 2 ≠ 0)]
  · apply ContinuousLinearMap.opNorm_le_bound _
      (mul_nonneg (hessianCoordConstant_nonneg hr htheta)
        (Real.rpow_nonneg (O3.lpNorm_nonneg r x) _))
    intro h
    apply (pi_norm_le_iff_of_nonneg
      (mul_nonneg
        (mul_nonneg (hessianCoordConstant_nonneg hr htheta)
          (Real.rpow_nonneg (O3.lpNorm_nonneg r x) _))
        (norm_nonneg h))).2
    intro i
    simpa only [kernelHessian_apply, Real.norm_eq_abs] using
      abs_kernelHessianCoord_apply_le hr htheta x h hx i

noncomputable def hessianAmbientConstant (r theta : ℝ) (d : ℕ) : ℝ :=
  hessianCoordConstant r theta d * lpAmbientConstant r d ^ (2 * theta - 2)

lemma hessianAmbientConstant_nonneg {r theta : ℝ}
    (hr : 2 < r) (htheta : 1 < theta) {d : ℕ} :
    0 ≤ hessianAmbientConstant r theta d := by
  unfold hessianAmbientConstant
  exact mul_nonneg (hessianCoordConstant_nonneg hr htheta)
    (Real.rpow_nonneg (lpAmbientConstant_nonneg r d) _)

lemma norm_kernelHessian_le_ambient_rpow {r theta : ℝ}
    (hr : 2 < r) (htheta : 1 < theta) (htr : 2 * theta < r) {d : ℕ}
    (x : Point d) :
    ‖kernelHessian r theta x‖ ≤
      hessianAmbientConstant r theta d * ‖x‖ ^ (2 * theta - 2) := by
  have hlp := lpNorm_le_ambientConstant (d := d) (by linarith : 1 ≤ r) x
  have hrpow := Real.rpow_le_rpow (O3.lpNorm_nonneg r x) hlp
    (by linarith : 0 ≤ 2 * theta - 2)
  have hcoordC : 0 ≤ hessianCoordConstant r theta d :=
    hessianCoordConstant_nonneg hr htheta
  calc
    ‖kernelHessian r theta x‖ ≤
        hessianCoordConstant r theta d * O3.lpNorm r x ^ (2 * theta - 2) :=
      norm_kernelHessian_le_lpNorm_rpow hr htheta htr x
    _ ≤ hessianCoordConstant r theta d *
        (lpAmbientConstant r d * ‖x‖) ^ (2 * theta - 2) := by gcongr
    _ = hessianAmbientConstant r theta d * ‖x‖ ^ (2 * theta - 2) := by
      rw [Real.mul_rpow (lpAmbientConstant_nonneg r d) (norm_nonneg x)]
      unfold hessianAmbientConstant
      ring

/-- The exact narrow-repair gate: the concrete ambient Hessian converges to
zero in continuous-linear-map operator norm at the origin. -/
theorem continuousAt_kernelHessian_zero {r theta : ℝ}
    (hr : 2 < r) (htheta : 1 < theta) (htr : 2 * theta < r) {d : ℕ} :
    ContinuousAt (kernelHessian (d := d) r theta) 0 := by
  rw [ContinuousAt, kernelHessian_zero hr htheta htr]
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero
    (fun x : Point d ↦ norm_nonneg (kernelHessian r theta x))
    (fun x : Point d ↦ norm_kernelHessian_le_ambient_rpow hr htheta htr x)
  have hpow : ContinuousAt
      (fun x : Point d ↦ ‖x‖ ^ (2 * theta - 2)) 0 :=
    continuousAt_id.norm.rpow_const (Or.inr (by linarith : 0 ≤ 2 * theta - 2))
  have hc : ContinuousAt
      (fun _ : Point d ↦ hessianAmbientConstant r theta d) 0 := continuousAt_const
  have hbound : ContinuousAt
      (fun x : Point d ↦ hessianAmbientConstant r theta d *
        ‖x‖ ^ (2 * theta - 2)) 0 := by
    change ContinuousAt
      ((fun _ : Point d ↦ hessianAmbientConstant r theta d) *
        (fun x : Point d ↦ ‖x‖ ^ (2 * theta - 2))) 0
    exact hc.mul hpow
  simpa [Real.zero_rpow (by linarith : 2 * theta - 2 ≠ 0)] using hbound.tendsto

end V7.Stage5AboveTwoLower.S5AHessianContinuity
