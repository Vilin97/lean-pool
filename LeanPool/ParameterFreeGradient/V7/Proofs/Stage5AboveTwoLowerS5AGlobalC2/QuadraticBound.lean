/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/
module


public import LeanPool.ParameterFreeGradient.V7.Proofs.Stage5AboveTwoLowerS5AGlobalC2.Calculus

/-!
The kernel Hessian satisfies the explicit quadratic-form upper bound.
-/

@[expose] public section

open scoped BigOperators

namespace V7.Stage5AboveTwoLower.S5AGlobalC2

open S5ARepair S5AHessianContinuity

private lemma pairing_powerDualityMap (r : ℝ) (x e : Point d) :
    (∑ i, e i * O3.Experimental.scalarJ r (x i)) =
      O3.pairing (O3.powerDualityMap r x) e := by
  apply Finset.sum_congr rfl
  intro i _
  simp only [O3.powerDualityMap, O3.Experimental.scalarJ]
  ring

lemma pairing_kernelHessian_eq {r theta : ℝ} {d : ℕ} (x e : Point d) :
    O3.pairing e (kernelHessian r theta x e) =
      (4 * theta * (2 * theta / r - 1) * r *
          O3.lpPower r x ^ (2 * theta / r - 2) *
          O3.pairing (O3.powerDualityMap r x) e ^ (2 : ℕ)) +
        (4 * theta * (r - 1) * O3.lpPower r x ^ (2 * theta / r - 1) *
          (∑ i, |x i| ^ (r - 2) * e i ^ (2 : ℕ))) := by
  rw [O3.pairing]
  simp only [kernelHessian_apply, kernelHessianCoord, add_apply, smul_apply,
    smul_eq_mul, ContinuousLinearMap.proj_apply, lpPowerFDeriv,
    pairingCLM_apply]
  simp only [mul_add, Finset.sum_add_distrib]
  rw [show
      (∑ i, e i *
        (4 * theta * O3.Experimental.scalarJ r (x i) *
          ((2 * theta / r - 1) * O3.lpPower r x ^ (2 * theta / r - 2) *
            (r * O3.pairing (O3.powerDualityMap r x) e)))) =
        (4 * theta * (2 * theta / r - 1) * r *
          O3.lpPower r x ^ (2 * theta / r - 2) *
          O3.pairing (O3.powerDualityMap r x) e) *
            (∑ i, e i * O3.Experimental.scalarJ r (x i)) by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring]
  rw [pairing_powerDualityMap]
  rw [show
      (∑ i, e i *
        (4 * theta * O3.lpPower r x ^ (2 * theta / r - 1) *
          ((r - 1) * |x i| ^ (r - 2) * e i))) =
        (4 * theta * (r - 1) * O3.lpPower r x ^ (2 * theta / r - 1)) *
          (∑ i, |x i| ^ (r - 2) * e i ^ (2 : ℕ)) by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring]
  ring

lemma kernelHessian_radial_nonpos {r theta : ℝ}
    (_hr : 2 < r) (htheta : 1 < theta) (htr : 2 * theta < r)
    {d : ℕ} (x e : Point d) :
    4 * theta * (2 * theta / r - 1) * r *
        O3.lpPower r x ^ (2 * theta / r - 2) *
        O3.pairing (O3.powerDualityMap r x) e ^ (2 : ℕ) ≤ 0 := by
  have hr0 : 0 < r := by linarith
  have hcoef : 2 * theta / r - 1 < 0 := by
    rw [sub_lt_zero, div_lt_one hr0]
    exact htr
  have hpow : 0 ≤ O3.lpPower r x ^ (2 * theta / r - 2) :=
    Real.rpow_nonneg (O3.lpPower_nonneg r x) _
  have hsquare : 0 ≤ O3.pairing (O3.powerDualityMap r x) e ^ (2 : ℕ) :=
    sq_nonneg _
  rw [show
      4 * theta * (2 * theta / r - 1) * r *
          O3.lpPower r x ^ (2 * theta / r - 2) *
          O3.pairing (O3.powerDualityMap r x) e ^ (2 : ℕ) =
        (2 * theta / r - 1) *
          ((4 * theta * r) * O3.lpPower r x ^ (2 * theta / r - 2) *
            O3.pairing (O3.powerDualityMap r x) e ^ (2 : ℕ)) by ring]
  have hfourtheta : 0 ≤ 4 * theta :=
    mul_nonneg (by norm_num) (by linarith)
  have hbase : 0 ≤ 4 * theta * r := mul_nonneg hfourtheta hr0.le
  exact mul_nonpos_of_nonpos_of_nonneg hcoef.le
    (mul_nonneg (mul_nonneg hbase hpow) hsquare)

lemma weighted_diagonal_bound {r theta : ℝ}
    (hr : 2 < r) {d : ℕ} (x e : Point d) (hx : x ≠ 0) :
    O3.lpPower r x ^ (2 * theta / r - 1) *
        (∑ i, |x i| ^ (r - 2) * e i ^ (2 : ℕ)) ≤
      O3.lpNorm r x ^ (2 * theta - 2) *
        O3.lpNorm r e ^ (2 : ℕ) := by
  have hn : 0 < O3.lpNorm r x := O3.lpNorm_pos_of_ne_zero hx
  have hweighted := O3.Stage2RouteD.weightedHolder_upper hr x e hx
  rw [lpPower_rpow_eq_lpNorm_rpow_of_ne_zero (by linarith : r ≠ 0) x hx]
  have hexp : r * (2 * theta / r - 1) = (2 * theta - 2) + (2 - r) := by
    field_simp [ne_of_gt (by linarith : 0 < r)]
    ring
  rw [hexp, Real.rpow_add hn]
  nlinarith [mul_le_mul_of_nonneg_left hweighted
    (Real.rpow_nonneg hn.le (2 * theta - 2))]

/-- The exact dimension-free Hessian quadratic bound used in the manuscript. -/
theorem kernelHessian_quadratic_bound {r theta : ℝ}
    (hr : 2 < r) (htheta : 1 < theta) (htr : 2 * theta < r)
    {d : ℕ} (x e : Point d) :
    O3.pairing e (kernelHessian r theta x e) ≤
      4 * theta * (r - 1) * O3.lpNorm r x ^ (2 * theta - 2) *
        O3.lpNorm r e ^ (2 : ℕ) := by
  by_cases hx : x = 0
  · subst x
    rw [kernelHessian_zero hr htheta htr]
    simp [O3.pairing, O3.lpNorm_zero (by linarith : 0 < r),
      Real.zero_rpow (by linarith : 2 * theta - 2 ≠ 0)]
  · rw [pairing_kernelHessian_eq]
    have hradial := kernelHessian_radial_nonpos hr htheta htr x e
    have hdiag := weighted_diagonal_bound (theta := theta) hr x e hx
    have hcoef : 0 ≤ 4 * theta * (r - 1) :=
      mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (by linarith)
    nlinarith [mul_le_mul_of_nonneg_left hdiag hcoef]

end V7.Stage5AboveTwoLower.S5AGlobalC2
