/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/

import LeanPool.ParameterFreeGradient.V7.Proofs.Stage2.GuardSoundness

/-!
Positivity and geometric-sum estimates for the local complexity exponent.
-/

namespace V7
namespace Stage2

open scoped BigOperators

private theorem finite_geometric_sum_le {c ratio : ℝ}
    (hc : 0 ≤ c) (hratio : 1 < ratio) (N : ℕ) :
    ∑ n ∈ Finset.range N, c * ratio ^ n ≤
      c * ratio ^ N / (ratio - 1) := by
  rw [← Finset.mul_sum, geom_sum_eq hratio.ne']
  have hden : 0 < ratio - 1 := sub_pos.mpr hratio
  have hpow : 0 ≤ ratio ^ N := pow_nonneg (by linarith) _
  calc
    c * ((ratio ^ N - 1) / (ratio - 1)) =
        c * (ratio ^ N - 1) / (ratio - 1) := by ring
    _ ≤ c * ratio ^ N / (ratio - 1) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (by linarith) hc) hden.le

theorem two_rpow_gt_one {a : ℝ} (ha : 0 < a) :
    1 < (2 : ℝ) ^ a :=
  Real.one_lt_rpow (by norm_num) ha

theorem one_sub_two_neg_rpow_pos {a : ℝ} (ha : 0 < a) :
    0 < 1 - (2 : ℝ) ^ (-a) := by
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  have h := two_rpow_gt_one ha
  exact sub_pos.mpr (inv_lt_one_of_one_lt₀ h)

theorem localCostExponent_pos {p : ℝ} :
    0 < localCostExponent p := by
  unfold localCostExponent
  split_ifs with h
  · norm_num
  · have hp2 : 2 < p := lt_of_not_ge h
    exact div_pos (by linarith) (by linarith)

private theorem geometric_coefficient_eq {a : ℝ} :
    (2 : ℝ) ^ a / ((2 : ℝ) ^ a - 1) =
      1 / (1 - (2 : ℝ) ^ (-a)) := by
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  have hr : (2 : ℝ) ^ a ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) _).ne'
  field_simp

/-- A dependency-pure finite dyadic sum.  The right hand side is the exact
coefficient frozen into the V7 controller carriers. -/
theorem dyadic_geometric_sum_le_endpoint {a beta : ℝ}
    (ha : 0 < a) (hbeta : 0 ≤ beta) (J : ℕ) :
    ∑ j ∈ Finset.range (J + 1), ((2 : ℝ) ^ j * beta) ^ a ≤
      (((2 : ℝ) ^ J * beta) ^ a) / (1 - (2 : ℝ) ^ (-a)) := by
  by_cases hb : beta = 0
  · subst beta
    simp [Real.zero_rpow ha.ne']
  have hbetaPos : 0 < beta := lt_of_le_of_ne hbeta (Ne.symm hb)
  have hratio : 1 < (2 : ℝ) ^ a := two_rpow_gt_one ha
  have hbetaPow : 0 ≤ beta ^ a := Real.rpow_nonneg hbeta _
  have hrewrite :
      ∑ j ∈ Finset.range (J + 1), ((2 : ℝ) ^ j * beta) ^ a =
        ∑ j ∈ Finset.range (J + 1), beta ^ a * ((2 : ℝ) ^ a) ^ j := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [Real.mul_rpow (pow_nonneg (by norm_num) _) hbeta]
    rw [Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 2) a j]
    ring
  rw [hrewrite]
  have hgeom := finite_geometric_sum_le hbetaPow hratio (J + 1)
  have hend : (((2 : ℝ) ^ J * beta) ^ a) =
      beta ^ a * ((2 : ℝ) ^ a) ^ J := by
    rw [Real.mul_rpow (pow_nonneg (by norm_num) _) hbeta]
    rw [Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 2) a J]
    ring
  rw [hend]
  calc
    ∑ j ∈ Finset.range (J + 1), beta ^ a * ((2 : ℝ) ^ a) ^ j
        ≤ beta ^ a * ((2 : ℝ) ^ a) ^ (J + 1) /
            ((2 : ℝ) ^ a - 1) := hgeom
    _ = (2 : ℝ) ^ a / ((2 : ℝ) ^ a - 1) *
          (beta ^ a * ((2 : ℝ) ^ a) ^ J) := by rw [pow_succ]; ring
    _ = (beta ^ a * ((2 : ℝ) ^ a) ^ J) /
          (1 - (2 : ℝ) ^ (-a)) := by
      rw [geometric_coefficient_eq]
      ring

end Stage2
end V7
