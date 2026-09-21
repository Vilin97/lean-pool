/-
Copyright (c) 2026 Yash Kanoria. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yash Kanoria
-/

import LeanPool.FullyDynamicMatching.FD1D.Basic

/-! # Arithmetic -/

namespace FD1D

noncomputable section

/-!
# Numerical estimates

The square-root estimates and explicit constants in the final cost bounds.
-/

theorem sqrt_div_sqrt_six_le_four_div
    {x m : ℝ} (hm : 0 < m) (hx0 : 0 ≤ x)
    (hx : x ≤ 96 / m ^ 2) :
    Real.sqrt x / Real.sqrt 6 ≤ 4 / m := by
  have hsix : 0 < Real.sqrt 6 := Real.sqrt_pos.2 (by norm_num)
  rw [div_le_iff₀ hsix]
  apply (Real.sqrt_le_iff).2
  constructor
  · positivity
  · calc
      x ≤ 96 / m ^ 2 := hx
      _ = (4 / m * Real.sqrt 6) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 6)]
        field_simp
        <;> ring

theorem stationary_sqrt_term_le
    {H m : ℝ} (hm : 0 < m)
    (hH0 : 1 / m ^ 2 ≤ H)
    (hH : H ≤ 206 / (3 * m ^ 2)) :
    Real.sqrt (H - 1 / m ^ 2) / Real.sqrt 6 ≤ 4 / m := by
  apply sqrt_div_sqrt_six_le_four_div hm (sub_nonneg.2 hH0)
  calc
    H - 1 / m ^ 2 ≤ 206 / (3 * m ^ 2) - 1 / m ^ 2 :=
      sub_le_sub_right hH _
    _ ≤ 96 / m ^ 2 := by
      field_simp
      nlinarith

/-- Equation (3) plus the hazard bound implies the advertised stationary cost. -/
theorem stationary_cost_le_six
    {a m H cell cost : ℝ}
    (ha : 0 ≤ a) (hm : 0 < m)
    (hcell : cell ≤ 2 * a / m)
    (hH0 : 1 / m ^ 2 ≤ H)
    (hH : H ≤ 206 / (3 * m ^ 2))
    (hcost :
      cost ≤ cell +
        a / Real.sqrt 6 * Real.sqrt (H - 1 / m ^ 2)) :
    cost ≤ 6 * a / m := by
  have hsqrt := stationary_sqrt_term_le hm hH0 hH
  have hterm :
      a / Real.sqrt 6 * Real.sqrt (H - 1 / m ^ 2) ≤
        a * (4 / m) := by
    calc
      a / Real.sqrt 6 * Real.sqrt (H - 1 / m ^ 2) =
          a * (Real.sqrt (H - 1 / m ^ 2) / Real.sqrt 6) := by ring
      _ ≤ a * (4 / m) := mul_le_mul_of_nonneg_left hsqrt ha
  calc
    cost ≤ cell +
        a / Real.sqrt 6 * Real.sqrt (H - 1 / m ^ 2) := hcost
    _ ≤ 2 * a / m + a * (4 / m) := add_le_add hcell hterm
    _ = 6 * a / m := by ring

theorem inv_horizon_le_inv_sq
    {T m : ℝ} (hm : 0 < m) (hT : m ^ 2 ≤ T) :
    1 / T ≤ 1 / m ^ 2 := by
  have hm2 : 0 < m ^ 2 := sq_pos_of_pos hm
  have hT0 : 0 < T := lt_of_lt_of_le hm2 hT
  exact one_div_le_one_div_of_le hm2 hT

theorem transient_sqrt_term_le
    {H T m : ℝ} (hm : 0 < m) (hT : m ^ 2 ≤ T)
    (hH0 : 1 / m ^ 2 ≤ H)
    (hH : H ≤ 206 / (3 * m ^ 2) + 1 / T) :
    Real.sqrt (H - 1 / m ^ 2) / Real.sqrt 6 ≤ 4 / m := by
  apply sqrt_div_sqrt_six_le_four_div hm (sub_nonneg.2 hH0)
  have hInv := inv_horizon_le_inv_sq hm hT
  calc
    H - 1 / m ^ 2
        ≤ 206 / (3 * m ^ 2) + 1 / T - 1 / m ^ 2 :=
      sub_le_sub_right hH _
    _ ≤ 206 / (3 * m ^ 2) := by linarith
    _ ≤ 96 / m ^ 2 := by
      have hm2 : 0 < m ^ 2 := sq_pos_of_pos hm
      apply (div_le_div_iff₀ (by positivity) hm2).2
      field_simp
      norm_num

theorem transient_cost_le_six
    {a m T H cell cost : ℝ}
    (ha : 0 ≤ a) (hm : 0 < m) (hT : m ^ 2 ≤ T)
    (hcell : cell ≤ 2 * a / m)
    (hH0 : 1 / m ^ 2 ≤ H)
    (hH : H ≤ 206 / (3 * m ^ 2) + 1 / T)
    (hcost :
      cost ≤ cell +
        a / Real.sqrt 6 * Real.sqrt (H - 1 / m ^ 2)) :
    cost ≤ 6 * a / m := by
  have hsqrt := transient_sqrt_term_le hm hT hH0 hH
  have hterm :
      a / Real.sqrt 6 * Real.sqrt (H - 1 / m ^ 2) ≤
        a * (4 / m) := by
    calc
      a / Real.sqrt 6 * Real.sqrt (H - 1 / m ^ 2) =
          a * (Real.sqrt (H - 1 / m ^ 2) / Real.sqrt 6) := by ring
      _ ≤ a * (4 / m) := mul_le_mul_of_nonneg_left hsqrt ha
  calc
    cost ≤ cell +
        a / Real.sqrt 6 * Real.sqrt (H - 1 / m ^ 2) := hcost
    _ ≤ 2 * a / m + a * (4 / m) := add_le_add hcell hterm
    _ = 6 * a / m := by ring

end

end FD1D
