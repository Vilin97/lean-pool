/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.FineMaterialRates

/-! Summation of the actual first-material velocity recursion. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4

/-- Minimal separation controls every negative-power scalar amplitude sum.
The constant does not depend on the number of scales or on Λ. -/
theorem amnr_negative_power_sum {β p : ℝ} (I : AVenhance.Ingredients β)
    (hp : p ≤ -(1 / 7 : ℝ)) (m : ℕ) :
    (∑ j ∈ Finset.range (m + 1), AVenhance.epsilon β I.Λ j ^ p) ≤
      2 * AVenhance.epsilon β I.Λ m ^ p := by
  have hL128 : (2 : ℝ) ^ 7 ≤ (I.Λ : ℝ) := by exact_mod_cast I.two_pow_seven_le
  have hr : (I.Λ : ℝ) ^ p ≤ 1 / 2 := by
    calc
      _ ≤ ((2 : ℝ) ^ 7) ^ p :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) hL128 (by linarith)
      _ = (2 : ℝ) ^ (7 * p) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num
      _ ≤ (2 : ℝ) ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = _ := by rw [Real.rpow_neg_one]; norm_num
  have hstep (j : ℕ) : AVenhance.epsilon β I.Λ j ^ p ≤
      (1 / 2 : ℝ) * AVenhance.epsilon β I.Λ (j + 1) ^ p := by
    have he := AVenhance.Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
      (m := j + 1)
    have hLp : 0 < (I.Λ : ℝ) := by positivity
    have hs := AVenhance.Infra.Ingredients.epsilon_minsep I.one_lt_beta I.beta_lt
      I.two_pow_seven_le (m := j)
    have hh := Real.rpow_le_rpow_of_nonpos (mul_pos hLp he) hs
      (show p ≤ 0 by linarith)
    rw [Real.mul_rpow hLp.le he.le] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right hr (Real.rpow_nonneg he.le _))
  have hs := AVenhance.Infra.Construction.sum_le_last_mul_geometric
    (fun j => AVenhance.epsilon β I.Λ j ^ p) (by norm_num : 0 ≤ (1 / 2 : ℝ)) hstep m
  have hg := AVenhance.Infra.Construction.sum_geometric_le
    (by norm_num : 0 ≤ (1 / 2 : ℝ)) (by norm_num : (1 / 2 : ℝ) < 1) (m + 1)
  norm_num at hg
  exact (hs.trans (mul_le_mul_of_nonneg_left hg
    (Real.rpow_nonneg (AVenhance.Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt
      I.two_pow_seven_le (m := m)).le _))).trans_eq (by ring)

/-- Absolute summation of an actual scalar recursion, retaining its base term. -/
theorem amnr_abs_recursion_sum (v u : ℕ → ℝ) {K : ℝ} (hK : 0 ≤ K)
    (hu : ∀ j, 0 ≤ u j) (hzero : v 0 = 0)
    (hstep : ∀ j, |v (j + 1) - v j| ≤ K * u (j + 1)) (m : ℕ) :
    |v m| ≤ K * ∑ j ∈ Finset.range (m + 1), u j := by
  induction m with
  | zero => simpa [hzero] using mul_nonneg hK (hu 0)
  | succ m ih =>
    calc
      |v (m + 1)| = |v (m + 1) - v m + v m| := by congr 1; ring
      _ ≤ |v (m + 1) - v m| + |v m| := abs_add_le _ _
      _ ≤ K * u (m + 1) + K * ∑ j ∈ Finset.range (m + 1), u j := add_le_add (hstep m) ih
      _ = K * ∑ j ∈ Finset.range (m + 1 + 1), u j := by
        rw [Finset.sum_range_succ (f := u) (n := m + 1)]
        ring

end AVenhance.Infra.Section4
