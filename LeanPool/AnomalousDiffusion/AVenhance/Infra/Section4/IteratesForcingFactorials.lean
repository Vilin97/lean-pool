/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesYoungWeights
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesWordFactorials

/-! Exact shifted factorial profiles for differentiated material forcing. -/

@[expose] public section

namespace AVenhance.Infra.Section4

/-- Squared cancellation at an arbitrary shifted scalar factorial. -/
theorem iterate_weighted_shifted_factorial_term_le (n j a : ℕ) (hj : j ≤ n)
    {b L : ℝ} (hL : 0 < L) :
    (Nat.choose n j : ℝ) ^ 2 * (2 : ℝ) ^ j *
      ((j.factorial : ℝ) * b ^ j) ^ 2 *
      (((n - j + a).factorial : ℝ) * L ^ (n - j)) ^ 2 ≤
      (2 * (b / L) ^ 2) ^ j *
      (((n + a).factorial : ℝ) * L ^ n) ^ 2 := by
  have hnat := iterate_choose_factorial_shift_le n j a hj
  have hf : (Nat.choose n j : ℝ) * (j.factorial : ℝ) *
      ((n - j + a).factorial : ℝ) ≤ ((n + a).factorial : ℝ) := by
    exact_mod_cast hnat
  have hs : ((Nat.choose n j : ℝ) * (j.factorial : ℝ) *
      ((n - j + a).factorial : ℝ)) ^ 2 ≤
      ((n + a).factorial : ℝ) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hf 2
  have hp : L ^ n = L ^ j * L ^ (n - j) := by
    rw [← pow_add, Nat.add_sub_of_le hj]
  have he : (2 * (b / L) ^ 2) ^ j *
      (((n + a).factorial : ℝ) * L ^ n) ^ 2 =
      ((n + a).factorial : ℝ) ^ 2 *
        ((2 : ℝ) ^ j * (b ^ j) ^ 2 * (L ^ (n - j)) ^ 2) := by
    rw [hp, mul_pow, div_pow, ← pow_mul, ← pow_mul]
    have hc : L ^ (j * 2) * L⁻¹ ^ (j * 2) = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ hL.ne', one_pow]
    calc
      _ = ((n + a).factorial : ℝ) ^ 2 * ((2 : ℝ) ^ j *
        b ^ (j * 2) * L ^ ((n - j) * 2)) *
        (L ^ (j * 2) * L⁻¹ ^ (j * 2)) := by simp only [div_eq_mul_inv, mul_pow]; ring
      _ = _ := by rw [hc]; ring
  rw [he]
  convert mul_le_mul_of_nonneg_right hs
    (by positivity : 0 ≤ (2 : ℝ) ^ j * (b ^ j) ^ 2 * (L ^ (n - j)) ^ 2) using 1
  ring

/-- The full shifted factorial sum has a constant bound, including order zero. -/
theorem iterate_forcing_factorial_profile_sum_le (n a : ℕ)
    {b L : ℝ} (hL : 0 < L) (hg : 2 * (b / L) ^ 2 ≤ 1 / 2) :
    (∑ j ∈ Finset.range (n + 1), (Nat.choose n j : ℝ) ^ 2 * (2 : ℝ) ^ j *
      ((j.factorial : ℝ) * b ^ j) ^ 2 *
        (((n - j + a).factorial : ℝ) * L ^ (n - j)) ^ 2) ≤
      2 * (((n + a).factorial : ℝ) * L ^ n) ^ 2 := by
  calc
    _ ≤ ∑ j ∈ Finset.range (n + 1), (2 * (b / L) ^ 2) ^ j *
        (((n + a).factorial : ℝ) * L ^ n) ^ 2 := by
      apply Finset.sum_le_sum
      intro j hj
      exact iterate_weighted_shifted_factorial_term_le n j a
        (by have h := Finset.mem_range.mp hj; omega) hL
    _ = (∑ j ∈ Finset.range (n + 1), (2 * (b / L) ^ 2) ^ j) *
        (((n + a).factorial : ℝ) * L ^ n) ^ 2 := by rw [Finset.sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (iterate_geometric_kernel_le_two (by positivity) hg (n + 1)) (sq_nonneg _)

end AVenhance.Infra.Section4
