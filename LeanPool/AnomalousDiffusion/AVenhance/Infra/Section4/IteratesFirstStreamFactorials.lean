/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesLinearFactorials

/-! Absorb the exact first-stream multiplicity into analytic weights. -/

@[expose] public section

namespace AVenhance.Infra.Section4

/-- The n first-jet terms cost no derivative-order constant after the
 preceding factorial energy is compared to the current factorial energy. -/
theorem iterate_first_stream_factorial_le (n i : ℕ) (hn : 1 ≤ n) :
    n * (n - 1 + 2 * i).factorial ^ 2 ≤ (n + 2 * i).factorial ^ 2 := by
  have hm : 1 ≤ n + 2 * i := by omega
  have hf : (n + 2 * i).factorial = (n + 2 * i) * (n - 1 + 2 * i).factorial := by
    have he : n + 2 * i = (n - 1 + 2 * i) + 1 := by omega
    conv_lhs => rw [he, Nat.factorial_succ]
    rw [← he]
  rw [hf, Nat.mul_pow]
  apply Nat.mul_le_mul_right
  have hnm : n ≤ n + 2 * i := by omega
  exact hnm.trans (by nlinarith only [hm])

/-- The first coefficient derivative supplies exactly one squared analytic
 radius gain after summing all n positions. -/
theorem iterate_first_stream_analytic_weight_le (n i : ℕ) (hn : 1 ≤ n)
    {L : ℝ} (hL : 0 < L) :
    (n : ℝ) * (((n - 1 + 2 * i).factorial : ℝ) * L ^ (n - 1)) ^ 2 ≤
      (((n + 2 * i).factorial : ℝ) * L ^ n) ^ 2 / L ^ 2 := by
  have hf : (n : ℝ) * ((n - 1 + 2 * i).factorial : ℝ) ^ 2 ≤
      ((n + 2 * i).factorial : ℝ) ^ 2 := by
    exact_mod_cast iterate_first_stream_factorial_le n i hn
  have hp : L ^ n = L ^ (n - 1) * L := by
    have he : n = n - 1 + 1 := by omega
    conv_lhs => rw [he, pow_succ]
  have he : (((n + 2 * i).factorial : ℝ) * L ^ n) ^ 2 / L ^ 2 =
      ((n + 2 * i).factorial : ℝ) ^ 2 * (L ^ (n - 1)) ^ 2 := by
    rw [hp]
    field_simp
  rw [he, mul_pow]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hf (sq_nonneg (L ^ (n - 1)))

end AVenhance.Infra.Section4
