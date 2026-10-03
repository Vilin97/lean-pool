/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesWordFactorials

/-! Exact analytic weights in the linear material commutator recurrence. -/

@[expose] public section

namespace AVenhance.Infra.Section4

/-- The current lower-order factorial and preceding Hessian factorial are
absorbed by two current factorial weights. -/
theorem iterate_linear_material_factorial_le (n j i : ℕ) (hj : j ≤ n) :
    Nat.choose n j * j.factorial * (n - j + 2 * i).factorial *
      (n + 2 * i - 1).factorial ≤ (n + 2 * i).factorial ^ 2 := by
  have h₁ := iterate_choose_factorial_shift_le n j (2 * i) hj
  have h₂ := Nat.factorial_le (by omega : n + 2 * i - 1 ≤ n + 2 * i)
  simpa only [pow_two] using Nat.mul_le_mul h₁ h₂

/-- The remaining radius gain is exactly one geometric factor per velocity
jet. No derivative-order constant is introduced. -/
theorem iterate_linear_material_analytic_term_le (n j i : ℕ) (hj : j ≤ n)
    {b L : ℝ} (hb : 0 ≤ b) (hL : 0 < L) :
    (Nat.choose n j : ℝ) * ((j.factorial : ℝ) * b ^ j) *
      (((n - j + 2 * i).factorial : ℝ) * L ^ (n - j)) *
      (((n + 2 * i - 1).factorial : ℝ) * L ^ (n + 1)) ≤
      (b / L) ^ j * L * (((n + 2 * i).factorial : ℝ) * L ^ n) ^ 2 := by
  have hf : (Nat.choose n j : ℝ) * (j.factorial : ℝ) *
      ((n - j + 2 * i).factorial : ℝ) * ((n + 2 * i - 1).factorial : ℝ) ≤
      ((n + 2 * i).factorial : ℝ) ^ 2 := by
    exact_mod_cast iterate_linear_material_factorial_le n j i hj
  have hp : L ^ n = L ^ j * L ^ (n - j) := by rw [← pow_add, Nat.add_sub_of_le hj]
  have he : (b / L) ^ j * L * (((n + 2 * i).factorial : ℝ) * L ^ n) ^ 2 =
      ((n + 2 * i).factorial : ℝ) ^ 2 * (b ^ j * L ^ (n - j) * L ^ (n + 1)) := by
    simp only [div_pow, pow_succ, hp]
    field_simp
  rw [he]
  convert mul_le_mul_of_nonneg_right hf
    (by positivity : 0 ≤ b ^ j * L ^ (n - j) * L ^ (n + 1)) using 1
  ring

/-- The positive velocity-jet orders give the geometric linear kernel in the
actual norm recurrence. The leading radius factor cancels exactly. -/
theorem iterate_linear_material_series_le (n i : ℕ) {b L : ℝ}
    (hb : 0 ≤ b) (hL : 0 < L) (hg : b / L ≤ 1 / 2)
    (D : ℕ → ℝ) (hD : ∀ r, 0 ≤ D r) :
    (∑ k ∈ Finset.range n,
      (Nat.choose n (k + 1) : ℝ) * (((k + 1).factorial : ℝ) * b ^ (k + 1)) *
        (((n - (k + 1) + 2 * i).factorial : ℝ) * L ^ (n - (k + 1))) *
        (((n + 2 * i - 1).factorial : ℝ) * L ^ (n + 1)) * D (n - (k + 1))) ≤
      b * (((n + 2 * i).factorial : ℝ) * L ^ n) ^ 2 *
        ∑ k ∈ Finset.range n, (1 / (2 : ℝ)) ^ k * D (n - 1 - k) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  have hj : k + 1 ≤ n := by have ht := Finset.mem_range.mp hk; omega
  have ht := mul_le_mul_of_nonneg_right
    (iterate_linear_material_analytic_term_le n (k + 1) i hj hb hL) (hD (n - (k + 1)))
  have he : (b / L) ^ (k + 1) * L *
      (((n + 2 * i).factorial : ℝ) * L ^ n) ^ 2 * D (n - (k + 1)) =
      b * (((n + 2 * i).factorial : ℝ) * L ^ n) ^ 2 *
        (b / L) ^ k * D (n - 1 - k) := by
    have hn : n - (k + 1) = n - 1 - k := by omega
    rw [hn, pow_succ]
    field_simp
  rw [he] at ht
  apply ht.trans
  have hp := pow_le_pow_left₀ (div_nonneg hb hL.le) hg k
  have hm := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ b * (((n + 2 * i).factorial : ℝ) * L ^ n) ^
        2))
    (hD (n - 1 - k))
  simpa only [mul_assoc] using hm

end AVenhance.Infra.Section4
